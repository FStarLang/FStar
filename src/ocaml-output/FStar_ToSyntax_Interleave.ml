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
             (fun uu___159_133  ->
                match uu___159_133 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____143,uu____144,uu____145),uu____146) ->
                    let uu____159 = FStar_Ident.lid_of_ids [id1] in
                    [uu____159]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____161,uu____162,uu____163),uu____164) ->
                    let uu____197 = FStar_Ident.lid_of_ids [id1] in
                    [uu____197]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____199,uu____200,uu____201),uu____202) ->
                    let uu____243 = FStar_Ident.lid_of_ids [id1] in
                    [uu____243]
                | uu____244 -> []))
    | uu____251 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____258 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____258
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
           | FStar_Parser_AST.Tycon (uu____303,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___160_338  ->
                       match uu___160_338 with
                       | (FStar_Parser_AST.TyconAbstract uu____345,uu____346)
                           -> true
                       | uu____361 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 impl.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let def_ids = definition_lids impl in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 let uu____390 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____390
                  then
                    let uu____405 =
                      let uu____410 =
                        let uu____411 =
                          let uu____412 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid) in
                          FStar_All.pipe_right uu____412
                            (FStar_String.concat ", ") in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____411 in
                      (FStar_Errors.WrongDefinitionOrder, uu____410) in
                    FStar_Errors.raise_error uu____405
                      impl.FStar_Parser_AST.drange
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____479) -> ([], iface2)
                    | (uu____490::uu____491,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____522 = aux ys iface_tl1 in
                          (match uu____522 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____554 =
                             let uu____555 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____555 in
                           if uu____554
                           then
                             let uu____568 =
                               let uu____573 =
                                 let uu____574 =
                                   FStar_Parser_AST.decl_to_string iface_hd1 in
                                 let uu____575 = FStar_Ident.string_of_lid y in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____574 uu____575 in
                               (FStar_Errors.WrongDefinitionOrder, uu____573) in
                             FStar_Errors.raise_error uu____568
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2) in
                  let uu____585 = aux mutually_defined_with_x iface_tl in
                  match uu____585 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____616 ->
               let uu____617 = prefix_with_iface_decls iface_tl impl in
               (match uu____617 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____669,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___161_704  ->
                       match uu___161_704 with
                       | (FStar_Parser_AST.TyconAbstract uu____711,uu____712)
                           -> true
                       | uu____727 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____736 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____736
               then
                 let uu____737 =
                   let uu____742 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText in
                   (FStar_Errors.BothValAndLetInInterface, uu____742) in
                 FStar_Errors.raise_error uu____737
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____744 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____744
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____746 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____755 -> false
            | uu____756 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____783,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____800 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____800 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____837 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____858 -> true
            | uu____863 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____890 -> (iface1, [impl])
      | uu____895 ->
          let uu____896 = FStar_Options.ml_ish () in
          if uu____896
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
          let uu____928 = FStar_Options.ml_ish () in
          if uu____928
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____932 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____932 with
        | FStar_Pervasives_Native.Some uu____941 ->
            let uu____946 =
              let uu____951 =
                let uu____952 = FStar_Ident.string_of_lid mname in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____952 in
              (FStar_Errors.InterfaceAlreadyProcessed, uu____951) in
            FStar_Errors.raise_error uu____946
              (FStar_Ident.range_of_lid mname)
        | FStar_Pervasives_Native.None  ->
            let uu____959 =
              FStar_ToSyntax_Env.set_iface_decls env mname decls in
            ((), uu____959)
let prefix_with_interface_decls:
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_ToSyntax_Env.withenv
  =
  fun impl  ->
    fun env  ->
      let uu____976 =
        let uu____981 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____981 in
      match uu____976 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____997 = prefix_one_decl iface1 impl in
          (match uu____997 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1023 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____1023 iface2 in
               (impl1, env1))
let interleave_module:
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_ToSyntax_Env.withenv
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1045 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1060 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____1060 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1076 =
                   FStar_List.fold_left
                     (fun uu____1100  ->
                        fun impl  ->
                          match uu____1100 with
                          | (iface2,impls1) ->
                              let uu____1128 = prefix_one_decl iface2 impl in
                              (match uu____1128 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____1076 with
                  | (iface2,impls1) ->
                      let uu____1177 =
                        let uu____1186 =
                          FStar_Util.prefix_until
                            (fun uu___162_1205  ->
                               match uu___162_1205 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1206;
                                   FStar_Parser_AST.drange = uu____1207;
                                   FStar_Parser_AST.doc = uu____1208;
                                   FStar_Parser_AST.quals = uu____1209;
                                   FStar_Parser_AST.attrs = uu____1210;_} ->
                                   true
                               | uu____1217 -> false) iface2 in
                        match uu____1186 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest)) in
                      (match uu____1177 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets in
                           let env1 =
                             FStar_ToSyntax_Env.set_iface_decls env l
                               remaining_iface_vals in
                           let a1 = FStar_Parser_AST.Module (l, impls2) in
                           (match remaining_iface_vals with
                            | uu____1290::uu____1291 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1295 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals in
                                  FStar_All.pipe_right uu____1295
                                    (FStar_String.concat "\n\t") in
                                let uu____1300 =
                                  let uu____1305 =
                                    let uu____1306 =
                                      FStar_Ident.string_of_lid l in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1306 err in
                                  (FStar_Errors.InterfaceNotImplementedByModule,
                                    uu____1305) in
                                FStar_Errors.raise_error uu____1300
                                  (FStar_Ident.range_of_lid l)
                            | uu____1311 -> (a1, env1)))))