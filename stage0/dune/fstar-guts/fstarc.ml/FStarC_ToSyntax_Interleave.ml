open Prims
let id_eq_lid (i : FStarC_Ident.ident) (l : FStarC_Ident.lident) :
  Prims.bool=
  (FStarC_Ident.string_of_id i) =
    (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid l))
let is_val (x : FStarC_Ident.ident) (d : FStarC_Parser_AST.decl) :
  Prims.bool=
  match d.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.Val (y, uu___) ->
      (FStarC_Ident.string_of_id x) = (FStarC_Ident.string_of_id y)
  | FStarC_Parser_AST.DeclToBeDesugared
      { FStarC_Parser_AST.lang_name = uu___; FStarC_Parser_AST.blob = uu___1;
        FStarC_Parser_AST.idents = y::[];
        FStarC_Parser_AST.to_string = uu___2; FStarC_Parser_AST.eq = uu___3;
        FStarC_Parser_AST.dep_scan = uu___4;_}
      -> (FStarC_Ident.string_of_id x) = (FStarC_Ident.string_of_id y)
  | uu___ -> false
let is_type (x : FStarC_Ident.ident) (d : FStarC_Parser_AST.decl) :
  Prims.bool=
  match d.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) ->
      FStarC_Util.for_some
        (fun t ->
           (FStarC_Parser_AST.id_of_tycon t) = (FStarC_Ident.string_of_id x))
        tys
  | uu___ -> false
let definition_lids (d : FStarC_Parser_AST.decl) :
  FStarC_Ident.lident Prims.list=
  match d.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.TopLevelLet (uu___, defs) ->
      FStarC_Parser_AST.lids_of_let defs
  | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) ->
      FStarC_List.collect
        (fun uu___2 ->
           match uu___2 with
           | FStarC_Parser_AST.TyconAbbrev (id, uu___3, uu___4, uu___5) ->
               let uu___6 = FStarC_Ident.lid_of_ids [id] in [uu___6]
           | FStarC_Parser_AST.TyconRecord
               (id, uu___3, uu___4, uu___5, uu___6) ->
               let uu___7 = FStarC_Ident.lid_of_ids [id] in [uu___7]
           | FStarC_Parser_AST.TyconVariant (id, uu___3, uu___4, uu___5) ->
               let uu___6 = FStarC_Ident.lid_of_ids [id] in [uu___6]
           | uu___3 -> []) tys
  | FStarC_Parser_AST.Splice (uu___, ids, uu___1) ->
      FStarC_List.map (fun id -> FStarC_Ident.lid_of_ids [id]) ids
  | FStarC_Parser_AST.DeclToBeDesugared
      { FStarC_Parser_AST.lang_name = uu___; FStarC_Parser_AST.blob = uu___1;
        FStarC_Parser_AST.idents = ids; FStarC_Parser_AST.to_string = uu___2;
        FStarC_Parser_AST.eq = uu___3; FStarC_Parser_AST.dep_scan = uu___4;_}
      -> FStarC_List.map (fun id -> FStarC_Ident.lid_of_ids [id]) ids
  | FStarC_Parser_AST.DeclSyntaxExtension
      (extension_name, code, uu___, range) ->
      let ext_parser =
        FStarC_Parser_AST_Util.lookup_extension_parser extension_name in
      (match ext_parser with
       | FStar_Pervasives_Native.None ->
           FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl d
             FStarC_Errors_Codes.Fatal_SyntaxError ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic
                (FStarC_Format.fmt1 "Unknown syntax extension %s"
                   extension_name))
       | FStar_Pervasives_Native.Some parser ->
           (match parser.FStarC_Parser_AST_Util.parse_decl_name code range
            with
            | FStar_Pervasives.Inl error ->
                FStarC_Errors.raise_error
                  FStarC_Class_HasRange.hasRange_range
                  error.FStarC_Parser_AST_Util.range
                  FStarC_Errors_Codes.Fatal_SyntaxError ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic error.FStarC_Parser_AST_Util.message)
            | FStar_Pervasives.Inr id ->
                let uu___1 = FStarC_Ident.lid_of_ids [id] in [uu___1]))
  | uu___ -> []
let is_definition_of (x : FStarC_Ident.ident) (d : FStarC_Parser_AST.decl) :
  Prims.bool=
  let uu___ = definition_lids d in FStarC_Util.for_some (id_eq_lid x) uu___
let rec prefix_with_iface_decls (iface : FStarC_Parser_AST.decl Prims.list)
  (impl : FStarC_Parser_AST.decl) :
  (FStarC_Parser_AST.decl Prims.list * FStarC_Parser_AST.decl Prims.list)=
  let qualify_karamel_private impl1 =
    let karamel_private =
      FStarC_Parser_AST.mk_term
        (FStarC_Parser_AST.Const
           (FStarC_Const.Const_string
              ("KrmlPrivate", (impl1.FStarC_Parser_AST.drange))))
        impl1.FStarC_Parser_AST.drange FStarC_Parser_AST.Expr in
    {
      FStarC_Parser_AST.d = (impl1.FStarC_Parser_AST.d);
      FStarC_Parser_AST.drange = (impl1.FStarC_Parser_AST.drange);
      FStarC_Parser_AST.quals = (impl1.FStarC_Parser_AST.quals);
      FStarC_Parser_AST.attrs = (karamel_private ::
        (impl1.FStarC_Parser_AST.attrs));
      FStarC_Parser_AST.interleaved = (impl1.FStarC_Parser_AST.interleaved)
    } in
  if FStarC_Parser_AST.uu___is_Friend impl.FStarC_Parser_AST.d
  then (iface, [impl])
  else
    (match iface with
     | [] -> ([], [qualify_karamel_private impl])
     | iface_hd::iface_tl ->
         (match iface_hd.FStarC_Parser_AST.d with
          | FStarC_Parser_AST.Tycon (uu___1, uu___2, tys) when
              FStarC_Util.for_some
                (fun uu___3 ->
                   match uu___3 with
                   | FStarC_Parser_AST.TyconAbstract uu___4 -> true
                   | uu___4 -> false) tys
              ->
              FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl impl
                FStarC_Errors_Codes.Fatal_AbstractTypeDeclarationInInterface
                () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic
                   [FStarC_Errors_Msg.text
                      "Interface contains an abstract 'type' declaration; use 'val' instead."])
          | FStarC_Parser_AST.Splice (uu___1, x::[], uu___2) ->
              let def_ids = definition_lids impl in
              let defines_x = FStarC_Util.for_some (id_eq_lid x) def_ids in
              if Prims.op_Negation defines_x
              then
                ((let uu___4 =
                    FStarC_Util.for_some
                      (fun y ->
                         FStarC_Util.for_some
                           (is_val (FStarC_Ident.ident_of_lid y)) iface_tl)
                      def_ids in
                  if uu___4
                  then
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStarC_Class_PP.pp FStarC_Ident.pretty_ident x in
                          let uu___9 =
                            let uu___10 =
                              FStarC_Class_PP.pp
                                (FStarC_Class_PP.pp_list
                                   FStarC_Ident.pretty_lident) def_ids in
                            FStar_Pprint.op_Hat_Slash_Hat
                              (FStarC_Errors_Msg.text "to precede") uu___10 in
                          FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                        FStar_Pprint.op_Hat_Slash_Hat
                          (FStarC_Errors_Msg.text
                             "Expected the definition of") uu___7 in
                      [uu___6] in
                    FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl
                      impl FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___5)
                  else ());
                 (iface, [qualify_karamel_private impl]))
              else
                (let mutually_defined_with_x =
                   FStarC_List.filter
                     (fun y -> Prims.op_Negation (id_eq_lid x y)) def_ids in
                 let rec aux mutuals iface1 =
                   match (mutuals, iface1) with
                   | ([], uu___4) -> ([], iface1)
                   | (uu___4::uu___5, []) -> ([], [])
                   | (y::ys, iface_hd1::iface_tl1) when
                       is_val (FStarC_Ident.ident_of_lid y) iface_hd1 ->
                       let uu___4 = aux ys iface_tl1 in
                       (match uu___4 with
                        | (val_ys, iface2) -> ((iface_hd1 :: val_ys), iface2))
                   | (y::ys, iface_hd1::iface_tl1) when
                       let uu___4 =
                         FStarC_List.tryFind
                           (is_val (FStarC_Ident.ident_of_lid y)) iface_tl1 in
                       FStar_Pervasives_Native.uu___is_Some uu___4 ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStarC_Class_Show.show
                                 FStarC_Parser_AST.showable_decl iface_hd1 in
                             FStarC_Format.fmt2
                               "%s is out of order with the definition of %s"
                               uu___7 (FStarC_Ident.string_of_lid y) in
                           FStarC_Errors_Msg.text uu___6 in
                         [uu___5] in
                       FStarC_Errors.raise_error
                         FStarC_Parser_AST.hasRange_decl iface_hd1
                         FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                         (Obj.magic
                            FStarC_Errors_Msg.is_error_message_list_doc)
                         (Obj.magic uu___4)
                   | (y::ys, iface_hd1::iface_tl1) -> aux ys iface1 in
                 let uu___4 = aux mutually_defined_with_x iface_tl in
                 match uu___4 with
                 | (take_iface, rest_iface) ->
                     (rest_iface,
                       (FStarC_List.op_At (iface_hd :: take_iface) [impl])))
          | FStarC_Parser_AST.Val (x, uu___1) ->
              let def_ids = definition_lids impl in
              let defines_x = FStarC_Util.for_some (id_eq_lid x) def_ids in
              if Prims.op_Negation defines_x
              then
                ((let uu___3 =
                    FStarC_Util.for_some
                      (fun y ->
                         FStarC_Util.for_some
                           (is_val (FStarC_Ident.ident_of_lid y)) iface_tl)
                      def_ids in
                  if uu___3
                  then
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStarC_Class_PP.pp FStarC_Ident.pretty_ident x in
                          let uu___8 =
                            let uu___9 =
                              FStarC_Class_PP.pp
                                (FStarC_Class_PP.pp_list
                                   FStarC_Ident.pretty_lident) def_ids in
                            FStar_Pprint.op_Hat_Slash_Hat
                              (FStarC_Errors_Msg.text "to precede") uu___9 in
                          FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                        FStar_Pprint.op_Hat_Slash_Hat
                          (FStarC_Errors_Msg.text
                             "Expected the definition of") uu___6 in
                      [uu___5] in
                    FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl
                      impl FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___4)
                  else ());
                 (iface, [qualify_karamel_private impl]))
              else
                (let mutually_defined_with_x =
                   FStarC_List.filter
                     (fun y -> Prims.op_Negation (id_eq_lid x y)) def_ids in
                 let rec aux mutuals iface1 =
                   match (mutuals, iface1) with
                   | ([], uu___3) -> ([], iface1)
                   | (uu___3::uu___4, []) -> ([], [])
                   | (y::ys, iface_hd1::iface_tl1) when
                       is_val (FStarC_Ident.ident_of_lid y) iface_hd1 ->
                       let uu___3 = aux ys iface_tl1 in
                       (match uu___3 with
                        | (val_ys, iface2) -> ((iface_hd1 :: val_ys), iface2))
                   | (y::ys, iface_hd1::iface_tl1) when
                       let uu___3 =
                         FStarC_List.tryFind
                           (is_val (FStarC_Ident.ident_of_lid y)) iface_tl1 in
                       FStar_Pervasives_Native.uu___is_Some uu___3 ->
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStarC_Class_Show.show
                                 FStarC_Parser_AST.showable_decl iface_hd1 in
                             FStarC_Format.fmt2
                               "%s is out of order with the definition of %s"
                               uu___6 (FStarC_Ident.string_of_lid y) in
                           FStarC_Errors_Msg.text uu___5 in
                         [uu___4] in
                       FStarC_Errors.raise_error
                         FStarC_Parser_AST.hasRange_decl iface_hd1
                         FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                         (Obj.magic
                            FStarC_Errors_Msg.is_error_message_list_doc)
                         (Obj.magic uu___3)
                   | (y::ys, iface_hd1::iface_tl1) -> aux ys iface1 in
                 let uu___3 = aux mutually_defined_with_x iface_tl in
                 match uu___3 with
                 | (take_iface, rest_iface) ->
                     (rest_iface,
                       (FStarC_List.op_At (iface_hd :: take_iface) [impl])))
          | FStarC_Parser_AST.DeclToBeDesugared
              { FStarC_Parser_AST.lang_name = uu___1;
                FStarC_Parser_AST.blob = uu___2;
                FStarC_Parser_AST.idents = x::[];
                FStarC_Parser_AST.to_string = uu___3;
                FStarC_Parser_AST.eq = uu___4;
                FStarC_Parser_AST.dep_scan = uu___5;_}
              ->
              let def_ids = definition_lids impl in
              let defines_x = FStarC_Util.for_some (id_eq_lid x) def_ids in
              if defines_x
              then
                (match impl.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.DeclToBeDesugared uu___6 ->
                     (iface_tl, [impl])
                 | uu___6 -> (iface_tl, [iface_hd; impl]))
              else (iface, [qualify_karamel_private impl])
          | FStarC_Parser_AST.Pragma uu___1 ->
              prefix_with_iface_decls iface_tl impl
          | FStarC_Parser_AST.Exception (id, uu___1) ->
              (match impl.FStarC_Parser_AST.d with
               | FStarC_Parser_AST.Exception (id', uu___2) when
                   (FStarC_Ident.string_of_id id) =
                     (FStarC_Ident.string_of_id id')
                   -> (iface_tl, [impl])
               | uu___2 ->
                   let uu___3 = prefix_with_iface_decls iface_tl impl in
                   (match uu___3 with
                    | (iface1, ds) -> (iface1, (iface_hd :: ds))))
          | FStarC_Parser_AST.TopLevelLet (uu___1, defs) when
              iface_hd.FStarC_Parser_AST.attrs = [] ->
              let iface_lids = FStarC_Parser_AST.lids_of_let defs in
              let impl_lids = definition_lids impl in
              let uu___2 =
                FStarC_Util.for_some
                  (fun l ->
                     FStarC_Util.for_some
                       (fun l' -> id_eq_lid (FStarC_Ident.ident_of_lid l) l')
                       impl_lids) iface_lids in
              if uu___2
              then (iface_tl, [impl])
              else
                (let uu___4 = prefix_with_iface_decls iface_tl impl in
                 match uu___4 with
                 | (iface1, ds) -> (iface1, (iface_hd :: ds)))
          | uu___1 ->
              let uu___2 = prefix_with_iface_decls iface_tl impl in
              (match uu___2 with | (iface1, ds) -> (iface1, (iface_hd :: ds)))))
let check_initial_interface (iface : FStarC_Parser_AST.decl Prims.list) :
  FStarC_Parser_AST.decl Prims.list=
  let rec aux iface1 =
    match iface1 with
    | [] -> ()
    | hd::tl ->
        (match hd.FStarC_Parser_AST.d with
         | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) when
             FStarC_Util.for_some
               (fun uu___2 ->
                  match uu___2 with
                  | FStarC_Parser_AST.TyconAbstract uu___3 -> true
                  | uu___3 -> false) tys
             ->
             FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl hd
               FStarC_Errors_Codes.Fatal_AbstractTypeDeclarationInInterface
               () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic
                  "Interface contains an abstract 'type' declaration; use 'val' instead")
         | FStarC_Parser_AST.Val (x, t) ->
             let uu___ = FStarC_Util.for_some (is_definition_of x) tl in
             if uu___
             then
               FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl hd
                 FStarC_Errors_Codes.Fatal_BothValAndLetInInterface ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic
                    (FStarC_Format.fmt2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       (FStarC_Ident.string_of_id x)
                       (FStarC_Ident.string_of_id x)))
             else
               if
                 FStarC_List.contains FStarC_Parser_AST.Assumption
                   hd.FStarC_Parser_AST.quals
               then
                 FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl hd
                   FStarC_Errors_Codes.Fatal_AssumeValInInterface ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic
                      "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
               else ()
         | uu___ -> ()) in
  aux iface;
  FStarC_List.filter
    (fun d ->
       match d.FStarC_Parser_AST.d with
       | FStarC_Parser_AST.TopLevelModule uu___1 -> false
       | uu___1 -> true) iface
let prefix_one_decl (iface : FStarC_Parser_AST.decl Prims.list)
  (impl : FStarC_Parser_AST.decl) :
  (FStarC_Parser_AST.decl Prims.list * FStarC_Parser_AST.decl Prims.list)=
  match impl.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.TopLevelModule uu___ -> (iface, [impl])
  | uu___ -> prefix_with_iface_decls iface impl
let initialize_interface (mname : FStarC_Ident.lid)
  (l : FStarC_Parser_AST.decl Prims.list) : unit FStarC_Syntax_DsEnv.withenv=
  fun env ->
    let decls = check_initial_interface l in
    let uu___ = FStarC_Syntax_DsEnv.iface_decls env mname in
    match uu___ with
    | FStar_Pervasives_Native.Some uu___1 ->
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Ident.showable_lident mname in
          FStarC_Format.fmt1 "Interface %s has already been processed" uu___3 in
        FStarC_Errors.raise_error FStarC_Ident.hasrange_lident mname
          FStarC_Errors_Codes.Fatal_InterfaceAlreadyProcessed ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic uu___2)
    | FStar_Pervasives_Native.None ->
        let uu___1 = FStarC_Syntax_DsEnv.set_iface_decls env mname decls in
        ((), uu___1)
let fixup_interleaved_decls (iface : FStarC_Parser_AST.decl Prims.list) :
  FStarC_Parser_AST.decl Prims.list=
  let fix1 d =
    let d1 =
      {
        FStarC_Parser_AST.d = (d.FStarC_Parser_AST.d);
        FStarC_Parser_AST.drange = (d.FStarC_Parser_AST.drange);
        FStarC_Parser_AST.quals = (d.FStarC_Parser_AST.quals);
        FStarC_Parser_AST.attrs = (d.FStarC_Parser_AST.attrs);
        FStarC_Parser_AST.interleaved = true
      } in
    d1 in
  FStarC_List.map fix1 iface
let prefix_with_interface_decls (impl : FStarC_Parser_AST.decl) :
  FStarC_Parser_AST.decl Prims.list FStarC_Syntax_DsEnv.withenv=
  fun env ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Syntax_DsEnv.current_module env in
        FStarC_Syntax_DsEnv.iface_decls env uu___2 in
      match uu___1 with
      | FStar_Pervasives_Native.None -> ([impl], env)
      | FStar_Pervasives_Native.Some iface ->
          let iface1 = fixup_interleaved_decls iface in
          let uu___2 = prefix_one_decl iface1 impl in
          (match uu___2 with
           | (iface2, impl1) ->
               let env1 =
                 let uu___3 = FStarC_Syntax_DsEnv.current_module env in
                 FStarC_Syntax_DsEnv.set_iface_decls env uu___3 iface2 in
               (impl1, env1)) in
    match uu___ with
    | (decls, env1) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Syntax_DsEnv.current_module env1 in
              FStarC_Ident.string_of_lid uu___4 in
            FStarC_Options.dump_module uu___3 in
          if uu___2
          then
            let uu___3 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_list FStarC_Parser_AST.showable_decl)
                decls in
            FStarC_Format.print1 "Interleaved decls:\n%s\n" uu___3
          else ());
         (decls, env1))
let interleave_module (a : FStarC_Parser_AST.modul)
  (expect_complete_modul : Prims.bool) :
  FStarC_Parser_AST.modul FStarC_Syntax_DsEnv.withenv=
  fun env ->
    match a with
    | FStarC_Parser_AST.Interface uu___ -> (a, env)
    | FStarC_Parser_AST.Module
        { FStarC_Parser_AST.no_prelude = no_prelude;
          FStarC_Parser_AST.mname = l; FStarC_Parser_AST.decls = impls;_}
        ->
        let uu___ = FStarC_Syntax_DsEnv.iface_decls env l in
        (match uu___ with
         | FStar_Pervasives_Native.None -> (a, env)
         | FStar_Pervasives_Native.Some iface ->
             let iface1 = fixup_interleaved_decls iface in
             let uu___1 =
               FStarC_List.fold_left
                 (fun uu___2 impl ->
                    match uu___2 with
                    | (iface2, impls1) ->
                        let uu___3 = prefix_one_decl iface2 impl in
                        (match uu___3 with
                         | (iface3, impls') ->
                             (iface3, (FStarC_List.op_At impls1 impls'))))
                 (iface1, []) impls in
             (match uu___1 with
              | (iface2, impls1) ->
                  let uu___2 =
                    let uu___3 =
                      FStarC_Util.prefix_until
                        (fun uu___4 ->
                           match uu___4 with
                           | {
                               FStarC_Parser_AST.d = FStarC_Parser_AST.Val
                                 uu___5;
                               FStarC_Parser_AST.drange = uu___6;
                               FStarC_Parser_AST.quals = uu___7;
                               FStarC_Parser_AST.attrs = uu___8;
                               FStarC_Parser_AST.interleaved = uu___9;_} ->
                               true
                           | {
                               FStarC_Parser_AST.d = FStarC_Parser_AST.Splice
                                 uu___5;
                               FStarC_Parser_AST.drange = uu___6;
                               FStarC_Parser_AST.quals = uu___7;
                               FStarC_Parser_AST.attrs = uu___8;
                               FStarC_Parser_AST.interleaved = uu___9;_} ->
                               true
                           | uu___5 -> false) iface2 in
                    match uu___3 with
                    | FStar_Pervasives_Native.None -> (iface2, [])
                    | FStar_Pervasives_Native.Some (lets, one_val, rest) ->
                        (lets, (one_val :: rest)) in
                  (match uu___2 with
                   | (iface_lets, remaining_iface_vals) ->
                       let impls2 = FStarC_List.op_At impls1 iface_lets in
                       let impls3 =
                         let iface_let_names =
                           FStarC_List.collect
                             (fun d ->
                                if
                                  Prims.op_Negation
                                    d.FStarC_Parser_AST.interleaved
                                then []
                                else
                                  if
                                    Prims.op_Negation
                                      (Prims.uu___is_Nil
                                         d.FStarC_Parser_AST.attrs)
                                  then []
                                  else
                                    (match d.FStarC_Parser_AST.d with
                                     | FStarC_Parser_AST.TopLevelLet
                                         (uu___5, defs) ->
                                         let uu___6 =
                                           FStarC_Parser_AST.lids_of_let defs in
                                         FStarC_List.map
                                           (fun l1 ->
                                              FStarC_Ident.string_of_id
                                                (FStarC_Ident.ident_of_lid l1))
                                           uu___6
                                     | uu___5 -> [])) impls2 in
                         let iface_exn_names =
                           FStarC_List.collect
                             (fun d ->
                                if
                                  Prims.op_Negation
                                    d.FStarC_Parser_AST.interleaved
                                then []
                                else
                                  (match d.FStarC_Parser_AST.d with
                                   | FStarC_Parser_AST.Exception (id, uu___4)
                                       -> [FStarC_Ident.string_of_id id]
                                   | uu___4 -> [])) impls2 in
                         if
                           (Prims.uu___is_Nil iface_let_names) &&
                             (Prims.uu___is_Nil iface_exn_names)
                         then impls2
                         else
                           FStarC_List.filter
                             (fun d ->
                                if d.FStarC_Parser_AST.interleaved
                                then true
                                else
                                  (match d.FStarC_Parser_AST.d with
                                   | FStarC_Parser_AST.TopLevelLet
                                       (uu___5, defs) ->
                                       let fst_lids =
                                         let uu___6 =
                                           FStarC_Parser_AST.lids_of_let defs in
                                         FStarC_List.map
                                           (fun l1 ->
                                              FStarC_Ident.string_of_id
                                                (FStarC_Ident.ident_of_lid l1))
                                           uu___6 in
                                       if Prims.uu___is_Nil fst_lids
                                       then true
                                       else
                                         (let uu___7 =
                                            FStarC_Util.for_all
                                              (fun n ->
                                                 FStarC_Util.for_some
                                                   (fun m -> n = m)
                                                   iface_let_names) fst_lids in
                                          Prims.op_Negation uu___7)
                                   | FStarC_Parser_AST.Exception (id, uu___5)
                                       ->
                                       let uu___6 =
                                         FStarC_Util.for_some
                                           (fun m ->
                                              (FStarC_Ident.string_of_id id)
                                                = m) iface_exn_names in
                                       Prims.op_Negation uu___6
                                   | uu___5 -> true)) impls2 in
                       let env1 =
                         let uu___3 = FStarC_Options.interactive () in
                         if uu___3
                         then
                           FStarC_Syntax_DsEnv.set_iface_decls env l
                             remaining_iface_vals
                         else env in
                       let a1 =
                         FStarC_Parser_AST.Module
                           {
                             FStarC_Parser_AST.no_prelude = no_prelude;
                             FStarC_Parser_AST.mname = l;
                             FStarC_Parser_AST.decls = impls3
                           } in
                       (match remaining_iface_vals with
                        | uu___3::uu___4 when expect_complete_modul ->
                            ((let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_Class_Show.show
                                          FStarC_Ident.showable_lident l in
                                      FStarC_Format.fmt1
                                        "Some interface elements were not implemented by module %s:"
                                        uu___10 in
                                    FStarC_Errors_Msg.text uu___9 in
                                  let uu___9 =
                                    let uu___10 =
                                      FStarC_List.map
                                        (fun d ->
                                           let uu___11 =
                                             FStarC_Class_Show.show
                                               FStarC_Parser_AST.showable_decl
                                               d in
                                           FStar_Pprint.doc_of_string uu___11)
                                        remaining_iface_vals in
                                    FStarC_Errors_Msg.sublist
                                      FStar_Pprint.empty uu___10 in
                                  FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
                                [uu___7] in
                              FStarC_Errors.log_issue
                                FStarC_Ident.hasrange_lident l
                                FStarC_Errors_Codes.Fatal_InterfaceNotImplementedByModule
                                ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_list_doc)
                                (Obj.magic uu___6));
                             (a1, env1))
                        | uu___3 ->
                            ((let uu___5 =
                                FStarC_Options.dump_module
                                  (FStarC_Ident.string_of_lid l) in
                              if uu___5
                              then
                                let uu___6 =
                                  FStarC_Parser_AST.modul_to_string a1 in
                                FStarC_Format.print1
                                  "Interleaved module is:\n%s\n" uu___6
                              else ());
                             (a1, env1))))))
