open Prims
let (id_eq_lid : FStarC_Ident.ident -> FStarC_Ident.lident -> Prims.bool) =
  fun i ->
    fun l ->
      let uu___ = FStarC_Ident.string_of_id i in
      let uu___1 =
        let uu___2 = FStarC_Ident.ident_of_lid l in
        FStarC_Ident.string_of_id uu___2 in
      uu___ = uu___1
let (is_val : FStarC_Ident.ident -> FStarC_Parser_AST.decl -> Prims.bool) =
  fun x ->
    fun d ->
      match d.FStarC_Parser_AST.d with
      | FStarC_Parser_AST.Val (y, uu___) ->
          let uu___1 = FStarC_Ident.string_of_id x in
          let uu___2 = FStarC_Ident.string_of_id y in uu___1 = uu___2
      | uu___ -> false
let (is_type : FStarC_Ident.ident -> FStarC_Parser_AST.decl -> Prims.bool) =
  fun x ->
    fun d ->
      match d.FStarC_Parser_AST.d with
      | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) ->
          FStarC_Compiler_Util.for_some
            (fun t ->
               let uu___2 = FStarC_Parser_AST.id_of_tycon t in
               let uu___3 = FStarC_Ident.string_of_id x in uu___2 = uu___3)
            tys
      | uu___ -> false
let (definition_lids :
  FStarC_Parser_AST.decl -> FStarC_Ident.lident Prims.list) =
  fun d ->
    match d.FStarC_Parser_AST.d with
    | FStarC_Parser_AST.TopLevelLet (uu___, defs) ->
        FStarC_Parser_AST.lids_of_let defs
    | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) ->
        FStarC_Compiler_List.collect
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
        FStarC_Compiler_List.map (fun id -> FStarC_Ident.lid_of_ids [id]) ids
    | FStarC_Parser_AST.DeclToBeDesugared
        { FStarC_Parser_AST.lang_name = uu___;
          FStarC_Parser_AST.blob = uu___1; FStarC_Parser_AST.idents = ids;
          FStarC_Parser_AST.to_string = uu___2;
          FStarC_Parser_AST.eq = uu___3;
          FStarC_Parser_AST.dep_scan = uu___4;_}
        ->
        FStarC_Compiler_List.map (fun id -> FStarC_Ident.lid_of_ids [id]) ids
    | FStarC_Parser_AST.DeclSyntaxExtension
        (extension_name, code, uu___, range) ->
        let ext_parser =
          FStarC_Parser_AST_Util.lookup_extension_parser extension_name in
        (match ext_parser with
         | FStar_Pervasives_Native.None ->
             let uu___1 =
               FStarC_Compiler_Util.format1 "Unknown syntax extension %s"
                 extension_name in
             FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl d
               FStarC_Errors_Codes.Fatal_SyntaxError ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___1)
         | FStar_Pervasives_Native.Some parser ->
             let uu___1 =
               parser.FStarC_Parser_AST_Util.parse_decl_name code range in
             (match uu___1 with
              | FStar_Pervasives.Inl error ->
                  FStarC_Errors.raise_error
                    FStarC_Class_HasRange.hasRange_range
                    error.FStarC_Parser_AST_Util.range
                    FStarC_Errors_Codes.Fatal_SyntaxError ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic error.FStarC_Parser_AST_Util.message)
              | FStar_Pervasives.Inr id ->
                  let uu___2 = FStarC_Ident.lid_of_ids [id] in [uu___2]))
    | uu___ -> []
let (is_definition_of :
  FStarC_Ident.ident -> FStarC_Parser_AST.decl -> Prims.bool) =
  fun x ->
    fun d ->
      let uu___ = definition_lids d in
      FStarC_Compiler_Util.for_some (id_eq_lid x) uu___
let rec (prefix_with_iface_decls :
  FStarC_Parser_AST.decl Prims.list ->
    FStarC_Parser_AST.decl ->
      (FStarC_Parser_AST.decl Prims.list * FStarC_Parser_AST.decl Prims.list))
  =
  fun iface ->
    fun impl ->
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
          FStarC_Parser_AST.interleaved =
            (impl1.FStarC_Parser_AST.interleaved)
        } in
      match iface with
      | [] ->
          let uu___ = let uu___1 = qualify_karamel_private impl in [uu___1] in
          ([], uu___)
      | iface_hd::iface_tl ->
          (match iface_hd.FStarC_Parser_AST.d with
           | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) when
               FStarC_Compiler_Util.for_some
                 (fun uu___2 ->
                    match uu___2 with
                    | FStarC_Parser_AST.TyconAbstract uu___3 -> true
                    | uu___3 -> false) tys
               ->
               let uu___2 =
                 let uu___3 =
                   FStarC_Errors_Msg.text
                     "Interface contains an abstract 'type' declaration; use 'val' instead." in
                 [uu___3] in
               FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl impl
                 FStarC_Errors_Codes.Fatal_AbstractTypeDeclarationInInterface
                 () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___2)
           | FStarC_Parser_AST.Splice (uu___, x::[], uu___1) ->
               let def_ids = definition_lids impl in
               let defines_x =
                 FStarC_Compiler_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 ((let uu___3 =
                     FStarC_Compiler_Util.for_some
                       (fun y ->
                          let uu___4 =
                            let uu___5 = FStarC_Ident.ident_of_lid y in
                            is_val uu___5 in
                          FStarC_Compiler_Util.for_some uu___4 iface_tl)
                       def_ids in
                   if uu___3
                   then
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStarC_Errors_Msg.text
                             "Expected the definition of" in
                         let uu___7 =
                           let uu___8 =
                             FStarC_Class_PP.pp FStarC_Ident.pretty_ident x in
                           let uu___9 =
                             let uu___10 =
                               FStarC_Errors_Msg.text "to precede" in
                             let uu___11 =
                               FStarC_Class_PP.pp
                                 (FStarC_Class_PP.pp_list
                                    FStarC_Ident.pretty_lident) def_ids in
                             FStarC_Pprint.op_Hat_Slash_Hat uu___10 uu___11 in
                           FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                         FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                       [uu___5] in
                     FStarC_Errors.raise_error
                       FStarC_Parser_AST.hasRange_decl impl
                       FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___4)
                   else ());
                  (let uu___3 =
                     let uu___4 = qualify_karamel_private impl in [uu___4] in
                   (iface, uu___3)))
               else
                 (let mutually_defined_with_x =
                    FStarC_Compiler_List.filter
                      (fun y ->
                         let uu___3 = id_eq_lid x y in
                         Prims.op_Negation uu___3) def_ids in
                  let rec aux mutuals iface1 =
                    match (mutuals, iface1) with
                    | ([], uu___3) -> ([], iface1)
                    | (uu___3::uu___4, []) -> ([], [])
                    | (y::ys, iface_hd1::iface_tl1) when
                        let uu___3 = FStarC_Ident.ident_of_lid y in
                        is_val uu___3 iface_hd1 ->
                        let uu___3 = aux ys iface_tl1 in
                        (match uu___3 with
                         | (val_ys, iface2) ->
                             ((iface_hd1 :: val_ys), iface2))
                    | (y::ys, iface_hd1::iface_tl1) when
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = FStarC_Ident.ident_of_lid y in
                            is_val uu___5 in
                          FStarC_Compiler_List.tryFind uu___4 iface_tl1 in
                        FStarC_Compiler_Option.isSome uu___3 ->
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStarC_Class_Show.show
                                  FStarC_Parser_AST.showable_decl iface_hd1 in
                              let uu___7 = FStarC_Ident.string_of_lid y in
                              FStarC_Compiler_Util.format2
                                "%s is out of order with the definition of %s"
                                uu___6 uu___7 in
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
                        (FStarC_Compiler_List.op_At (iface_hd :: take_iface)
                           [impl])))
           | FStarC_Parser_AST.Val (x, uu___) ->
               let def_ids = definition_lids impl in
               let defines_x =
                 FStarC_Compiler_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 ((let uu___2 =
                     FStarC_Compiler_Util.for_some
                       (fun y ->
                          let uu___3 =
                            let uu___4 = FStarC_Ident.ident_of_lid y in
                            is_val uu___4 in
                          FStarC_Compiler_Util.for_some uu___3 iface_tl)
                       def_ids in
                   if uu___2
                   then
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStarC_Errors_Msg.text
                             "Expected the definition of" in
                         let uu___6 =
                           let uu___7 =
                             FStarC_Class_PP.pp FStarC_Ident.pretty_ident x in
                           let uu___8 =
                             let uu___9 = FStarC_Errors_Msg.text "to precede" in
                             let uu___10 =
                               FStarC_Class_PP.pp
                                 (FStarC_Class_PP.pp_list
                                    FStarC_Ident.pretty_lident) def_ids in
                             FStarC_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                           FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                         FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                       [uu___4] in
                     FStarC_Errors.raise_error
                       FStarC_Parser_AST.hasRange_decl impl
                       FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___3)
                   else ());
                  (let uu___2 =
                     let uu___3 = qualify_karamel_private impl in [uu___3] in
                   (iface, uu___2)))
               else
                 (let mutually_defined_with_x =
                    FStarC_Compiler_List.filter
                      (fun y ->
                         let uu___2 = id_eq_lid x y in
                         Prims.op_Negation uu___2) def_ids in
                  let rec aux mutuals iface1 =
                    match (mutuals, iface1) with
                    | ([], uu___2) -> ([], iface1)
                    | (uu___2::uu___3, []) -> ([], [])
                    | (y::ys, iface_hd1::iface_tl1) when
                        let uu___2 = FStarC_Ident.ident_of_lid y in
                        is_val uu___2 iface_hd1 ->
                        let uu___2 = aux ys iface_tl1 in
                        (match uu___2 with
                         | (val_ys, iface2) ->
                             ((iface_hd1 :: val_ys), iface2))
                    | (y::ys, iface_hd1::iface_tl1) when
                        let uu___2 =
                          let uu___3 =
                            let uu___4 = FStarC_Ident.ident_of_lid y in
                            is_val uu___4 in
                          FStarC_Compiler_List.tryFind uu___3 iface_tl1 in
                        FStarC_Compiler_Option.isSome uu___2 ->
                        let uu___2 =
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                FStarC_Class_Show.show
                                  FStarC_Parser_AST.showable_decl iface_hd1 in
                              let uu___6 = FStarC_Ident.string_of_lid y in
                              FStarC_Compiler_Util.format2
                                "%s is out of order with the definition of %s"
                                uu___5 uu___6 in
                            FStarC_Errors_Msg.text uu___4 in
                          [uu___3] in
                        FStarC_Errors.raise_error
                          FStarC_Parser_AST.hasRange_decl iface_hd1
                          FStarC_Errors_Codes.Fatal_WrongDefinitionOrder ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_list_doc)
                          (Obj.magic uu___2)
                    | (y::ys, iface_hd1::iface_tl1) -> aux ys iface1 in
                  let uu___2 = aux mutually_defined_with_x iface_tl in
                  match uu___2 with
                  | (take_iface, rest_iface) ->
                      (rest_iface,
                        (FStarC_Compiler_List.op_At (iface_hd :: take_iface)
                           [impl])))
           | FStarC_Parser_AST.Pragma uu___ ->
               prefix_with_iface_decls iface_tl impl
           | uu___ ->
               let uu___1 = prefix_with_iface_decls iface_tl impl in
               (match uu___1 with
                | (iface1, ds) -> (iface1, (iface_hd :: ds))))
let (check_initial_interface :
  FStarC_Parser_AST.decl Prims.list -> FStarC_Parser_AST.decl Prims.list) =
  fun iface ->
    let rec aux iface1 =
      match iface1 with
      | [] -> ()
      | hd::tl ->
          (match hd.FStarC_Parser_AST.d with
           | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) when
               FStarC_Compiler_Util.for_some
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
               let uu___ =
                 FStarC_Compiler_Util.for_some (is_definition_of x) tl in
               if uu___
               then
                 let uu___1 =
                   let uu___2 = FStarC_Ident.string_of_id x in
                   let uu___3 = FStarC_Ident.string_of_id x in
                   FStarC_Compiler_Util.format2
                     "'val %s' and 'let %s' cannot both be provided in an interface"
                     uu___2 uu___3 in
                 FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl hd
                   FStarC_Errors_Codes.Fatal_BothValAndLetInInterface ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___1)
               else
                 if
                   FStarC_Compiler_List.contains FStarC_Parser_AST.Assumption
                     hd.FStarC_Parser_AST.quals
                 then
                   FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl
                     hd FStarC_Errors_Codes.Fatal_AssumeValInInterface ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                 else ()
           | uu___ -> ()) in
    aux iface;
    FStarC_Compiler_List.filter
      (fun d ->
         match d.FStarC_Parser_AST.d with
         | FStarC_Parser_AST.TopLevelModule uu___1 -> false
         | uu___1 -> true) iface
let (ml_mode_prefix_with_iface_decls :
  FStarC_Parser_AST.decl Prims.list ->
    FStarC_Parser_AST.decl ->
      (FStarC_Parser_AST.decl Prims.list * FStarC_Parser_AST.decl Prims.list))
  =
  fun iface ->
    fun impl ->
      match impl.FStarC_Parser_AST.d with
      | FStarC_Parser_AST.TopLevelModule uu___ ->
          let uu___1 =
            FStarC_Compiler_List.span
              (fun d ->
                 match d.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.Open uu___2 -> true
                 | FStarC_Parser_AST.ModuleAbbrev uu___2 -> true
                 | uu___2 -> false) iface in
          (match uu___1 with
           | (iface_prefix_opens, iface1) ->
               let iface2 =
                 FStarC_Compiler_List.filter
                   (fun d ->
                      match d.FStarC_Parser_AST.d with
                      | FStarC_Parser_AST.Val uu___2 -> true
                      | FStarC_Parser_AST.Tycon uu___2 -> true
                      | uu___2 -> false) iface1 in
               (iface2,
                 (FStarC_Compiler_List.op_At [impl] iface_prefix_opens)))
      | FStarC_Parser_AST.Open uu___ ->
          let uu___1 =
            FStarC_Compiler_List.span
              (fun d ->
                 match d.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.Open uu___2 -> true
                 | FStarC_Parser_AST.ModuleAbbrev uu___2 -> true
                 | uu___2 -> false) iface in
          (match uu___1 with
           | (iface_prefix_opens, iface1) ->
               let iface2 =
                 FStarC_Compiler_List.filter
                   (fun d ->
                      match d.FStarC_Parser_AST.d with
                      | FStarC_Parser_AST.Val uu___2 -> true
                      | FStarC_Parser_AST.Tycon uu___2 -> true
                      | uu___2 -> false) iface1 in
               (iface2,
                 (FStarC_Compiler_List.op_At [impl] iface_prefix_opens)))
      | FStarC_Parser_AST.Friend uu___ ->
          let uu___1 =
            FStarC_Compiler_List.span
              (fun d ->
                 match d.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.Open uu___2 -> true
                 | FStarC_Parser_AST.ModuleAbbrev uu___2 -> true
                 | uu___2 -> false) iface in
          (match uu___1 with
           | (iface_prefix_opens, iface1) ->
               let iface2 =
                 FStarC_Compiler_List.filter
                   (fun d ->
                      match d.FStarC_Parser_AST.d with
                      | FStarC_Parser_AST.Val uu___2 -> true
                      | FStarC_Parser_AST.Tycon uu___2 -> true
                      | uu___2 -> false) iface1 in
               (iface2,
                 (FStarC_Compiler_List.op_At [impl] iface_prefix_opens)))
      | FStarC_Parser_AST.Include uu___ ->
          let uu___1 =
            FStarC_Compiler_List.span
              (fun d ->
                 match d.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.Open uu___2 -> true
                 | FStarC_Parser_AST.ModuleAbbrev uu___2 -> true
                 | uu___2 -> false) iface in
          (match uu___1 with
           | (iface_prefix_opens, iface1) ->
               let iface2 =
                 FStarC_Compiler_List.filter
                   (fun d ->
                      match d.FStarC_Parser_AST.d with
                      | FStarC_Parser_AST.Val uu___2 -> true
                      | FStarC_Parser_AST.Tycon uu___2 -> true
                      | uu___2 -> false) iface1 in
               (iface2,
                 (FStarC_Compiler_List.op_At [impl] iface_prefix_opens)))
      | FStarC_Parser_AST.ModuleAbbrev uu___ ->
          let uu___1 =
            FStarC_Compiler_List.span
              (fun d ->
                 match d.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.Open uu___2 -> true
                 | FStarC_Parser_AST.ModuleAbbrev uu___2 -> true
                 | uu___2 -> false) iface in
          (match uu___1 with
           | (iface_prefix_opens, iface1) ->
               let iface2 =
                 FStarC_Compiler_List.filter
                   (fun d ->
                      match d.FStarC_Parser_AST.d with
                      | FStarC_Parser_AST.Val uu___2 -> true
                      | FStarC_Parser_AST.Tycon uu___2 -> true
                      | uu___2 -> false) iface1 in
               (iface2,
                 (FStarC_Compiler_List.op_At [impl] iface_prefix_opens)))
      | uu___ ->
          let uu___1 =
            FStarC_Compiler_List.span
              (fun d ->
                 match d.FStarC_Parser_AST.d with
                 | FStarC_Parser_AST.Tycon uu___2 -> true
                 | uu___2 -> false) iface in
          (match uu___1 with
           | (iface_prefix_tycons, iface1) ->
               let maybe_get_iface_vals lids iface2 =
                 FStarC_Compiler_List.partition
                   (fun d ->
                      FStarC_Compiler_Util.for_some
                        (fun x ->
                           let uu___2 = FStarC_Ident.ident_of_lid x in
                           is_val uu___2 d) lids) iface2 in
               (match impl.FStarC_Parser_AST.d with
                | FStarC_Parser_AST.TopLevelLet uu___2 ->
                    let xs = definition_lids impl in
                    let uu___3 = maybe_get_iface_vals xs iface1 in
                    (match uu___3 with
                     | (val_xs, rest_iface) ->
                         (rest_iface,
                           (FStarC_Compiler_List.op_At iface_prefix_tycons
                              (FStarC_Compiler_List.op_At val_xs [impl]))))
                | FStarC_Parser_AST.Tycon uu___2 ->
                    let xs = definition_lids impl in
                    let uu___3 = maybe_get_iface_vals xs iface1 in
                    (match uu___3 with
                     | (val_xs, rest_iface) ->
                         (rest_iface,
                           (FStarC_Compiler_List.op_At iface_prefix_tycons
                              (FStarC_Compiler_List.op_At val_xs [impl]))))
                | uu___2 ->
                    (iface1,
                      (FStarC_Compiler_List.op_At iface_prefix_tycons [impl]))))
let ml_mode_check_initial_interface :
  'uuuuu .
    'uuuuu ->
      FStarC_Parser_AST.decl Prims.list -> FStarC_Parser_AST.decl Prims.list
  =
  fun mname ->
    fun iface ->
      FStarC_Compiler_List.filter
        (fun d ->
           match d.FStarC_Parser_AST.d with
           | FStarC_Parser_AST.Tycon (uu___, uu___1, tys) when
               FStarC_Compiler_Util.for_some
                 (fun uu___2 ->
                    match uu___2 with
                    | FStarC_Parser_AST.TyconAbstract uu___3 -> true
                    | uu___3 -> false) tys
               ->
               FStarC_Errors.raise_error FStarC_Parser_AST.hasRange_decl d
                 FStarC_Errors_Codes.Fatal_AbstractTypeDeclarationInInterface
                 () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic
                    "Interface contains an abstract 'type' declaration; use 'val' instead")
           | FStarC_Parser_AST.Tycon uu___ -> true
           | FStarC_Parser_AST.Val uu___ -> true
           | FStarC_Parser_AST.Open uu___ -> true
           | FStarC_Parser_AST.ModuleAbbrev uu___ -> true
           | uu___ -> false) iface
let (ulib_modules : Prims.string Prims.list) =
  ["FStar.Calc";
  "FStar.TSet";
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
let (apply_ml_mode_optimizations : FStarC_Ident.lident -> Prims.bool) =
  fun mname ->
    ((FStarC_Options.ml_ish ()) &&
       (let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid mname in
          let uu___2 = FStarC_Parser_Dep.core_modules () in
          FStarC_Compiler_List.contains uu___1 uu___2 in
        Prims.op_Negation uu___))
      &&
      (let uu___ =
         let uu___1 = FStarC_Ident.string_of_lid mname in
         FStarC_Compiler_List.contains uu___1 ulib_modules in
       Prims.op_Negation uu___)
let (prefix_one_decl :
  FStarC_Ident.lident ->
    FStarC_Parser_AST.decl Prims.list ->
      FStarC_Parser_AST.decl ->
        (FStarC_Parser_AST.decl Prims.list * FStarC_Parser_AST.decl
          Prims.list))
  =
  fun mname ->
    fun iface ->
      fun impl ->
        match impl.FStarC_Parser_AST.d with
        | FStarC_Parser_AST.TopLevelModule uu___ -> (iface, [impl])
        | uu___ ->
            let uu___1 = apply_ml_mode_optimizations mname in
            if uu___1
            then ml_mode_prefix_with_iface_decls iface impl
            else prefix_with_iface_decls iface impl
let (initialize_interface :
  FStarC_Ident.lident ->
    FStarC_Parser_AST.decl Prims.list -> unit FStarC_Syntax_DsEnv.withenv)
  =
  fun mname ->
    fun l ->
      fun env ->
        let decls =
          let uu___ = apply_ml_mode_optimizations mname in
          if uu___
          then ml_mode_check_initial_interface mname l
          else check_initial_interface l in
        let uu___ = FStarC_Syntax_DsEnv.iface_decls env mname in
        match uu___ with
        | FStar_Pervasives_Native.Some uu___1 ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Ident.showable_lident mname in
              FStarC_Compiler_Util.format1
                "Interface %s has already been processed" uu___3 in
            FStarC_Errors.raise_error FStarC_Ident.hasrange_lident mname
              FStarC_Errors_Codes.Fatal_InterfaceAlreadyProcessed ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2)
        | FStar_Pervasives_Native.None ->
            let uu___1 = FStarC_Syntax_DsEnv.set_iface_decls env mname decls in
            ((), uu___1)
let (fixup_interleaved_decls :
  FStarC_Parser_AST.decl Prims.list -> FStarC_Parser_AST.decl Prims.list) =
  fun iface ->
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
    FStarC_Compiler_List.map fix1 iface
let (prefix_with_interface_decls :
  FStarC_Ident.lident ->
    FStarC_Parser_AST.decl ->
      FStarC_Parser_AST.decl Prims.list FStarC_Syntax_DsEnv.withenv)
  =
  fun mname ->
    fun impl ->
      fun env ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Syntax_DsEnv.current_module env in
            FStarC_Syntax_DsEnv.iface_decls env uu___2 in
          match uu___1 with
          | FStar_Pervasives_Native.None -> ([impl], env)
          | FStar_Pervasives_Native.Some iface ->
              let iface1 = fixup_interleaved_decls iface in
              let uu___2 = prefix_one_decl mname iface1 impl in
              (match uu___2 with
               | (iface2, impl1) ->
                   let env1 =
                     let uu___3 = FStarC_Syntax_DsEnv.current_module env in
                     FStarC_Syntax_DsEnv.set_iface_decls env uu___3 iface2 in
                   (impl1, env1)) in
        match uu___ with
        | (decls, env1) ->
            ((let uu___2 =
                let uu___3 = FStarC_Ident.string_of_lid mname in
                FStarC_Options.dump_module uu___3 in
              if uu___2
              then
                let uu___3 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list
                       FStarC_Parser_AST.showable_decl) decls in
                FStarC_Compiler_Util.print1 "Interleaved decls:\n%s\n" uu___3
              else ());
             (decls, env1))
let (interleave_module :
  FStarC_Parser_AST.modul ->
    Prims.bool -> FStarC_Parser_AST.modul FStarC_Syntax_DsEnv.withenv)
  =
  fun a ->
    fun expect_complete_modul ->
      fun env ->
        match a with
        | FStarC_Parser_AST.Interface uu___ -> (a, env)
        | FStarC_Parser_AST.Module (l, impls) ->
            let uu___ = FStarC_Syntax_DsEnv.iface_decls env l in
            (match uu___ with
             | FStar_Pervasives_Native.None -> (a, env)
             | FStar_Pervasives_Native.Some iface ->
                 let iface1 = fixup_interleaved_decls iface in
                 let uu___1 =
                   FStarC_Compiler_List.fold_left
                     (fun uu___2 ->
                        fun impl ->
                          match uu___2 with
                          | (iface2, impls1) ->
                              let uu___3 = prefix_one_decl l iface2 impl in
                              (match uu___3 with
                               | (iface3, impls') ->
                                   (iface3,
                                     (FStarC_Compiler_List.op_At impls1
                                        impls')))) (iface1, []) impls in
                 (match uu___1 with
                  | (iface2, impls1) ->
                      let uu___2 =
                        let uu___3 =
                          FStarC_Compiler_Util.prefix_until
                            (fun uu___4 ->
                               match uu___4 with
                               | {
                                   FStarC_Parser_AST.d =
                                     FStarC_Parser_AST.Val uu___5;
                                   FStarC_Parser_AST.drange = uu___6;
                                   FStarC_Parser_AST.quals = uu___7;
                                   FStarC_Parser_AST.attrs = uu___8;
                                   FStarC_Parser_AST.interleaved = uu___9;_}
                                   -> true
                               | {
                                   FStarC_Parser_AST.d =
                                     FStarC_Parser_AST.Splice uu___5;
                                   FStarC_Parser_AST.drange = uu___6;
                                   FStarC_Parser_AST.quals = uu___7;
                                   FStarC_Parser_AST.attrs = uu___8;
                                   FStarC_Parser_AST.interleaved = uu___9;_}
                                   -> true
                               | uu___5 -> false) iface2 in
                        match uu___3 with
                        | FStar_Pervasives_Native.None -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets, one_val, rest)
                            -> (lets, (one_val :: rest)) in
                      (match uu___2 with
                       | (iface_lets, remaining_iface_vals) ->
                           let impls2 =
                             FStarC_Compiler_List.op_At impls1 iface_lets in
                           let env1 =
                             let uu___3 = FStarC_Options.interactive () in
                             if uu___3
                             then
                               FStarC_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env in
                           let a1 = FStarC_Parser_AST.Module (l, impls2) in
                           (match remaining_iface_vals with
                            | uu___3::uu___4 when expect_complete_modul ->
                                ((let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            FStarC_Class_Show.show
                                              FStarC_Ident.showable_lident l in
                                          FStarC_Compiler_Util.format1
                                            "Some interface elements were not implemented by module %s:"
                                            uu___10 in
                                        FStarC_Errors_Msg.text uu___9 in
                                      let uu___9 =
                                        let uu___10 =
                                          FStarC_Compiler_List.map
                                            (fun d ->
                                               let uu___11 =
                                                 FStarC_Class_Show.show
                                                   FStarC_Parser_AST.showable_decl
                                                   d in
                                               FStarC_Pprint.doc_of_string
                                                 uu___11)
                                            remaining_iface_vals in
                                        FStarC_Errors_Msg.sublist
                                          FStarC_Pprint.empty uu___10 in
                                      FStarC_Pprint.op_Hat_Hat uu___8 uu___9 in
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
                                    let uu___6 = FStarC_Ident.string_of_lid l in
                                    FStarC_Options.dump_module uu___6 in
                                  if uu___5
                                  then
                                    let uu___6 =
                                      FStarC_Parser_AST.modul_to_string a1 in
                                    FStarC_Compiler_Util.print1
                                      "Interleaved module is:\n%s\n" uu___6
                                  else ());
                                 (a1, env1))))))