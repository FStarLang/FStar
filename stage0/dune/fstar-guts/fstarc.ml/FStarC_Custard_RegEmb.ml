open Prims
exception NoEmbedding of Prims.string 
let uu___is_NoEmbedding (projectee : Prims.exn) : Prims.bool= true
let __proj__NoEmbedding__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | NoEmbedding uu___ -> uu___
let warn_not_implemented (r : FStarC_Range_Type.t) (what : Prims.string)
  (msg : Prims.string) : unit=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                FStarC_Errors.lookup
                  FStarC_Errors_Codes.Warning_PluginNotImplemented in
              FStarC_Errors.error_number uu___6 in
            FStarC_Class_PP.pp FStarC_Class_PP.pp_int uu___5 in
          FStar_Pprint.op_Hat_Slash_Hat uu___4
            (FStarC_Errors_Msg.text "to carry on.") in
        FStar_Pprint.op_Hat_Hat (FStarC_Errors_Msg.text "Use --warn_error -")
          uu___3 in
      [uu___2] in
    (FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
       (FStarC_Errors_Msg.text
          (FStarC_Format.fmt1 "Plugin `%s' can not run natively because:"
             what)) (FStarC_Errors_Msg.text msg))
      :: uu___1 in
  FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
    FStarC_Errors_Codes.Warning_PluginNotImplemented ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
type embedding_data =
  {
  arity: Prims.int ;
  syn_emb: FStarC_Ident.lident ;
  nbe_emb: FStarC_Ident.lident FStar_Pervasives_Native.option }
let __proj__Mkembedding_data__item__arity (projectee : embedding_data) :
  Prims.int= match projectee with | { arity; syn_emb; nbe_emb;_} -> arity
let __proj__Mkembedding_data__item__syn_emb (projectee : embedding_data) :
  FStarC_Ident.lident=
  match projectee with | { arity; syn_emb; nbe_emb;_} -> syn_emb
let __proj__Mkembedding_data__item__nbe_emb (projectee : embedding_data) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  match projectee with | { arity; syn_emb; nbe_emb;_} -> nbe_emb
let builtin_embeddings : (FStarC_Ident.lident * embedding_data) Prims.list=
  let syn s =
    FStarC_Ident.lid_of_path ["FStarC"; "Syntax"; "Embeddings"; s]
      FStarC_Range_Type.dummyRange in
  let nbe s =
    FStarC_Ident.lid_of_path ["FStarC"; "TypeChecker"; "NBETerm"; s]
      FStarC_Range_Type.dummyRange in
  let refl s =
    FStarC_Ident.lid_of_path ["FStarC"; "Reflection"; "V2"; "Embeddings"; s]
      FStarC_Range_Type.dummyRange in
  let nbe_refl s =
    FStarC_Ident.lid_of_path
      ["FStarC"; "Reflection"; "V2"; "NBEEmbeddings"; s]
      FStarC_Range_Type.dummyRange in
  let base n s =
    let uu___ = syn s in
    let uu___1 = let uu___2 = nbe s in FStar_Pervasives_Native.Some uu___2 in
    { arity = n; syn_emb = uu___; nbe_emb = uu___1 } in
  let rfl s =
    let uu___ = refl s in
    let uu___1 =
      let uu___2 = nbe_refl s in FStar_Pervasives_Native.Some uu___2 in
    { arity = Prims.int_zero; syn_emb = uu___; nbe_emb = uu___1 } in
  let uu___ =
    let uu___1 = base Prims.int_zero "e_int" in
    (FStarC_Parser_Const.int_lid, uu___1) in
  let uu___1 =
    let uu___2 =
      let uu___3 = base Prims.int_zero "e_bool" in
      (FStarC_Parser_Const.bool_lid, uu___3) in
    let uu___3 =
      let uu___4 =
        let uu___5 = base Prims.int_zero "e_unit" in
        (FStarC_Parser_Const.unit_lid, uu___5) in
      let uu___5 =
        let uu___6 =
          let uu___7 = base Prims.int_zero "e_string" in
          (FStarC_Parser_Const.string_lid, uu___7) in
        let uu___7 =
          let uu___8 =
            let uu___9 = base Prims.int_zero "e_norm_step" in
            (FStarC_Parser_Const.norm_step_lid, uu___9) in
          let uu___9 =
            let uu___10 =
              let uu___11 = base Prims.int_zero "e_range" in
              (FStarC_Parser_Const.range_lid, uu___11) in
            let uu___11 =
              let uu___12 =
                let uu___13 = base Prims.int_zero "e_vconfig" in
                (FStarC_Parser_Const.vconfig_lid, uu___13) in
              let uu___13 =
                let uu___14 =
                  let uu___15 = base Prims.int_one "e_list" in
                  (FStarC_Parser_Const.list_lid, uu___15) in
                let uu___15 =
                  let uu___16 =
                    let uu___17 = base Prims.int_one "e_option" in
                    (FStarC_Parser_Const.option_lid, uu___17) in
                  let uu___17 =
                    let uu___18 =
                      let uu___19 = base Prims.int_one "e_sealed" in
                      (FStarC_Parser_Const.sealed_lid, uu___19) in
                    let uu___19 =
                      let uu___20 =
                        let uu___21 =
                          FStarC_Parser_Const_Tuples.mk_tuple_lid
                            (Prims.of_int 2) FStarC_Range_Type.dummyRange in
                        let uu___22 = base (Prims.of_int 2) "e_tuple2" in
                        (uu___21, uu___22) in
                      let uu___21 =
                        let uu___22 =
                          let uu___23 =
                            FStarC_Parser_Const_Tuples.mk_tuple_lid
                              (Prims.of_int 3) FStarC_Range_Type.dummyRange in
                          let uu___24 = base (Prims.of_int 3) "e_tuple3" in
                          (uu___23, uu___24) in
                        let uu___23 =
                          let uu___24 =
                            let uu___25 = base (Prims.of_int 2) "e_either" in
                            (FStarC_Parser_Const.either_lid, uu___25) in
                          let uu___25 =
                            let uu___26 =
                              let uu___27 =
                                FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                  "namedv" in
                              let uu___28 = rfl "e_namedv" in
                              (uu___27, uu___28) in
                            let uu___27 =
                              let uu___28 =
                                let uu___29 =
                                  FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                    "bv" in
                                let uu___30 = rfl "e_bv" in
                                (uu___29, uu___30) in
                              let uu___29 =
                                let uu___30 =
                                  let uu___31 =
                                    FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                      "binder" in
                                  let uu___32 = rfl "e_binder" in
                                  (uu___31, uu___32) in
                                let uu___31 =
                                  let uu___32 =
                                    let uu___33 =
                                      FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                        "term" in
                                    let uu___34 = rfl "e_term" in
                                    (uu___33, uu___34) in
                                  let uu___33 =
                                    let uu___34 =
                                      let uu___35 =
                                        FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                          "env" in
                                      let uu___36 = rfl "e_env" in
                                      (uu___35, uu___36) in
                                    let uu___35 =
                                      let uu___36 =
                                        let uu___37 =
                                          FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                            "fv" in
                                        let uu___38 = rfl "e_fv" in
                                        (uu___37, uu___38) in
                                      let uu___37 =
                                        let uu___38 =
                                          let uu___39 =
                                            FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                              "comp" in
                                          let uu___40 = rfl "e_comp" in
                                          (uu___39, uu___40) in
                                        let uu___39 =
                                          let uu___40 =
                                            let uu___41 =
                                              FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                                "sigelt" in
                                            let uu___42 = rfl "e_sigelt" in
                                            (uu___41, uu___42) in
                                          let uu___41 =
                                            let uu___42 =
                                              let uu___43 =
                                                FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                                  "ctx_uvar_and_subst" in
                                              let uu___44 =
                                                rfl "e_ctx_uvar_and_subst" in
                                              (uu___43, uu___44) in
                                            let uu___43 =
                                              let uu___44 =
                                                let uu___45 =
                                                  FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                                    "letbinding" in
                                                let uu___46 =
                                                  rfl "e_letbinding" in
                                                (uu___45, uu___46) in
                                              let uu___45 =
                                                let uu___46 =
                                                  let uu___47 =
                                                    FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                                      "ident" in
                                                  let uu___48 = rfl "e_ident" in
                                                  (uu___47, uu___48) in
                                                let uu___47 =
                                                  let uu___48 =
                                                    let uu___49 =
                                                      FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                                        "universe_uvar" in
                                                    let uu___50 =
                                                      rfl "e_universe_uvar" in
                                                    (uu___49, uu___50) in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      let uu___51 =
                                                        FStarC_Reflection_V2_Constants.fstar_refl_types_lid
                                                          "universe" in
                                                      let uu___52 =
                                                        rfl "e_universe" in
                                                      (uu___51, uu___52) in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        let uu___53 =
                                                          FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                            "vconst" in
                                                        let uu___54 =
                                                          rfl "e_vconst" in
                                                        (uu___53, uu___54) in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          let uu___55 =
                                                            FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                              "aqualv" in
                                                          let uu___56 =
                                                            rfl "e_aqualv" in
                                                          (uu___55, uu___56) in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            let uu___57 =
                                                              FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                "pattern" in
                                                            let uu___58 =
                                                              rfl "e_pattern" in
                                                            (uu___57,
                                                              uu___58) in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              let uu___59 =
                                                                FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                  "namedv_view" in
                                                              let uu___60 =
                                                                rfl
                                                                  "e_namedv_view" in
                                                              (uu___59,
                                                                uu___60) in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "bv_view" in
                                                                let uu___62 =
                                                                  rfl
                                                                    "e_bv_view" in
                                                                (uu___61,
                                                                  uu___62) in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "binder_view" in
                                                                  let uu___64
                                                                    =
                                                                    rfl
                                                                    "e_binder_view" in
                                                                  (uu___63,
                                                                    uu___64) in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "binding" in
                                                                    let uu___66
                                                                    =
                                                                    rfl
                                                                    "e_binding" in
                                                                    (uu___65,
                                                                    uu___66) in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "universe_view" in
                                                                    let uu___68
                                                                    =
                                                                    rfl
                                                                    "e_universe_view" in
                                                                    (uu___67,
                                                                    uu___68) in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "term_view" in
                                                                    let uu___70
                                                                    =
                                                                    rfl
                                                                    "e_term_view" in
                                                                    (uu___69,
                                                                    uu___70) in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "comp_view" in
                                                                    let uu___72
                                                                    =
                                                                    rfl
                                                                    "e_comp_view" in
                                                                    (uu___71,
                                                                    uu___72) in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "lb_view" in
                                                                    let uu___74
                                                                    =
                                                                    rfl
                                                                    "e_lb_view" in
                                                                    (uu___73,
                                                                    uu___74) in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "sigelt_view" in
                                                                    let uu___76
                                                                    =
                                                                    rfl
                                                                    "e_sigelt_view" in
                                                                    (uu___75,
                                                                    uu___76) in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    FStarC_Reflection_V2_Constants.fstar_refl_data_lid
                                                                    "qualifier" in
                                                                    let uu___78
                                                                    =
                                                                    rfl
                                                                    "e_qualifier" in
                                                                    (uu___77,
                                                                    uu___78) in
                                                                    [uu___76] in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                  uu___64 ::
                                                                    uu___65 in
                                                                uu___62 ::
                                                                  uu___63 in
                                                              uu___60 ::
                                                                uu___61 in
                                                            uu___58 ::
                                                              uu___59 in
                                                          uu___56 :: uu___57 in
                                                        uu___54 :: uu___55 in
                                                      uu___52 :: uu___53 in
                                                    uu___50 :: uu___51 in
                                                  uu___48 :: uu___49 in
                                                uu___46 :: uu___47 in
                                              uu___44 :: uu___45 in
                                            uu___42 :: uu___43 in
                                          uu___40 :: uu___41 in
                                        uu___38 :: uu___39 in
                                      uu___36 :: uu___37 in
                                    uu___34 :: uu___35 in
                                  uu___32 :: uu___33 in
                                uu___30 :: uu___31 in
                              uu___28 :: uu___29 in
                            uu___26 :: uu___27 in
                          uu___24 :: uu___25 in
                        uu___22 :: uu___23 in
                      uu___20 :: uu___21 in
                    uu___18 :: uu___19 in
                  uu___16 :: uu___17 in
                uu___14 :: uu___15 in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
let find_embedding (l : FStarC_Ident.lident) :
  embedding_data FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.find
      (fun uu___1 ->
         match uu___1 with | (l', uu___2) -> FStarC_Ident.lid_equals l l')
      builtin_embeddings in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, d) ->
      FStar_Pervasives_Native.Some d
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
type gen_emb =
  {
  ge_lid: FStarC_Ident.lident ;
  ge_ph: FStarC_Syntax_Syntax.bv ;
  ge_emb: FStarC_Custard_Syntax.name ;
  ge_knot: FStarC_Custard_Syntax.name }
let __proj__Mkgen_emb__item__ge_lid (projectee : gen_emb) :
  FStarC_Ident.lident=
  match projectee with | { ge_lid; ge_ph; ge_emb; ge_knot;_} -> ge_lid
let __proj__Mkgen_emb__item__ge_ph (projectee : gen_emb) :
  FStarC_Syntax_Syntax.bv=
  match projectee with | { ge_lid; ge_ph; ge_emb; ge_knot;_} -> ge_ph
let __proj__Mkgen_emb__item__ge_emb (projectee : gen_emb) :
  FStarC_Custard_Syntax.name=
  match projectee with | { ge_lid; ge_ph; ge_emb; ge_knot;_} -> ge_emb
let __proj__Mkgen_emb__item__ge_knot (projectee : gen_emb) :
  FStarC_Custard_Syntax.name=
  match projectee with | { ge_lid; ge_ph; ge_emb; ge_knot;_} -> ge_knot
let generated : gen_emb Prims.list FStarC_Effect.ref= FStarC_Effect.mk_ref []
let building : FStarC_Ident.lident Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let find_generated (l : FStarC_Ident.lident) :
  gen_emb FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang generated in
  FStarC_List.find (fun g -> FStarC_Ident.lid_equals g.ge_lid l) uu___
let emb_base (s : Prims.string) : FStarC_Ident.lident=
  FStarC_Ident.lid_of_str (Prims.strcat "FStarC.Syntax.Embeddings.Base." s)
let embedding_typ (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.typ=
  let uu___ =
    let uu___1 =
      FStarC_Ident.lid_of_str "FStarC.Syntax.Embeddings.Base.embedding" in
    FStarC_Syntax_Syntax.fvar uu___1 FStar_Pervasives_Native.None in
  FStarC_Syntax_Util.mk_app uu___ [FStarC_Syntax_Syntax.as_arg t]
let rec subst_expr (x : Prims.string) (v : FStarC_Custard_Syntax.expr)
  (e : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let go = subst_expr x v in
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar y when y = x -> v
  | FStarC_Custard_Syntax.ELet (y, t, e1, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 = go e1 in
          let uu___3 = if y = x then e2 else go e2 in (y, t, uu___2, uu___3) in
        FStarC_Custard_Syntax.ELet uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (e.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (e.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EFun (bs, b) ->
      let shadows =
        FStarC_List.existsb (fun b1 -> b1.FStarC_Custard_Syntax.b_name = x)
          bs in
      let uu___ =
        let uu___1 = let uu___2 = if shadows then b else go b in (bs, uu___2) in
        FStarC_Custard_Syntax.EFun uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (e.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (e.FStarC_Custard_Syntax.eff)
      }
  | uu___ -> FStarC_Custard_Syntax.map_children go e
let compile (st : FStarC_Custard_Extract.state)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Custard_Syntax.expr=
  let free = FStarC_Syntax_Free.names t in
  let used =
    let uu___ = FStarC_Effect.op_Bang generated in
    FStarC_List.filter
      (fun g ->
         FStarC_Class_Setlike.mem
           (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv)
           g.ge_ph free) uu___ in
  match used with
  | [] -> FStarC_Custard_Extract.expr_of_term st t
  | uu___ ->
      let e = FStarC_Custard_Extract.expr_of_term st t in
      FStarC_List.fold_left
        (fun e1 g ->
           let ety =
             FStarC_Custard_Extract.ty_of_typ st
               (g.ge_ph).FStarC_Syntax_Syntax.sort in
           let v =
             let uu___1 =
               let uu___2 = FStarC_Effect.op_Bang building in
               FStarC_List.existsb (FStarC_Ident.lid_equals g.ge_lid) uu___2 in
             if uu___1
             then
               FStarC_Custard_Syntax.mk
                 (FStarC_Custard_Syntax.EApp
                    ((FStarC_Custard_Syntax.mk
                        (FStarC_Custard_Syntax.EQual ((g.ge_knot), []))
                        (FStarC_Custard_Syntax.TArrow
                           (FStarC_Custard_Syntax.TUnit,
                             FStarC_Custard_Syntax.E_Impure, ety))
                        FStarC_Custard_Syntax.E_Pure),
                      [FStarC_Custard_Syntax.mk
                         (FStarC_Custard_Syntax.EConst
                            FStarC_Custard_Syntax.CUnit)
                         FStarC_Custard_Syntax.TUnit
                         FStarC_Custard_Syntax.E_Pure])) ety
                 FStarC_Custard_Syntax.E_Impure
             else
               FStarC_Custard_Syntax.mk
                 (FStarC_Custard_Syntax.EQual ((g.ge_emb), [])) ety
                 FStarC_Custard_Syntax.E_Impure in
           let uu___1 =
             FStarC_Custard_Syntax.uniq
               (FStarC_Ident.string_of_id
                  (g.ge_ph).FStarC_Syntax_Syntax.ppname)
               (g.ge_ph).FStarC_Syntax_Syntax.index in
           subst_expr uu___1 v e1) e used
let dummy : FStarC_Range_Type.t= FStarC_Range_Type.dummyRange
let ctor_fv (l : FStarC_Ident.lident) : FStarC_Syntax_Syntax.fv=
  FStarC_Syntax_Syntax.lid_and_dd_as_fv l
    (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor)
let pat_of (v : FStarC_Syntax_Syntax.pat') : FStarC_Syntax_Syntax.pat=
  FStarC_Syntax_Syntax.withinfo v dummy
let dot_pat : FStarC_Syntax_Syntax.pat=
  pat_of (FStarC_Syntax_Syntax.Pat_dot_term FStar_Pervasives_Native.None)
let rec term_list (ty : FStarC_Syntax_Syntax.typ)
  (es : FStarC_Syntax_Syntax.term Prims.list) : FStarC_Syntax_Syntax.term=
  match es with
  | [] ->
      let uu___ =
        FStarC_Syntax_Syntax.tdataconstr FStarC_Parser_Const.nil_lid in
      FStarC_Syntax_Util.mk_app uu___ [FStarC_Syntax_Syntax.iarg ty]
  | e::es1 ->
      let uu___ =
        FStarC_Syntax_Syntax.tdataconstr FStarC_Parser_Const.cons_lid in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = term_list ty es1 in
              FStarC_Syntax_Syntax.as_arg uu___5 in
            [uu___4] in
          (FStarC_Syntax_Syntax.as_arg e) :: uu___3 in
        (FStarC_Syntax_Syntax.iarg ty) :: uu___2 in
      FStarC_Syntax_Util.mk_app uu___ uu___1
let rec list_pat (vs : FStarC_Syntax_Syntax.bv Prims.list) :
  FStarC_Syntax_Syntax.pat=
  match vs with
  | [] ->
      let uu___ =
        let uu___1 =
          let uu___2 = ctor_fv FStarC_Parser_Const.nil_lid in
          (uu___2, FStar_Pervasives_Native.None, [(dot_pat, true)]) in
        FStarC_Syntax_Syntax.Pat_cons uu___1 in
      pat_of uu___
  | v::vs1 ->
      let uu___ =
        let uu___1 =
          let uu___2 = ctor_fv FStarC_Parser_Const.cons_lid in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = let uu___7 = list_pat vs1 in (uu___7, false) in
                [uu___6] in
              ((pat_of (FStarC_Syntax_Syntax.Pat_var v)), false) :: uu___5 in
            (dot_pat, true) :: uu___4 in
          (uu___2, FStar_Pervasives_Native.None, uu___3) in
        FStarC_Syntax_Syntax.Pat_cons uu___1 in
      pat_of uu___
let lid (s : Prims.string) : FStarC_Ident.lident= FStarC_Ident.lid_of_str s
let str (s : Prims.string) : FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_constant
       (FStarC_Const.Const_string (s, FStarC_Range_Type.dummyRange)))
    FStarC_Range_Type.dummyRange
let call (f : FStarC_Ident.lident)
  (tys : FStarC_Syntax_Syntax.term Prims.list)
  (args : FStarC_Syntax_Syntax.term Prims.list) : FStarC_Syntax_Syntax.term=
  let uu___ = FStarC_Syntax_Syntax.fvar f FStar_Pervasives_Native.None in
  let uu___1 =
    let uu___2 = FStarC_List.map FStarC_Syntax_Syntax.iarg tys in
    let uu___3 = FStarC_List.map FStarC_Syntax_Syntax.as_arg args in
    FStarC_List.op_At uu___2 uu___3 in
  FStarC_Syntax_Util.mk_app uu___ uu___1
let signature_of (st : FStarC_Custard_Extract.state)
  (f : FStarC_Ident.lident) (tys : FStarC_Syntax_Syntax.term Prims.list) :
  (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.typ)=
  FStarC_Custard_Extract.ensure_lid_available st f;
  (let uu___1 =
     let uu___2 = FStarC_Custard_Extract.tcenv st in
     FStarC_TypeChecker_Env.try_lookup_lid uu___2 f in
   match uu___1 with
   | FStar_Pervasives_Native.None ->
       FStarC_Effect.raise
         (NoEmbedding
            (Prims.strcat "no declaration for "
               (FStarC_Ident.string_of_lid f)))
   | FStar_Pervasives_Native.Some ((uu___2, ty), uu___3) ->
       let uu___4 = FStarC_Syntax_Util.arrow_formals_comp ty in
       (match uu___4 with
        | (bs, c) ->
            let n = FStarC_List.length tys in
            (if (FStarC_List.length bs) < n
             then
               FStarC_Effect.raise
                 (NoEmbedding
                    (Prims.strcat (FStarC_Ident.string_of_lid f)
                       " has too few binders"))
             else ();
             (let uu___6 = FStarC_List.splitAt n bs in
              match uu___6 with
              | (imps, rest) ->
                  (FStarC_List.iter2
                     (fun b uu___8 ->
                        if
                          match b.FStarC_Syntax_Syntax.binder_qual with
                          | FStar_Pervasives_Native.None -> true
                          | uu___9 -> false
                        then
                          FStarC_Effect.raise
                            (NoEmbedding
                               (Prims.strcat (FStarC_Ident.string_of_lid f)
                                  " does not begin with implicit binders"))
                        else ()) imps tys;
                   (let s =
                      FStarC_List.map2
                        (fun b t ->
                           FStarC_Syntax_Syntax.NT
                             ((b.FStarC_Syntax_Syntax.binder_bv), t)) imps
                        tys in
                    let uu___8 = FStarC_Syntax_Subst.subst_binders s rest in
                    let uu___9 =
                      FStarC_Syntax_Subst.subst s
                        (FStarC_Syntax_Util.comp_result c) in
                    (uu___8, uu___9)))))))
let last_binders (n : Prims.int)
  (bs : FStarC_Syntax_Syntax.binder Prims.list) :
  FStarC_Syntax_Syntax.binder Prims.list=
  let k = FStarC_List.length bs in
  if k < n
  then
    FStarC_Effect.raise
      (NoEmbedding "interpretation function has too few binders")
  else ();
  FStar_Pervasives_Native.snd (FStarC_List.splitAt (k - n) bs)
let fresh_bvs (bs : FStarC_Syntax_Syntax.binder Prims.list) :
  FStarC_Syntax_Syntax.bv Prims.list=
  FStarC_List.map
    (fun b ->
       FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
         (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort) bs
type kind =
  | SyntaxTerm 
  | NBETerm 
let uu___is_SyntaxTerm (projectee : kind) : Prims.bool=
  match projectee with | SyntaxTerm -> true | uu___ -> false
let uu___is_NBETerm (projectee : kind) : Prims.bool=
  match projectee with | NBETerm -> true | uu___ -> false
let nbe_unsupported (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.term=
  let uu___ = lid "FStarC.TypeChecker.NBETerm.e_unsupported" in
  call uu___ [t] []
let whnf (st : FStarC_Custard_Extract.state) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ=
  let head_lid t1 =
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Util.head_and_args_full t1 in
            FStar_Pervasives_Native.fst uu___4 in
          FStarC_Syntax_Util.un_uinst uu___3 in
        FStarC_Syntax_Subst.compress uu___2 in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.lid_of_fv fv)
    | uu___1 -> FStar_Pervasives_Native.None in
  let rec go fuel t1 =
    let uu___ = head_lid t1 in
    match uu___ with
    | FStar_Pervasives_Native.None -> t1
    | FStar_Pervasives_Native.Some l when
        let uu___1 = find_embedding l in
        match uu___1 with
        | FStar_Pervasives_Native.Some v -> true
        | uu___2 -> false -> t1
    | FStar_Pervasives_Native.Some l ->
        (FStarC_Custard_Extract.ensure_lid_available st l;
         (let t' =
            let uu___2 = FStarC_Custard_Extract.tcenv st in
            FStarC_Custard_Mono.norm_bounded uu___2 "an embedded type"
              [FStarC_TypeChecker_Env.Primops;
              FStarC_TypeChecker_Env.Weak;
              FStarC_TypeChecker_Env.HNF;
              FStarC_TypeChecker_Env.UnfoldUntil
                FStarC_Syntax_Syntax.delta_constant;
              FStarC_TypeChecker_Env.Beta] t1 in
          let t'1 =
            let uu___2 = FStarC_Syntax_Util.un_uinst t' in
            FStarC_Syntax_Subst.compress uu___2 in
          if fuel <= Prims.int_zero
          then t'1
          else
            (let uu___2 = head_lid t'1 in
             match uu___2 with
             | FStar_Pervasives_Native.Some l' when
                 FStarC_Ident.lid_equals l l' -> t'1
             | uu___3 -> go (fuel - Prims.int_one) t'1))) in
  let uu___ =
    let uu___1 = FStarC_Syntax_Util.un_uinst t in
    FStarC_Syntax_Subst.compress uu___1 in
  go (Prims.of_int 20) uu___
type tvenv = (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.bv) Prims.list
let find_tv (env : tvenv) (b : FStarC_Syntax_Syntax.bv) :
  FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 ->
         match uu___1 with | (a, uu___2) -> FStarC_Syntax_Syntax.bv_eq a b)
      env in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, v) ->
      FStar_Pervasives_Native.Some v
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec embedding_for (st : FStarC_Custard_Extract.state) (k : kind)
  (env : tvenv) (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.term=
  let t1 = whnf st t in
  match t1.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b2 = x; FStarC_Syntax_Syntax.phi = uu___;_} ->
      embedding_for st k env x.FStarC_Syntax_Syntax.sort
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = t2; FStarC_Syntax_Syntax.asc = uu___;
        FStarC_Syntax_Syntax.eff_opt = uu___1;_}
      -> embedding_for st k env t2
  | FStarC_Syntax_Syntax.Tm_name bv when
      let uu___ = find_tv env bv in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let v =
        let uu___ = find_tv env bv in
        match uu___ with | FStar_Pervasives_Native.Some v1 -> v1 in
      let comb =
        match k with
        | SyntaxTerm -> lid "FStarC.Syntax.Embeddings.mk_any_emb"
        | NBETerm -> lid "FStarC.TypeChecker.NBETerm.mk_any_emb" in
      let uu___ = let uu___1 = FStarC_Syntax_Syntax.bv_to_name v in [uu___1] in
      call comb [] uu___
  | FStarC_Syntax_Syntax.Tm_arrow uu___ when
      let uu___1 = FStarC_Syntax_Util.arrow_one_ln t1 in
      match uu___1 with
      | FStar_Pervasives_Native.Some (uu___2, c) ->
          FStarC_Syntax_Util.is_pure_comp c
      | FStar_Pervasives_Native.None -> false ->
      let uu___1 =
        let uu___2 = FStarC_Syntax_Util.arrow_one t1 in
        match uu___2 with | FStar_Pervasives_Native.Some v -> v in
      (match uu___1 with
       | (b, c) ->
           let t0 =
             (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
           let t11 = FStarC_Syntax_Util.comp_result c in
           let comb =
             match k with
             | SyntaxTerm -> lid "FStarC.Syntax.Embeddings.e_arrow"
             | NBETerm -> lid "FStarC.TypeChecker.NBETerm.e_arrow" in
           let uu___2 =
             let uu___3 = embedding_for st k env t0 in
             let uu___4 = let uu___5 = embedding_for st k env t11 in [uu___5] in
             uu___3 :: uu___4 in
           call comb [t0; t11] uu___2)
  | FStarC_Syntax_Syntax.Tm_app uu___ ->
      let uu___1 = FStarC_Syntax_Util.head_and_args_full t1 in
      (match uu___1 with
       | (head, args) ->
           let tys = FStarC_List.map FStar_Pervasives_Native.fst args in
           let uu___2 = embedding_head st k head in
           (match uu___2 with
            | FStar_Pervasives_Native.Some f ->
                let uu___3 = FStarC_List.map (embedding_for st k env) tys in
                call f tys uu___3
            | FStar_Pervasives_Native.None ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t1 in
                    Prims.strcat "no embedding for " uu___5 in
                  NoEmbedding uu___4 in
                FStarC_Effect.raise uu___3))
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      let uu___ = embedding_head st k t1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some f -> call f [] []
       | FStar_Pervasives_Native.None ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Custard_Extract.tcenv st in
               FStarC_TypeChecker_Env.fv_has_attr uu___3 fv
                 FStarC_Parser_Const.plugin_attr in
             Prims.not uu___2 in
           if uu___1
           then
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t1 in
                 Prims.strcat "no embedding for " uu___4 in
               NoEmbedding uu___3 in
             FStarC_Effect.raise uu___2
           else
             (match k with
              | NBETerm -> nbe_unsupported t1
              | SyntaxTerm ->
                  let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                  (ensure_generated st l;
                   (let uu___3 = find_generated l in
                    match uu___3 with
                    | FStar_Pervasives_Native.Some g ->
                        FStarC_Syntax_Syntax.bv_to_name g.ge_ph
                    | FStar_Pervasives_Native.None ->
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term t1 in
                            Prims.strcat "no embedding for " uu___6 in
                          NoEmbedding uu___5 in
                        FStarC_Effect.raise uu___4))))
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
          Prims.strcat "cannot embed type " uu___3 in
        NoEmbedding uu___2 in
      FStarC_Effect.raise uu___1
and embedding_head (st : FStarC_Custard_Extract.state) (k : kind)
  (t : FStarC_Syntax_Syntax.term) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.un_uinst t in
      FStarC_Syntax_Subst.compress uu___2 in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      let l = FStarC_Syntax_Syntax.lid_of_fv fv in
      let uu___1 = find_embedding l in
      (match uu___1 with
       | FStar_Pervasives_Native.Some d ->
           (match k with
            | SyntaxTerm -> FStar_Pervasives_Native.Some (d.syn_emb)
            | NBETerm -> d.nbe_emb)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___1 -> FStar_Pervasives_Native.None
and ensure_generated (st : FStarC_Custard_Extract.state)
  (l : FStarC_Ident.lident) : unit=
  let uu___ =
    let uu___1 = find_generated l in
    match uu___1 with
    | FStar_Pervasives_Native.Some v -> true
    | uu___2 -> false in
  if uu___
  then ()
  else
    (let uu___1 =
       let uu___2 = FStarC_Custard_Extract.tcenv st in
       FStarC_TypeChecker_Env.lookup_sigelt uu___2 l in
     match uu___1 with
     | FStar_Pervasives_Native.Some
         {
           FStarC_Syntax_Syntax.sigel =
             FStarC_Syntax_Syntax.Sig_inductive_typ
             { FStarC_Syntax_Syntax.lid = uu___2;
               FStarC_Syntax_Syntax.us = uu___3;
               FStarC_Syntax_Syntax.params = params;
               FStarC_Syntax_Syntax.num_uniform_params = uu___4;
               FStarC_Syntax_Syntax.t = uu___5;
               FStarC_Syntax_Syntax.mutuals = mutuals;
               FStarC_Syntax_Syntax.ds = uu___6;
               FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
           FStarC_Syntax_Syntax.sigrng = uu___8;
           FStarC_Syntax_Syntax.sigquals = uu___9;
           FStarC_Syntax_Syntax.sigmeta = uu___10;
           FStarC_Syntax_Syntax.sigattrs = uu___11;
           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
           FStarC_Syntax_Syntax.sigopts = uu___13;_}
         ->
         (if (match params with | hd::tl -> true | uu___15 -> false)
          then
            FStarC_Effect.raise
              (NoEmbedding
                 (Prims.strcat "cannot generate an embedding for "
                    (Prims.strcat (FStarC_Ident.string_of_lid l)
                       ": the inductive has parameters")))
          else ();
          (let group =
             let uu___15 =
               FStarC_List.filter
                 (fun m -> Prims.not (FStarC_Ident.lid_equals m l)) mutuals in
             l :: uu___15 in
           let entries =
             FStarC_List.map
               (fun g ->
                  let nm = FStarC_Custard_Extract.name_of_lid g in
                  let e =
                    let uu___15 =
                      let uu___16 =
                        let uu___17 =
                          FStarC_Syntax_Syntax.fvar g
                            FStar_Pervasives_Native.None in
                        embedding_typ uu___17 in
                      FStarC_Syntax_Syntax.new_bv
                        FStar_Pervasives_Native.None uu___16 in
                    {
                      ge_lid = g;
                      ge_ph = uu___15;
                      ge_emb =
                        {
                          FStarC_Custard_Syntax.ns =
                            (nm.FStarC_Custard_Syntax.ns);
                          FStarC_Custard_Syntax.id =
                            (Prims.strcat "e_" nm.FStarC_Custard_Syntax.id);
                          FStarC_Custard_Syntax.spec =
                            (nm.FStarC_Custard_Syntax.spec)
                        };
                      ge_knot =
                        {
                          FStarC_Custard_Syntax.ns =
                            (nm.FStarC_Custard_Syntax.ns);
                          FStarC_Custard_Syntax.id =
                            (Prims.strcat "__knot_e_"
                               nm.FStarC_Custard_Syntax.id);
                          FStarC_Custard_Syntax.spec =
                            (nm.FStarC_Custard_Syntax.spec)
                        }
                    } in
                  (let uu___16 =
                     let uu___17 = FStarC_Effect.op_Bang generated in e ::
                       uu___17 in
                   FStarC_Effect.op_Colon_Equals generated uu___16);
                  e) group in
           let saved = FStarC_Effect.op_Bang building in
           FStarC_Effect.op_Colon_Equals building
             (FStarC_List.op_At group saved);
           FStarC_List.iter (generate_one st) entries;
           FStarC_Effect.op_Colon_Equals building saved))
     | uu___2 ->
         FStarC_Effect.raise
           (NoEmbedding
              (Prims.strcat "no inductive declaration for "
                 (FStarC_Ident.string_of_lid l))))
and generate_one (st : FStarC_Custard_Extract.state) (g : gen_emb) : 
  unit=
  let env = FStarC_Custard_Extract.tcenv st in
  let gty = FStarC_Syntax_Syntax.fvar g.ge_lid FStar_Pervasives_Native.None in
  let uu___ = FStarC_TypeChecker_Env.datacons_of_typ env g.ge_lid in
  match uu___ with
  | (uu___1, cs) ->
      let ctors =
        FStarC_List.map
          (fun c ->
             let uu___2 = FStarC_TypeChecker_Env.lookup_sigelt env c in
             match uu___2 with
             | FStar_Pervasives_Native.Some
                 {
                   FStarC_Syntax_Syntax.sigel =
                     FStarC_Syntax_Syntax.Sig_datacon
                     { FStarC_Syntax_Syntax.lid1 = uu___3;
                       FStarC_Syntax_Syntax.us1 = uu___4;
                       FStarC_Syntax_Syntax.t1 = t;
                       FStarC_Syntax_Syntax.ty_lid = uu___5;
                       FStarC_Syntax_Syntax.num_ty_params = uu___6;
                       FStarC_Syntax_Syntax.mutuals1 = uu___7;
                       FStarC_Syntax_Syntax.injective_type_params1 = uu___8;
                       FStarC_Syntax_Syntax.proj_disc_lids = uu___9;_};
                   FStarC_Syntax_Syntax.sigrng = uu___10;
                   FStarC_Syntax_Syntax.sigquals = uu___11;
                   FStarC_Syntax_Syntax.sigmeta = uu___12;
                   FStarC_Syntax_Syntax.sigattrs = uu___13;
                   FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___14;
                   FStarC_Syntax_Syntax.sigopts = uu___15;_}
                 ->
                 let uu___16 =
                   let uu___17 = FStarC_Syntax_Util.arrow_formals t in
                   FStar_Pervasives_Native.fst uu___17 in
                 (c, uu___16)
             | uu___3 ->
                 FStarC_Effect.raise
                   (NoEmbedding
                      (Prims.strcat "no declaration for constructor "
                         (FStarC_Ident.string_of_lid c)))) cs in
      let body =
        let uu___2 =
          let uu___3 = emb_base "mk_extracted_embedding" in
          let uu___4 =
            let uu___5 = str (FStarC_Ident.string_of_lid g.ge_lid) in
            let uu___6 =
              let uu___7 = unembed_fun st gty ctors in
              let uu___8 = let uu___9 = embed_fun st gty ctors in [uu___9] in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          call uu___3 [gty] uu___4 in
        compile st uu___2 in
      let ety =
        let uu___2 = embedding_typ gty in
        FStarC_Custard_Extract.ty_of_typ st uu___2 in
      (FStarC_Custard_Extract.emit st
         (Prims.strcat "regemb-knot:" (FStarC_Ident.string_of_lid g.ge_lid))
         (FStarC_Custard_Syntax.DLet
            {
              FStarC_Custard_Syntax.dl_name = (g.ge_knot);
              FStarC_Custard_Syntax.dl_typars = [];
              FStarC_Custard_Syntax.dl_binders =
                [{
                   FStarC_Custard_Syntax.b_name = "_thunk";
                   FStarC_Custard_Syntax.b_ty = FStarC_Custard_Syntax.TUnit
                 }];
              FStarC_Custard_Syntax.dl_ret = ety;
              FStarC_Custard_Syntax.dl_eff = FStarC_Custard_Syntax.E_Impure;
              FStarC_Custard_Syntax.dl_body = body;
              FStarC_Custard_Syntax.dl_flags =
                [FStarC_Custard_Syntax.Comment
                   (Prims.strcat "Embedding for "
                      (FStarC_Ident.string_of_lid g.ge_lid))]
            });
       FStarC_Custard_Extract.emit st
         (Prims.strcat "regemb-emb:" (FStarC_Ident.string_of_lid g.ge_lid))
         (FStarC_Custard_Syntax.DLet
            {
              FStarC_Custard_Syntax.dl_name = (g.ge_emb);
              FStarC_Custard_Syntax.dl_typars = [];
              FStarC_Custard_Syntax.dl_binders = [];
              FStarC_Custard_Syntax.dl_ret = ety;
              FStarC_Custard_Syntax.dl_eff = FStarC_Custard_Syntax.E_Impure;
              FStarC_Custard_Syntax.dl_body =
                (FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EApp
                      ((FStarC_Custard_Syntax.mk
                          (FStarC_Custard_Syntax.EQual ((g.ge_knot), []))
                          (FStarC_Custard_Syntax.TArrow
                             (FStarC_Custard_Syntax.TUnit,
                               FStarC_Custard_Syntax.E_Impure, ety))
                          FStarC_Custard_Syntax.E_Pure),
                        [FStarC_Custard_Syntax.mk
                           (FStarC_Custard_Syntax.EConst
                              FStarC_Custard_Syntax.CUnit)
                           FStarC_Custard_Syntax.TUnit
                           FStarC_Custard_Syntax.E_Pure])) ety
                   FStarC_Custard_Syntax.E_Impure);
              FStarC_Custard_Syntax.dl_flags = []
            }))
and embed_fun (st : FStarC_Custard_Extract.state)
  (gty : FStarC_Syntax_Syntax.typ)
  (ctors :
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.binder Prims.list) Prims.list)
  : FStarC_Syntax_Syntax.term=
  let x = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None gty in
  let arg_ty =
    let uu___ = FStarC_Ident.lid_of_str "FStarC.Syntax.Syntax.arg" in
    FStarC_Syntax_Syntax.fvar uu___ FStar_Pervasives_Native.None in
  let brs =
    FStarC_List.map
      (fun uu___ ->
         match uu___ with
         | (c, bs) ->
             let vs =
               FStarC_List.map
                 (fun b ->
                    FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                 bs in
             let p =
               let uu___1 =
                 let uu___2 =
                   let uu___3 = ctor_fv c in
                   let uu___4 =
                     FStarC_List.map2
                       (fun b v ->
                          ((pat_of (FStarC_Syntax_Syntax.Pat_var v)),
                            (match b.FStarC_Syntax_Syntax.binder_qual with
                             | FStar_Pervasives_Native.Some v1 -> true
                             | uu___5 -> false))) bs vs in
                   (uu___3, FStar_Pervasives_Native.None, uu___4) in
                 FStarC_Syntax_Syntax.Pat_cons uu___2 in
               pat_of uu___1 in
             let args =
               FStarC_List.map2
                 (fun b v ->
                    let uu___1 =
                      FStarC_Ident.lid_of_str "FStarC.Syntax.Syntax.as_arg" in
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = emb_base "extracted_embed" in
                        let uu___5 =
                          let uu___6 =
                            embedding_for st SyntaxTerm []
                              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                          let uu___7 =
                            let uu___8 = FStarC_Syntax_Syntax.bv_to_name v in
                            [uu___8] in
                          uu___6 :: uu___7 in
                        call uu___4
                          [(b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort]
                          uu___5 in
                      [uu___3] in
                    call uu___1 [] uu___2) bs vs in
             let head =
               let uu___1 =
                 FStarC_Ident.lid_of_str "FStarC.Syntax.Syntax.tdataconstr" in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Ident.lid_of_str "FStarC.Ident.lid_of_str" in
                   let uu___5 =
                     let uu___6 = str (FStarC_Ident.string_of_lid c) in
                     [uu___6] in
                   call uu___4 [] uu___5 in
                 [uu___3] in
               call uu___1 [] uu___2 in
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   FStarC_Ident.lid_of_str "FStarC.Syntax.Util.mk_app" in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = term_list arg_ty args in [uu___6] in
                   head :: uu___5 in
                 call uu___3 [] uu___4 in
               (p, FStar_Pervasives_Native.None, uu___2) in
             FStarC_Syntax_Subst.close_branch uu___1) ctors in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Syntax_Syntax.bv_to_name x in
        {
          FStarC_Syntax_Syntax.scrutinee = uu___3;
          FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
          FStarC_Syntax_Syntax.brs = brs;
          FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
        } in
      FStarC_Syntax_Syntax.Tm_match uu___2 in
    FStarC_Syntax_Syntax.mk uu___1 dummy in
  FStarC_Syntax_Util.abs [FStarC_Syntax_Syntax.mk_binder x] uu___
    FStar_Pervasives_Native.None
and unembed_fun (st : FStarC_Custard_Extract.state)
  (gty : FStarC_Syntax_Syntax.typ)
  (ctors :
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.binder Prims.list) Prims.list)
  : FStarC_Syntax_Syntax.term=
  let t_term =
    let uu___ = FStarC_Ident.lid_of_str "FStarC.Syntax.Syntax.term" in
    FStarC_Syntax_Syntax.fvar uu___ FStar_Pervasives_Native.None in
  let t_terms =
    let uu___ =
      FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.list_lid
        FStar_Pervasives_Native.None in
    FStarC_Syntax_Util.mk_app uu___ [FStarC_Syntax_Syntax.as_arg t_term] in
  let scrut_ty =
    let uu___ =
      let uu___1 =
        FStarC_Parser_Const_Tuples.mk_tuple_lid (Prims.of_int 2) dummy in
      FStarC_Syntax_Syntax.fvar uu___1 FStar_Pervasives_Native.None in
    FStarC_Syntax_Util.mk_app uu___
      [FStarC_Syntax_Syntax.as_arg FStarC_Syntax_Syntax.t_string;
      FStarC_Syntax_Syntax.as_arg t_terms] in
  let tm = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None scrut_ty in
  let none =
    let uu___ = FStarC_Syntax_Syntax.tdataconstr FStarC_Parser_Const.none_lid in
    FStarC_Syntax_Util.mk_app uu___ [FStarC_Syntax_Syntax.iarg gty] in
  let brs =
    FStarC_List.map
      (fun uu___ ->
         match uu___ with
         | (c, bs) ->
             let ps =
               FStarC_List.map
                 (fun uu___1 ->
                    FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t_term) bs in
             let vs =
               FStarC_List.map
                 (fun b ->
                    FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                 bs in
             let p =
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       FStarC_Ident.lid_of_str
                         "FStar.Pervasives.Native.Mktuple2" in
                     ctor_fv uu___4 in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = list_pat ps in (uu___9, false) in
                           [uu___8] in
                         ((pat_of
                             (FStarC_Syntax_Syntax.Pat_constant
                                (FStarC_Const.Const_string
                                   ((FStarC_Ident.string_of_lid c), dummy)))),
                           false) :: uu___7 in
                       (dot_pat, true) :: uu___6 in
                     (dot_pat, true) :: uu___5 in
                   (uu___3, FStar_Pervasives_Native.None, uu___4) in
                 FStarC_Syntax_Syntax.Pat_cons uu___2 in
               pat_of uu___1 in
             let ret =
               let uu___1 =
                 FStarC_Syntax_Syntax.tdataconstr
                   FStarC_Parser_Const.some_lid in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Syntax.tdataconstr c in
                       let uu___7 =
                         FStarC_List.map2
                           (fun b v ->
                              let uu___8 = FStarC_Syntax_Syntax.bv_to_name v in
                              (uu___8,
                                (FStarC_Syntax_Util.aqual_of_binder b))) bs
                           vs in
                       FStarC_Syntax_Util.mk_app uu___6 uu___7 in
                     FStarC_Syntax_Syntax.as_arg uu___5 in
                   [uu___4] in
                 (FStarC_Syntax_Syntax.iarg gty) :: uu___3 in
               FStarC_Syntax_Util.mk_app uu___1 uu___2 in
             let steps =
               let uu___1 = FStarC_List.map2 (fun a b -> (a, b)) ps vs in
               FStarC_List.map2
                 (fun b uu___2 -> match uu___2 with | (pv, v) -> (b, pv, v))
                 bs uu___1 in
             let body =
               FStarC_List.fold_right
                 (fun uu___1 acc ->
                    match uu___1 with
                    | (b, pv, v) ->
                        let uu___2 =
                          FStarC_Ident.lid_of_str "FStarC.Option.bind" in
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = emb_base "extracted_unembed" in
                            let uu___6 =
                              let uu___7 =
                                embedding_for st SyntaxTerm []
                                  (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                              let uu___8 =
                                let uu___9 =
                                  FStarC_Syntax_Syntax.bv_to_name pv in
                                [uu___9] in
                              uu___7 :: uu___8 in
                            call uu___5
                              [(b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort]
                              uu___6 in
                          let uu___5 =
                            let uu___6 =
                              FStarC_Syntax_Util.abs
                                [FStarC_Syntax_Syntax.mk_binder v] acc
                                FStar_Pervasives_Native.None in
                            [uu___6] in
                          uu___4 :: uu___5 in
                        call uu___2
                          [(b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort;
                          gty] uu___3) steps ret in
             FStarC_Syntax_Subst.close_branch
               (p, FStar_Pervasives_Native.None, body)) ctors in
  let catchall =
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None scrut_ty in
          FStarC_Syntax_Syntax.Pat_var uu___3 in
        pat_of uu___2 in
      (uu___1, FStar_Pervasives_Native.None, none) in
    FStarC_Syntax_Subst.close_branch uu___ in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Syntax_Syntax.bv_to_name tm in
        {
          FStarC_Syntax_Syntax.scrutinee = uu___3;
          FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
          FStarC_Syntax_Syntax.brs = (FStarC_List.op_At brs [catchall]);
          FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
        } in
      FStarC_Syntax_Syntax.Tm_match uu___2 in
    FStarC_Syntax_Syntax.mk uu___1 dummy in
  FStarC_Syntax_Util.abs [FStarC_Syntax_Syntax.mk_binder tm] uu___
    FStar_Pervasives_Native.None
let native_lid (s : Prims.string) : FStarC_Custard_Syntax.name=
  {
    FStarC_Custard_Syntax.ns = ["FStarC"; "Tactics"; "Native"];
    FStarC_Custard_Syntax.id = s;
    FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
  }
let register_fn (st : FStarC_Custard_Extract.state) (which : Prims.string)
  (ty : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.name=
  let nm = native_lid which in
  FStarC_Custard_Extract.emit st (Prims.strcat "regemb-extern:" which)
    (FStarC_Custard_Syntax.DExternal
       {
         FStarC_Custard_Syntax.dx_name = nm;
         FStarC_Custard_Syntax.dx_typars = [];
         FStarC_Custard_Syntax.dx_ty = ty;
         FStarC_Custard_Syntax.dx_target = FStar_Pervasives_Native.None;
         FStarC_Custard_Syntax.dx_header = FStar_Pervasives_Native.None;
         FStarC_Custard_Syntax.dx_flags = []
       });
  nm
let ir_call (f : FStarC_Custard_Syntax.name)
  (fty : FStarC_Custard_Syntax.cty)
  (args : FStarC_Custard_Syntax.expr Prims.list) :
  FStarC_Custard_Syntax.expr=
  let rec res t n =
    if n <= Prims.int_zero
    then t
    else
      (match t with
       | FStarC_Custard_Syntax.TArrow (uu___, uu___1, t1) ->
           res t1 (n - Prims.int_one)
       | uu___ -> FStarC_Custard_Syntax.TAny) in
  let uu___ = res fty (FStarC_List.length args) in
  FStarC_Custard_Syntax.mk
    (FStarC_Custard_Syntax.EApp
       ((FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EQual (f, [])) fty
           FStarC_Custard_Syntax.E_Pure), args)) uu___
    FStarC_Custard_Syntax.E_Impure
let arg_typ (k : kind) : FStarC_Syntax_Syntax.typ=
  match k with
  | SyntaxTerm ->
      let uu___ = lid "FStarC.Syntax.Syntax.term" in
      FStarC_Syntax_Syntax.fvar uu___ FStar_Pervasives_Native.None
  | NBETerm ->
      let uu___ = lid "FStarC.TypeChecker.NBETerm.t" in
      FStarC_Syntax_Syntax.fvar uu___ FStar_Pervasives_Native.None
let peel_type_args (st : FStarC_Custard_Extract.state)
  (args_bv : FStarC_Syntax_Syntax.bv)
  (tvs : FStarC_Syntax_Syntax.bv Prims.list) (rest : FStarC_Syntax_Syntax.bv)
  (res_ty : FStarC_Syntax_Syntax.typ) (body : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  let rec go tvs1 =
    match tvs1 with
    | [] -> pat_of (FStarC_Syntax_Syntax.Pat_var rest)
    | v::tvs2 ->
        let arg =
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = lid "FStar.Pervasives.Native.Mktuple2" in
                ctor_fv uu___3 in
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              FStarC_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStarC_Syntax_Syntax.tun in
                            FStarC_Syntax_Syntax.Pat_var uu___10 in
                          pat_of uu___9 in
                        (uu___8, false) in
                      [uu___7] in
                    ((pat_of (FStarC_Syntax_Syntax.Pat_var v)), false) ::
                      uu___6 in
                  (dot_pat, true) :: uu___5 in
                (dot_pat, true) :: uu___4 in
              (uu___2, FStar_Pervasives_Native.None, uu___3) in
            FStarC_Syntax_Syntax.Pat_cons uu___1 in
          pat_of uu___ in
        let uu___ =
          let uu___1 =
            let uu___2 = ctor_fv FStarC_Parser_Const.cons_lid in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 = let uu___7 = go tvs2 in (uu___7, false) in
                  [uu___6] in
                (arg, false) :: uu___5 in
              (dot_pat, true) :: uu___4 in
            (uu___2, FStar_Pervasives_Native.None, uu___3) in
          FStarC_Syntax_Syntax.Pat_cons uu___1 in
        pat_of uu___ in
  let fail =
    let uu___ = lid "FStarC.Effect.failwith" in
    let uu___1 =
      let uu___2 = str "Custard: a plugin was applied to too few arguments" in
      [uu___2] in
    call uu___ [res_ty] uu___1 in
  let catchall =
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              args_bv.FStarC_Syntax_Syntax.sort in
          FStarC_Syntax_Syntax.Pat_var uu___3 in
        pat_of uu___2 in
      (uu___1, FStar_Pervasives_Native.None, fail) in
    FStarC_Syntax_Subst.close_branch uu___ in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Syntax.bv_to_name args_bv in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 = go tvs in
            (uu___6, FStar_Pervasives_Native.None, body) in
          FStarC_Syntax_Subst.close_branch uu___5 in
        [uu___4; catchall] in
      {
        FStarC_Syntax_Syntax.scrutinee = uu___2;
        FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
        FStarC_Syntax_Syntax.brs = uu___3;
        FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
      } in
    FStarC_Syntax_Syntax.Tm_match uu___1 in
  FStarC_Syntax_Syntax.mk uu___ dummy
let interp_term (st : FStarC_Custard_Extract.state) (k : kind)
  (tac : Prims.bool) (fv_lid : FStarC_Ident.lident) (n : Prims.int)
  (tvs : FStarC_Syntax_Syntax.binder Prims.list)
  (bs : FStarC_Syntax_Syntax.binder Prims.list)
  (res : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.term=
  let env =
    FStarC_List.map
      (fun b ->
         let uu___ =
           let uu___1 = arg_typ k in
           FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu___1 in
         ((b.FStarC_Syntax_Syntax.binder_bv), uu___)) tvs in
  let tys =
    let uu___ =
      FStarC_List.map
        (fun b ->
           (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort) bs in
    FStarC_List.op_At uu___ [res] in
  let embs = FStarC_List.map (embedding_for st k env) tys in
  let f = FStarC_Syntax_Syntax.fvar fv_lid FStar_Pervasives_Native.None in
  let wrap vs res_ty mk =
    match env with
    | [] -> mk vs
    | uu___ ->
        let uu___1 = FStarC_Util.prefix vs in
        (match uu___1 with
         | (pre, args_bv) ->
             let rest =
               FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                 args_bv.FStarC_Syntax_Syntax.sort in
             let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd env in
             let uu___3 = mk (FStarC_List.op_At pre [rest]) in
             peel_type_args st args_bv uu___2 rest res_ty uu___3) in
  if tac
  then
    let h =
      let uu___ =
        let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
        Prims.strcat "FStarC.Tactics.InterpFuns.mk_tactic_interpretation_"
          uu___1 in
      lid uu___ in
    let uu___ = signature_of st h tys in
    match uu___ with
    | (hbs, hres) ->
        let vs =
          let uu___1 = last_binders (Prims.of_int 4) hbs in fresh_bvs uu___1 in
        let body =
          wrap vs hres
            (fun vs1 ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     str
                       (Prims.strcat (FStarC_Ident.string_of_lid fv_lid)
                          " (plugin)") in
                   [uu___3; f] in
                 let uu___3 =
                   let uu___4 =
                     FStarC_List.map FStarC_Syntax_Syntax.bv_to_name vs1 in
                   FStarC_List.op_At embs uu___4 in
                 FStarC_List.op_At uu___2 uu___3 in
               call h tys uu___1) in
        let uu___1 = FStarC_List.map FStarC_Syntax_Syntax.mk_binder vs in
        FStarC_Syntax_Util.abs uu___1 body FStar_Pervasives_Native.None
  else
    (let h =
       match k with
       | SyntaxTerm ->
           let uu___ =
             let uu___1 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
             Prims.strcat "FStarC.Syntax.Embeddings.arrow_as_prim_step_"
               uu___1 in
           lid uu___
       | NBETerm ->
           let uu___ =
             let uu___1 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
             Prims.strcat "FStarC.TypeChecker.NBETerm.arrow_as_prim_step_"
               uu___1 in
           lid uu___ in
     let uu___ = signature_of st h tys in
     match uu___ with
     | (hbs, hres) ->
         let vs =
           let uu___1 = last_binders (Prims.of_int 3) hbs in fresh_bvs uu___1 in
         let lid_of_str =
           let uu___1 = lid "FStarC.Ident.lid_of_str" in
           let uu___2 =
             let uu___3 = str (FStarC_Ident.string_of_lid fv_lid) in [uu___3] in
           call uu___1 [] uu___2 in
         let body =
           wrap vs hres
             (fun vs1 ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStarC_List.map FStarC_Syntax_Syntax.bv_to_name vs1 in
                    FStarC_List.op_At [f; lid_of_str] uu___3 in
                  FStarC_List.op_At embs uu___2 in
                call h tys uu___1) in
         let vs1 =
           match k with
           | NBETerm -> vs
           | SyntaxTerm ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = lid "FStarC.TypeChecker.Primops.Base.psc" in
                   FStarC_Syntax_Syntax.fvar uu___3
                     FStar_Pervasives_Native.None in
                 FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   uu___2 in
               uu___1 :: vs in
         let uu___1 = FStarC_List.map FStarC_Syntax_Syntax.mk_binder vs1 in
         FStarC_Syntax_Util.abs uu___1 body FStar_Pervasives_Native.None)
let split_type_binders (bs : FStarC_Syntax_Syntax.binder Prims.list) :
  (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.binder
    Prims.list)=
  let is_type b =
    let uu___ =
      let uu___1 =
        FStarC_Syntax_Subst.compress
          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_type _0 -> true
    | uu___1 -> false in
  let uu___ =
    FStarC_Util.prefix_until
      (fun b -> let uu___1 = is_type b in Prims.not uu___1) bs in
  match uu___ with
  | FStar_Pervasives_Native.None -> (bs, [])
  | FStar_Pervasives_Native.Some (tvs, x, rest) -> (tvs, (x :: rest))
let plugin_norm_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.EraseUniverses;
  FStarC_TypeChecker_Env.AllowUnboundUniverses;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
  FStarC_TypeChecker_Env.ForExtraction]
let registration (st : FStarC_Custard_Extract.state)
  (arity_opt : Prims.int FStar_Pervasives_Native.option)
  (r : FStarC_Range_Type.t) (lb : FStarC_Syntax_Syntax.letbinding) : 
  unit=
  let fv =
    match lb.FStarC_Syntax_Syntax.lbname with | FStar_Pervasives.Inr v -> v in
  let fv_lid = FStarC_Syntax_Syntax.lid_of_fv fv in
  let name_str = FStarC_Ident.string_of_lid fv_lid in
  let key = Prims.strcat "regemb:" name_str in
  let uu___ = FStarC_Custard_Extract.emitted st key in
  if uu___
  then ()
  else
    (let t =
       let uu___1 = FStarC_Custard_Extract.tcenv st in
       FStarC_Custard_Mono.norm_bounded uu___1 "a plugin's type"
         plugin_norm_steps lb.FStarC_Syntax_Syntax.lbtyp in
     let uu___1 = FStarC_Syntax_Util.arrow_formals_comp t in
     match uu___1 with
     | (bs, c) ->
         let uu___2 =
           match arity_opt with
           | FStar_Pervasives_Native.None -> (bs, c)
           | FStar_Pervasives_Native.Some k ->
               let nbs = FStarC_List.length bs in
               if k = nbs
               then (bs, c)
               else
                 if k < nbs
                 then
                   (let uu___3 = FStarC_Util.first_N k bs in
                    match uu___3 with
                    | (bs1, rest) ->
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Util.arrow rest c in
                          FStarC_Syntax_Syntax.mk_Total uu___5 in
                        (bs1, uu___4))
                 else
                   (let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_int k in
                        let uu___6 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_nat nbs in
                        FStarC_Format.fmt2
                          "expected arity at least %s; got %s" uu___5 uu___6 in
                      NoEmbedding uu___4 in
                    FStarC_Effect.raise uu___3) in
         (match uu___2 with
          | (bs1, c1) ->
              let arity = FStarC_List.length bs1 in
              let uu___3 = split_type_binders bs1 in
              (match uu___3 with
               | (tvs, bs2) ->
                   let n = FStarC_List.length bs2 in
                   let res = FStarC_Syntax_Util.comp_result c1 in
                   let tac =
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Util.is_pure_comp c1 in
                       Prims.not uu___5 in
                     if uu___4
                     then
                       FStarC_Ident.lid_equals
                         (FStarC_Syntax_Util.comp_effect_name c1)
                         FStarC_Parser_Const.effect_TAC_lid
                     else false in
                   ((let uu___5 =
                       if Prims.not tac
                       then
                         let uu___6 = FStarC_Syntax_Util.is_pure_comp c1 in
                         Prims.not uu___6
                       else false in
                     if uu___5
                     then
                       FStarC_Effect.raise
                         (NoEmbedding
                            (Prims.strcat "no plugin for effect "
                               (FStarC_Ident.string_of_lid
                                  (FStarC_Syntax_Util.comp_effect_name c1))))
                     else ());
                    if n = Prims.int_zero
                    then
                      FStarC_Effect.raise
                        (NoEmbedding
                           "a plugin must take at least one argument")
                    else ();
                    if tac && (n > (Prims.of_int 20))
                    then
                      FStarC_Effect.raise
                        (NoEmbedding
                           "tactic plugins can take at most 20 arguments")
                    else ();
                    (let string_ty =
                       FStarC_Custard_Extract.ty_of_typ st
                         FStarC_Syntax_Syntax.t_string in
                     let int_ty =
                       FStarC_Custard_Extract.ty_of_typ st
                         FStarC_Syntax_Syntax.t_int in
                     let interp =
                       let uu___7 =
                         interp_term st SyntaxTerm tac fv_lid n tvs bs2 res in
                       compile st uu___7 in
                     let uu___7 =
                       if tac
                       then
                         ([interp], "register_tactic",
                           (arity + Prims.int_one))
                       else
                         (let nbe =
                            let uu___8 =
                              interp_term st NBETerm tac fv_lid n tvs bs2 res in
                            compile st uu___8 in
                          ([interp; nbe], "register_plugin", arity)) in
                     match uu___7 with
                     | (args, which, arity1) ->
                         let fty =
                           FStarC_List.fold_right
                             (fun a t1 ->
                                FStarC_Custard_Syntax.TArrow
                                  ((a.FStarC_Custard_Syntax.ty),
                                    FStarC_Custard_Syntax.E_Pure, t1)) args
                             FStarC_Custard_Syntax.TUnit in
                         let fty1 =
                           FStarC_Custard_Syntax.TArrow
                             (string_ty, FStarC_Custard_Syntax.E_Pure,
                               (FStarC_Custard_Syntax.TArrow
                                  (int_ty, FStarC_Custard_Syntax.E_Pure, fty))) in
                         let reg = register_fn st which fty1 in
                         let body =
                           ir_call reg fty1
                             (FStarC_List.op_At
                                [FStarC_Custard_Syntax.mk
                                   (FStarC_Custard_Syntax.EConst
                                      (FStarC_Custard_Syntax.CString name_str))
                                   string_ty FStarC_Custard_Syntax.E_Pure;
                                FStarC_Custard_Syntax.mk
                                  (FStarC_Custard_Syntax.EConst
                                     (FStarC_Custard_Syntax.CInt
                                        (arity1, FStar_IntegerLiteral.Dec,
                                          FStar_Pervasives_Native.None)))
                                  int_ty FStarC_Custard_Syntax.E_Pure] args) in
                         let nm = FStarC_Custard_Extract.name_of_lid fv_lid in
                         FStarC_Custard_Extract.emit st key
                           (FStarC_Custard_Syntax.DLet
                              {
                                FStarC_Custard_Syntax.dl_name =
                                  {
                                    FStarC_Custard_Syntax.ns =
                                      (nm.FStarC_Custard_Syntax.ns);
                                    FStarC_Custard_Syntax.id =
                                      (Prims.strcat "__plugin_"
                                         nm.FStarC_Custard_Syntax.id);
                                    FStarC_Custard_Syntax.spec =
                                      (nm.FStarC_Custard_Syntax.spec)
                                  };
                                FStarC_Custard_Syntax.dl_typars = [];
                                FStarC_Custard_Syntax.dl_binders = [];
                                FStarC_Custard_Syntax.dl_ret =
                                  FStarC_Custard_Syntax.TUnit;
                                FStarC_Custard_Syntax.dl_eff =
                                  FStarC_Custard_Syntax.E_Impure;
                                FStarC_Custard_Syntax.dl_body = body;
                                FStarC_Custard_Syntax.dl_flags =
                                  [FStarC_Custard_Syntax.Root;
                                  FStarC_Custard_Syntax.Comment
                                    (Prims.strcat "Plugin registration for "
                                       name_str)]
                              }))))))
let plugin_arity (attrs : FStarC_Syntax_Syntax.term Prims.list) :
  Prims.int FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  FStarC_Util.find_map attrs
    (fun t ->
       let uu___ = FStarC_Syntax_Util.head_and_args_full t in
       match uu___ with
       | (head, args) ->
           let uu___1 =
             let uu___2 =
               FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.plugin_attr
                 head in
             Prims.not uu___2 in
           if uu___1
           then FStar_Pervasives_Native.None
           else
             (match args with
              | (a, uu___2)::[] ->
                  let uu___3 =
                    FStarC_Syntax_Embeddings_Base.unembed
                      FStarC_Syntax_Embeddings.e_int a
                      FStarC_Syntax_Embeddings_Base.id_norm_cb in
                  FStar_Pervasives_Native.Some uu___3
              | uu___2 ->
                  FStar_Pervasives_Native.Some FStar_Pervasives_Native.None))
let handle_sigelt (st : FStarC_Custard_Extract.state)
  (arity_opt : Prims.int FStar_Pervasives_Native.option)
  (se : FStarC_Syntax_Syntax.sigelt) : unit=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (uu___, lbs);
        FStarC_Syntax_Syntax.lids1 = uu___1;_}
      ->
      FStarC_List.iter
        (fun lb ->
           try
             (fun uu___2 ->
                match () with
                | () ->
                    registration st arity_opt se.FStarC_Syntax_Syntax.sigrng
                      lb) ()
           with
           | NoEmbedding msg ->
               warn_not_implemented se.FStarC_Syntax_Syntax.sigrng
                 (match lb.FStarC_Syntax_Syntax.lbname with
                  | FStar_Pervasives.Inr fv ->
                      FStarC_Ident.string_of_lid
                        (FStarC_Syntax_Syntax.lid_of_fv fv)
                  | FStar_Pervasives.Inl bv ->
                      FStarC_Ident.string_of_id
                        bv.FStarC_Syntax_Syntax.ppname) msg) lbs
  | uu___ -> ()
let requested (roots : FStarC_Ident.lident Prims.list)
  (md : FStarC_Syntax_Syntax.modul) : Prims.bool=
  let m = FStarC_Ident.string_of_lid md.FStarC_Syntax_Syntax.name in
  FStarC_List.existsb (fun l -> (FStarC_Ident.string_of_lid l) = m) roots
let handle_module (st : FStarC_Custard_Extract.state)
  (roots : FStarC_Ident.lident Prims.list) (md : FStarC_Syntax_Syntax.modul)
  : unit=
  let uu___ = let uu___1 = requested roots md in Prims.not uu___1 in
  if uu___
  then ()
  else
    FStarC_List.iter
      (fun se ->
         let uu___1 = plugin_arity se.FStarC_Syntax_Syntax.sigattrs in
         match uu___1 with
         | FStar_Pervasives_Native.None -> ()
         | FStar_Pervasives_Native.Some uu___2 when
             FStarC_List.existsb
               (fun uu___3 ->
                  match uu___3 with
                  | FStarC_Syntax_Syntax.Projector uu___4 -> true
                  | FStarC_Syntax_Syntax.Discriminator uu___4 -> true
                  | uu___4 -> false) se.FStarC_Syntax_Syntax.sigquals
             -> ()
         | FStar_Pervasives_Native.Some arity_opt ->
             handle_sigelt st arity_opt se)
      md.FStarC_Syntax_Syntax.declarations
