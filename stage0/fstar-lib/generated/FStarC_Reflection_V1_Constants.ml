open Prims
type refl_constant =
  {
  lid: FStarC_Ident.lid ;
  fv: FStarC_Syntax_Syntax.fv ;
  t: FStarC_Syntax_Syntax.term }
let (__proj__Mkrefl_constant__item__lid : refl_constant -> FStarC_Ident.lid)
  = fun projectee -> match projectee with | { lid; fv; t;_} -> lid
let (__proj__Mkrefl_constant__item__fv :
  refl_constant -> FStarC_Syntax_Syntax.fv) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> fv
let (__proj__Mkrefl_constant__item__t :
  refl_constant -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> t
let (refl_constant_lid : refl_constant -> FStarC_Ident.lid) =
  fun rc -> rc.lid
let (refl_constant_term : refl_constant -> FStarC_Syntax_Syntax.term) =
  fun rc -> rc.t
let (fstar_refl_lid : Prims.string Prims.list -> FStarC_Ident.lident) =
  fun s ->
    FStarC_Ident.lid_of_path
      (FStarC_Compiler_List.op_At ["FStar"; "Stubs"; "Reflection"] s)
      FStarC_Compiler_Range_Type.dummyRange
let (fstar_refl_types_lid : Prims.string -> FStarC_Ident.lident) =
  fun s -> fstar_refl_lid ["Types"; s]
let (fstar_refl_builtins_lid : Prims.string -> FStarC_Ident.lident) =
  fun s -> fstar_refl_lid ["V1"; "Builtins"; s]
let (fstar_refl_data_lid : Prims.string -> FStarC_Ident.lident) =
  fun s -> fstar_refl_lid ["V1"; "Data"; s]
let (fstar_refl_data_const : Prims.string -> refl_constant) =
  fun s ->
    let lid = fstar_refl_data_lid s in
    let uu___ =
      FStarC_Syntax_Syntax.lid_as_fv lid
        (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
    let uu___1 = FStarC_Syntax_Syntax.tdataconstr lid in
    { lid; fv = uu___; t = uu___1 }
let (mk_refl_types_lid_as_term : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s ->
    let uu___ = fstar_refl_types_lid s in FStarC_Syntax_Syntax.tconst uu___
let (mk_refl_types_lid_as_fv : Prims.string -> FStarC_Syntax_Syntax.fv) =
  fun s ->
    let uu___ = fstar_refl_types_lid s in FStarC_Syntax_Syntax.fvconst uu___
let (mk_refl_data_lid_as_term : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s ->
    let uu___ = fstar_refl_data_lid s in FStarC_Syntax_Syntax.tconst uu___
let (mk_refl_data_lid_as_fv : Prims.string -> FStarC_Syntax_Syntax.fv) =
  fun s ->
    let uu___ = fstar_refl_data_lid s in FStarC_Syntax_Syntax.fvconst uu___
let (mk_inspect_pack_pair : Prims.string -> (refl_constant * refl_constant))
  =
  fun s ->
    let inspect_lid = fstar_refl_builtins_lid (Prims.strcat "inspect" s) in
    let pack_lid = fstar_refl_builtins_lid (Prims.strcat "pack" s) in
    let inspect_fv =
      FStarC_Syntax_Syntax.lid_as_fv inspect_lid FStar_Pervasives_Native.None in
    let pack_fv =
      FStarC_Syntax_Syntax.lid_as_fv pack_lid FStar_Pervasives_Native.None in
    let inspect =
      let uu___ = FStarC_Syntax_Syntax.fv_to_tm inspect_fv in
      { lid = inspect_lid; fv = inspect_fv; t = uu___ } in
    let pack =
      let uu___ = FStarC_Syntax_Syntax.fv_to_tm pack_fv in
      { lid = pack_lid; fv = pack_fv; t = uu___ } in
    (inspect, pack)
let (uu___0 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_ln"
let (fstar_refl_inspect_ln : refl_constant) =
  match uu___0 with
  | (fstar_refl_inspect_ln1, fstar_refl_pack_ln) -> fstar_refl_inspect_ln1
let (fstar_refl_pack_ln : refl_constant) =
  match uu___0 with
  | (fstar_refl_inspect_ln1, fstar_refl_pack_ln1) -> fstar_refl_pack_ln1
let (uu___1 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_fv"
let (fstar_refl_inspect_fv : refl_constant) =
  match uu___1 with
  | (fstar_refl_inspect_fv1, fstar_refl_pack_fv) -> fstar_refl_inspect_fv1
let (fstar_refl_pack_fv : refl_constant) =
  match uu___1 with
  | (fstar_refl_inspect_fv1, fstar_refl_pack_fv1) -> fstar_refl_pack_fv1
let (uu___2 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_bv"
let (fstar_refl_inspect_bv : refl_constant) =
  match uu___2 with
  | (fstar_refl_inspect_bv1, fstar_refl_pack_bv) -> fstar_refl_inspect_bv1
let (fstar_refl_pack_bv : refl_constant) =
  match uu___2 with
  | (fstar_refl_inspect_bv1, fstar_refl_pack_bv1) -> fstar_refl_pack_bv1
let (uu___3 : (refl_constant * refl_constant)) =
  mk_inspect_pack_pair "_binder"
let (fstar_refl_inspect_binder : refl_constant) =
  match uu___3 with
  | (fstar_refl_inspect_binder1, fstar_refl_pack_binder) ->
      fstar_refl_inspect_binder1
let (fstar_refl_pack_binder : refl_constant) =
  match uu___3 with
  | (fstar_refl_inspect_binder1, fstar_refl_pack_binder1) ->
      fstar_refl_pack_binder1
let (uu___4 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_comp"
let (fstar_refl_inspect_comp : refl_constant) =
  match uu___4 with
  | (fstar_refl_inspect_comp1, fstar_refl_pack_comp) ->
      fstar_refl_inspect_comp1
let (fstar_refl_pack_comp : refl_constant) =
  match uu___4 with
  | (fstar_refl_inspect_comp1, fstar_refl_pack_comp1) ->
      fstar_refl_pack_comp1
let (uu___5 : (refl_constant * refl_constant)) =
  mk_inspect_pack_pair "_sigelt"
let (fstar_refl_inspect_sigelt : refl_constant) =
  match uu___5 with
  | (fstar_refl_inspect_sigelt1, fstar_refl_pack_sigelt) ->
      fstar_refl_inspect_sigelt1
let (fstar_refl_pack_sigelt : refl_constant) =
  match uu___5 with
  | (fstar_refl_inspect_sigelt1, fstar_refl_pack_sigelt1) ->
      fstar_refl_pack_sigelt1
let (uu___6 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_lb"
let (fstar_refl_inspect_lb : refl_constant) =
  match uu___6 with
  | (fstar_refl_inspect_lb1, fstar_refl_pack_lb) -> fstar_refl_inspect_lb1
let (fstar_refl_pack_lb : refl_constant) =
  match uu___6 with
  | (fstar_refl_inspect_lb1, fstar_refl_pack_lb1) -> fstar_refl_pack_lb1
let (uu___7 : (refl_constant * refl_constant)) =
  mk_inspect_pack_pair "_universe"
let (fstar_refl_inspect_universe : refl_constant) =
  match uu___7 with
  | (fstar_refl_inspect_universe1, fstar_refl_pack_universe) ->
      fstar_refl_inspect_universe1
let (fstar_refl_pack_universe : refl_constant) =
  match uu___7 with
  | (fstar_refl_inspect_universe1, fstar_refl_pack_universe1) ->
      fstar_refl_pack_universe1
let (fstar_refl_env : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "env"
let (fstar_refl_env_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "env"
let (fstar_refl_bv : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "bv"
let (fstar_refl_bv_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "bv"
let (fstar_refl_fv : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "fv"
let (fstar_refl_fv_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "fv"
let (fstar_refl_comp : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "comp"
let (fstar_refl_comp_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "comp"
let (fstar_refl_binder : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "binder"
let (fstar_refl_binder_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "binder"
let (fstar_refl_sigelt : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "sigelt"
let (fstar_refl_sigelt_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "sigelt"
let (fstar_refl_term : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "term"
let (fstar_refl_term_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "term"
let (fstar_refl_letbinding : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "letbinding"
let (fstar_refl_letbinding_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "letbinding"
let (fstar_refl_ident : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "ident"
let (fstar_refl_ident_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "ident"
let (fstar_refl_univ_name : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "univ_name"
let (fstar_refl_univ_name_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "univ_name"
let (fstar_refl_optionstate : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "optionstate"
let (fstar_refl_optionstate_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "optionstate"
let (fstar_refl_universe : FStarC_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "universe"
let (fstar_refl_universe_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "universe"
let (fstar_refl_aqualv : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "aqualv"
let (fstar_refl_aqualv_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "aqualv"
let (fstar_refl_comp_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "comp_view"
let (fstar_refl_comp_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "comp_view"
let (fstar_refl_term_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "term_view"
let (fstar_refl_term_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "term_view"
let (fstar_refl_pattern : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "pattern"
let (fstar_refl_pattern_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "pattern"
let (fstar_refl_branch : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "branch"
let (fstar_refl_branch_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "branch"
let (fstar_refl_bv_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "bv_view"
let (fstar_refl_bv_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "bv_view"
let (fstar_refl_binder_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "binder_view"
let (fstar_refl_binder_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "binder_view"
let (fstar_refl_vconst : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "vconst"
let (fstar_refl_vconst_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "vconst"
let (fstar_refl_lb_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "lb_view"
let (fstar_refl_lb_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "lb_view"
let (fstar_refl_sigelt_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "sigelt_view"
let (fstar_refl_sigelt_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "sigelt_view"
let (fstar_refl_qualifier : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "qualifier"
let (fstar_refl_qualifier_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "qualifier"
let (fstar_refl_universe_view : FStarC_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "universe_view"
let (fstar_refl_universe_view_fv : FStarC_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "universe_view"
let (ref_Mk_bv : refl_constant) =
  let lid = fstar_refl_data_lid "Mkbv_view" in
  let attr =
    let uu___ =
      let uu___8 = fstar_refl_data_lid "bv_view" in
      let uu___9 =
        let uu___10 =
          FStarC_Ident.mk_ident
            ("bv_ppname", FStarC_Compiler_Range_Type.dummyRange) in
        let uu___11 =
          let uu___12 =
            FStarC_Ident.mk_ident
              ("bv_index", FStarC_Compiler_Range_Type.dummyRange) in
          [uu___12] in
        uu___10 :: uu___11 in
      (uu___8, uu___9) in
    FStarC_Syntax_Syntax.Record_ctor uu___ in
  let fv =
    FStarC_Syntax_Syntax.lid_as_fv lid (FStar_Pervasives_Native.Some attr) in
  let uu___ = FStarC_Syntax_Syntax.fv_to_tm fv in { lid; fv; t = uu___ }
let (ref_Mk_binder : refl_constant) =
  let lid = fstar_refl_data_lid "Mkbinder_view" in
  let attr =
    let uu___ =
      let uu___8 = fstar_refl_data_lid "binder_view" in
      let uu___9 =
        let uu___10 =
          FStarC_Ident.mk_ident
            ("binder_bv", FStarC_Compiler_Range_Type.dummyRange) in
        let uu___11 =
          let uu___12 =
            FStarC_Ident.mk_ident
              ("binder_qual", FStarC_Compiler_Range_Type.dummyRange) in
          let uu___13 =
            let uu___14 =
              FStarC_Ident.mk_ident
                ("binder_attrs", FStarC_Compiler_Range_Type.dummyRange) in
            let uu___15 =
              let uu___16 =
                FStarC_Ident.mk_ident
                  ("binder_sort", FStarC_Compiler_Range_Type.dummyRange) in
              [uu___16] in
            uu___14 :: uu___15 in
          uu___12 :: uu___13 in
        uu___10 :: uu___11 in
      (uu___8, uu___9) in
    FStarC_Syntax_Syntax.Record_ctor uu___ in
  let fv =
    FStarC_Syntax_Syntax.lid_as_fv lid (FStar_Pervasives_Native.Some attr) in
  let uu___ = FStarC_Syntax_Syntax.fv_to_tm fv in { lid; fv; t = uu___ }
let (ref_Mk_lb : refl_constant) =
  let lid = fstar_refl_data_lid "Mklb_view" in
  let attr =
    let uu___ =
      let uu___8 = fstar_refl_data_lid "lb_view" in
      let uu___9 =
        let uu___10 =
          FStarC_Ident.mk_ident
            ("lb_fv", FStarC_Compiler_Range_Type.dummyRange) in
        let uu___11 =
          let uu___12 =
            FStarC_Ident.mk_ident
              ("lb_us", FStarC_Compiler_Range_Type.dummyRange) in
          let uu___13 =
            let uu___14 =
              FStarC_Ident.mk_ident
                ("lb_typ", FStarC_Compiler_Range_Type.dummyRange) in
            let uu___15 =
              let uu___16 =
                FStarC_Ident.mk_ident
                  ("lb_def", FStarC_Compiler_Range_Type.dummyRange) in
              [uu___16] in
            uu___14 :: uu___15 in
          uu___12 :: uu___13 in
        uu___10 :: uu___11 in
      (uu___8, uu___9) in
    FStarC_Syntax_Syntax.Record_ctor uu___ in
  let fv =
    FStarC_Syntax_Syntax.lid_as_fv lid (FStar_Pervasives_Native.Some attr) in
  let uu___ = FStarC_Syntax_Syntax.fv_to_tm fv in { lid; fv; t = uu___ }
let (ref_Q_Explicit : refl_constant) = fstar_refl_data_const "Q_Explicit"
let (ref_Q_Implicit : refl_constant) = fstar_refl_data_const "Q_Implicit"
let (ref_Q_Meta : refl_constant) = fstar_refl_data_const "Q_Meta"
let (ref_C_Unit : refl_constant) = fstar_refl_data_const "C_Unit"
let (ref_C_True : refl_constant) = fstar_refl_data_const "C_True"
let (ref_C_False : refl_constant) = fstar_refl_data_const "C_False"
let (ref_C_Int : refl_constant) = fstar_refl_data_const "C_Int"
let (ref_C_String : refl_constant) = fstar_refl_data_const "C_String"
let (ref_C_Range : refl_constant) = fstar_refl_data_const "C_Range"
let (ref_C_Reify : refl_constant) = fstar_refl_data_const "C_Reify"
let (ref_C_Reflect : refl_constant) = fstar_refl_data_const "C_Reflect"
let (ref_Pat_Constant : refl_constant) = fstar_refl_data_const "Pat_Constant"
let (ref_Pat_Cons : refl_constant) = fstar_refl_data_const "Pat_Cons"
let (ref_Pat_Var : refl_constant) = fstar_refl_data_const "Pat_Var"
let (ref_Pat_Dot_Term : refl_constant) = fstar_refl_data_const "Pat_Dot_Term"
let (ref_Uv_Zero : refl_constant) = fstar_refl_data_const "Uv_Zero"
let (ref_Uv_Succ : refl_constant) = fstar_refl_data_const "Uv_Succ"
let (ref_Uv_Max : refl_constant) = fstar_refl_data_const "Uv_Max"
let (ref_Uv_BVar : refl_constant) = fstar_refl_data_const "Uv_BVar"
let (ref_Uv_Name : refl_constant) = fstar_refl_data_const "Uv_Name"
let (ref_Uv_Unif : refl_constant) = fstar_refl_data_const "Uv_Unif"
let (ref_Uv_Unk : refl_constant) = fstar_refl_data_const "Uv_Unk"
let (ref_Tv_Var : refl_constant) = fstar_refl_data_const "Tv_Var"
let (ref_Tv_BVar : refl_constant) = fstar_refl_data_const "Tv_BVar"
let (ref_Tv_FVar : refl_constant) = fstar_refl_data_const "Tv_FVar"
let (ref_Tv_UInst : refl_constant) = fstar_refl_data_const "Tv_UInst"
let (ref_Tv_App : refl_constant) = fstar_refl_data_const "Tv_App"
let (ref_Tv_Abs : refl_constant) = fstar_refl_data_const "Tv_Abs"
let (ref_Tv_Arrow : refl_constant) = fstar_refl_data_const "Tv_Arrow"
let (ref_Tv_Type : refl_constant) = fstar_refl_data_const "Tv_Type"
let (ref_Tv_Refine : refl_constant) = fstar_refl_data_const "Tv_Refine"
let (ref_Tv_Const : refl_constant) = fstar_refl_data_const "Tv_Const"
let (ref_Tv_Uvar : refl_constant) = fstar_refl_data_const "Tv_Uvar"
let (ref_Tv_Let : refl_constant) = fstar_refl_data_const "Tv_Let"
let (ref_Tv_Match : refl_constant) = fstar_refl_data_const "Tv_Match"
let (ref_Tv_AscT : refl_constant) = fstar_refl_data_const "Tv_AscribedT"
let (ref_Tv_AscC : refl_constant) = fstar_refl_data_const "Tv_AscribedC"
let (ref_Tv_Unknown : refl_constant) = fstar_refl_data_const "Tv_Unknown"
let (ref_Tv_Unsupp : refl_constant) = fstar_refl_data_const "Tv_Unsupp"
let (ref_C_Total : refl_constant) = fstar_refl_data_const "C_Total"
let (ref_C_GTotal : refl_constant) = fstar_refl_data_const "C_GTotal"
let (ref_C_Lemma : refl_constant) = fstar_refl_data_const "C_Lemma"
let (ref_C_Eff : refl_constant) = fstar_refl_data_const "C_Eff"
let (ref_Sg_Let : refl_constant) = fstar_refl_data_const "Sg_Let"
let (ref_Sg_Inductive : refl_constant) = fstar_refl_data_const "Sg_Inductive"
let (ref_Sg_Val : refl_constant) = fstar_refl_data_const "Sg_Val"
let (ref_Unk : refl_constant) = fstar_refl_data_const "Unk"
let (ref_qual_Assumption : refl_constant) =
  fstar_refl_data_const "Assumption"
let (ref_qual_InternalAssumption : refl_constant) =
  fstar_refl_data_const "InternalAssumption"
let (ref_qual_New : refl_constant) = fstar_refl_data_const "New"
let (ref_qual_Private : refl_constant) = fstar_refl_data_const "Private"
let (ref_qual_Unfold_for_unification_and_vcgen : refl_constant) =
  fstar_refl_data_const "Unfold_for_unification_and_vcgen"
let (ref_qual_Visible_default : refl_constant) =
  fstar_refl_data_const "Visible_default"
let (ref_qual_Irreducible : refl_constant) =
  fstar_refl_data_const "Irreducible"
let (ref_qual_Inline_for_extraction : refl_constant) =
  fstar_refl_data_const "Inline_for_extraction"
let (ref_qual_NoExtract : refl_constant) = fstar_refl_data_const "NoExtract"
let (ref_qual_Noeq : refl_constant) = fstar_refl_data_const "Noeq"
let (ref_qual_Unopteq : refl_constant) = fstar_refl_data_const "Unopteq"
let (ref_qual_TotalEffect : refl_constant) =
  fstar_refl_data_const "TotalEffect"
let (ref_qual_Logic : refl_constant) = fstar_refl_data_const "Logic"
let (ref_qual_Reifiable : refl_constant) = fstar_refl_data_const "Reifiable"
let (ref_qual_Reflectable : refl_constant) =
  fstar_refl_data_const "Reflectable"
let (ref_qual_Discriminator : refl_constant) =
  fstar_refl_data_const "Discriminator"
let (ref_qual_Projector : refl_constant) = fstar_refl_data_const "Projector"
let (ref_qual_RecordType : refl_constant) =
  fstar_refl_data_const "RecordType"
let (ref_qual_RecordConstructor : refl_constant) =
  fstar_refl_data_const "RecordConstructor"
let (ref_qual_Action : refl_constant) = fstar_refl_data_const "Action"
let (ref_qual_ExceptionConstructor : refl_constant) =
  fstar_refl_data_const "ExceptionConstructor"
let (ref_qual_HasMaskedEffect : refl_constant) =
  fstar_refl_data_const "HasMaskedEffect"
let (ref_qual_Effect : refl_constant) = fstar_refl_data_const "Effect"
let (ref_qual_OnlyName : refl_constant) = fstar_refl_data_const "OnlyName"