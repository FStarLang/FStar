open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | ZetaFull 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | DoNotUnfoldPureLets 
  | UnfoldUntil of FStarC_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStarC_Ident.lid Prims.list 
  | UnfoldOnce of FStarC_Ident.lid Prims.list 
  | UnfoldFully of FStarC_Ident.lid Prims.list 
  | UnfoldAttr of FStarC_Ident.lid Prims.list 
  | UnfoldQual of Prims.string Prims.list 
  | UnfoldNamespace of Prims.string Prims.list 
  | DontUnfoldAttr of FStarC_Ident.lid Prims.list 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe 
  | NBE 
  | ForExtraction 
  | Unrefine 
  | NormDebug 
  | DefaultUnivsToZero 
  | Tactics 
let uu___is_Beta (projectee : step) : Prims.bool=
  match projectee with | Beta -> true | uu___ -> false
let uu___is_Iota (projectee : step) : Prims.bool=
  match projectee with | Iota -> true | uu___ -> false
let uu___is_Zeta (projectee : step) : Prims.bool=
  match projectee with | Zeta -> true | uu___ -> false
let uu___is_ZetaFull (projectee : step) : Prims.bool=
  match projectee with | ZetaFull -> true | uu___ -> false
let uu___is_Exclude (projectee : step) : Prims.bool=
  match projectee with | Exclude _0 -> true | uu___ -> false
let __proj__Exclude__item___0 (projectee : step) : step=
  match projectee with | Exclude _0 -> _0
let uu___is_Weak (projectee : step) : Prims.bool=
  match projectee with | Weak -> true | uu___ -> false
let uu___is_HNF (projectee : step) : Prims.bool=
  match projectee with | HNF -> true | uu___ -> false
let uu___is_Primops (projectee : step) : Prims.bool=
  match projectee with | Primops -> true | uu___ -> false
let uu___is_Eager_unfolding (projectee : step) : Prims.bool=
  match projectee with | Eager_unfolding -> true | uu___ -> false
let uu___is_Inlining (projectee : step) : Prims.bool=
  match projectee with | Inlining -> true | uu___ -> false
let uu___is_DoNotUnfoldPureLets (projectee : step) : Prims.bool=
  match projectee with | DoNotUnfoldPureLets -> true | uu___ -> false
let uu___is_UnfoldUntil (projectee : step) : Prims.bool=
  match projectee with | UnfoldUntil _0 -> true | uu___ -> false
let __proj__UnfoldUntil__item___0 (projectee : step) :
  FStarC_Syntax_Syntax.delta_depth=
  match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly (projectee : step) : Prims.bool=
  match projectee with | UnfoldOnly _0 -> true | uu___ -> false
let __proj__UnfoldOnly__item___0 (projectee : step) :
  FStarC_Ident.lid Prims.list= match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldOnce (projectee : step) : Prims.bool=
  match projectee with | UnfoldOnce _0 -> true | uu___ -> false
let __proj__UnfoldOnce__item___0 (projectee : step) :
  FStarC_Ident.lid Prims.list= match projectee with | UnfoldOnce _0 -> _0
let uu___is_UnfoldFully (projectee : step) : Prims.bool=
  match projectee with | UnfoldFully _0 -> true | uu___ -> false
let __proj__UnfoldFully__item___0 (projectee : step) :
  FStarC_Ident.lid Prims.list= match projectee with | UnfoldFully _0 -> _0
let uu___is_UnfoldAttr (projectee : step) : Prims.bool=
  match projectee with | UnfoldAttr _0 -> true | uu___ -> false
let __proj__UnfoldAttr__item___0 (projectee : step) :
  FStarC_Ident.lid Prims.list= match projectee with | UnfoldAttr _0 -> _0
let uu___is_UnfoldQual (projectee : step) : Prims.bool=
  match projectee with | UnfoldQual _0 -> true | uu___ -> false
let __proj__UnfoldQual__item___0 (projectee : step) :
  Prims.string Prims.list= match projectee with | UnfoldQual _0 -> _0
let uu___is_UnfoldNamespace (projectee : step) : Prims.bool=
  match projectee with | UnfoldNamespace _0 -> true | uu___ -> false
let __proj__UnfoldNamespace__item___0 (projectee : step) :
  Prims.string Prims.list= match projectee with | UnfoldNamespace _0 -> _0
let uu___is_DontUnfoldAttr (projectee : step) : Prims.bool=
  match projectee with | DontUnfoldAttr _0 -> true | uu___ -> false
let __proj__DontUnfoldAttr__item___0 (projectee : step) :
  FStarC_Ident.lid Prims.list= match projectee with | DontUnfoldAttr _0 -> _0
let uu___is_PureSubtermsWithinComputations (projectee : step) : Prims.bool=
  match projectee with
  | PureSubtermsWithinComputations -> true
  | uu___ -> false
let uu___is_Simplify (projectee : step) : Prims.bool=
  match projectee with | Simplify -> true | uu___ -> false
let uu___is_EraseUniverses (projectee : step) : Prims.bool=
  match projectee with | EraseUniverses -> true | uu___ -> false
let uu___is_AllowUnboundUniverses (projectee : step) : Prims.bool=
  match projectee with | AllowUnboundUniverses -> true | uu___ -> false
let uu___is_Reify (projectee : step) : Prims.bool=
  match projectee with | Reify -> true | uu___ -> false
let uu___is_CompressUvars (projectee : step) : Prims.bool=
  match projectee with | CompressUvars -> true | uu___ -> false
let uu___is_NoFullNorm (projectee : step) : Prims.bool=
  match projectee with | NoFullNorm -> true | uu___ -> false
let uu___is_CheckNoUvars (projectee : step) : Prims.bool=
  match projectee with | CheckNoUvars -> true | uu___ -> false
let uu___is_Unmeta (projectee : step) : Prims.bool=
  match projectee with | Unmeta -> true | uu___ -> false
let uu___is_Unascribe (projectee : step) : Prims.bool=
  match projectee with | Unascribe -> true | uu___ -> false
let uu___is_NBE (projectee : step) : Prims.bool=
  match projectee with | NBE -> true | uu___ -> false
let uu___is_ForExtraction (projectee : step) : Prims.bool=
  match projectee with | ForExtraction -> true | uu___ -> false
let uu___is_Unrefine (projectee : step) : Prims.bool=
  match projectee with | Unrefine -> true | uu___ -> false
let uu___is_NormDebug (projectee : step) : Prims.bool=
  match projectee with | NormDebug -> true | uu___ -> false
let uu___is_DefaultUnivsToZero (projectee : step) : Prims.bool=
  match projectee with | DefaultUnivsToZero -> true | uu___ -> false
let uu___is_Tactics (projectee : step) : Prims.bool=
  match projectee with | Tactics -> true | uu___ -> false
type steps = step Prims.list
let dbg_ImplicitTrace : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "ImplicitTrace"
let dbg_LayeredEffectsEqns : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "LayeredEffectsEqns"
let rec eq_step (s1 : step) (s2 : step) : Prims.bool=
  match (s1, s2) with
  | (Beta, Beta) -> true
  | (Iota, Iota) -> true
  | (Zeta, Zeta) -> true
  | (ZetaFull, ZetaFull) -> true
  | (Exclude s11, Exclude s21) -> eq_step s11 s21
  | (Weak, Weak) -> true
  | (HNF, HNF) -> true
  | (Primops, Primops) -> true
  | (Eager_unfolding, Eager_unfolding) -> true
  | (Inlining, Inlining) -> true
  | (DoNotUnfoldPureLets, DoNotUnfoldPureLets) -> true
  | (UnfoldUntil s11, UnfoldUntil s21) -> s11 = s21
  | (UnfoldOnly lids1, UnfoldOnly lids2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Syntax_Syntax.ord_fv)) lids1
        lids2
  | (UnfoldOnce lids1, UnfoldOnce lids2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Syntax_Syntax.ord_fv)) lids1
        lids2
  | (UnfoldFully lids1, UnfoldFully lids2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Syntax_Syntax.ord_fv)) lids1
        lids2
  | (UnfoldAttr lids1, UnfoldAttr lids2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Syntax_Syntax.ord_fv)) lids1
        lids2
  | (UnfoldQual strs1, UnfoldQual strs2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Class_Ord.ord_string)) strs1
        strs2
  | (UnfoldNamespace strs1, UnfoldNamespace strs2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Class_Ord.ord_string)) strs1
        strs2
  | (DontUnfoldAttr lids1, DontUnfoldAttr lids2) ->
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Ord.ord_eq
           (FStarC_Class_Ord.ord_list FStarC_Syntax_Syntax.ord_fv)) lids1
        lids2
  | (PureSubtermsWithinComputations, PureSubtermsWithinComputations) -> true
  | (Simplify, Simplify) -> true
  | (EraseUniverses, EraseUniverses) -> true
  | (AllowUnboundUniverses, AllowUnboundUniverses) -> true
  | (Reify, Reify) -> true
  | (CompressUvars, CompressUvars) -> true
  | (NoFullNorm, NoFullNorm) -> true
  | (CheckNoUvars, CheckNoUvars) -> true
  | (Unmeta, Unmeta) -> true
  | (Unascribe, Unascribe) -> true
  | (NBE, NBE) -> true
  | (ForExtraction, ForExtraction) -> true
  | (Unrefine, Unrefine) -> true
  | (NormDebug, NormDebug) -> true
  | (DefaultUnivsToZero, DefaultUnivsToZero) -> true
  | (Tactics, Tactics) -> true
  | uu___ -> false
let deq_step : step FStarC_Class_Deq.deq=
  { FStarC_Class_Deq.op_Equals_Question = eq_step }
let rec step_to_string (s : step) : Prims.string=
  match s with
  | Beta -> "Beta"
  | Iota -> "Iota"
  | Zeta -> "Zeta"
  | ZetaFull -> "ZetaFull"
  | Exclude s1 ->
      let uu___ = step_to_string s1 in Prims.strcat "Exclude " uu___
  | Weak -> "Weak"
  | HNF -> "HNF"
  | Primops -> "Primops"
  | Eager_unfolding -> "Eager_unfolding"
  | Inlining -> "Inlining"
  | DoNotUnfoldPureLets -> "DoNotUnfoldPureLets"
  | UnfoldUntil s1 ->
      let uu___ =
        FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_delta_depth s1 in
      Prims.strcat "UnfoldUntil " uu___
  | UnfoldOnly lids1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) lids1 in
      Prims.strcat "UnfoldOnly " uu___
  | UnfoldOnce lids1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) lids1 in
      Prims.strcat "UnfoldOnce " uu___
  | UnfoldFully lids1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) lids1 in
      Prims.strcat "UnfoldFully " uu___
  | UnfoldAttr lids1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) lids1 in
      Prims.strcat "UnfoldAttr " uu___
  | UnfoldQual strs1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
          strs1 in
      Prims.strcat "UnfoldQual " uu___
  | UnfoldNamespace strs1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
          strs1 in
      Prims.strcat "UnfoldNamespace " uu___
  | DontUnfoldAttr lids1 ->
      let uu___ =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) lids1 in
      Prims.strcat "DontUnfoldAttr " uu___
  | PureSubtermsWithinComputations -> "PureSubtermsWithinComputations"
  | Simplify -> "Simplify"
  | EraseUniverses -> "EraseUniverses"
  | AllowUnboundUniverses -> "AllowUnboundUniverses"
  | Reify -> "Reify"
  | CompressUvars -> "CompressUvars"
  | NoFullNorm -> "NoFullNorm"
  | CheckNoUvars -> "CheckNoUvars"
  | Unmeta -> "Unmeta"
  | Unascribe -> "Unascribe"
  | NBE -> "NBE"
  | ForExtraction -> "ForExtraction"
  | Unrefine -> "Unrefine"
  | NormDebug -> "NormDebug"
  | DefaultUnivsToZero -> "DefaultUnivsToZero"
  | Tactics -> "Tactics"
  | uu___ -> failwith "fixme: step_to_string incomplete"
let showable_step : step FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = step_to_string }
type sig_binding =
  (FStarC_Ident.lident Prims.list * FStarC_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStarC_Syntax_Syntax.delta_depth 
let uu___is_NoDelta (projectee : delta_level) : Prims.bool=
  match projectee with | NoDelta -> true | uu___ -> false
let uu___is_InliningDelta (projectee : delta_level) : Prims.bool=
  match projectee with | InliningDelta -> true | uu___ -> false
let uu___is_Eager_unfolding_only (projectee : delta_level) : Prims.bool=
  match projectee with | Eager_unfolding_only -> true | uu___ -> false
let uu___is_Unfold (projectee : delta_level) : Prims.bool=
  match projectee with | Unfold _0 -> true | uu___ -> false
let __proj__Unfold__item___0 (projectee : delta_level) :
  FStarC_Syntax_Syntax.delta_depth= match projectee with | Unfold _0 -> _0
let deq_delta_level : delta_level FStarC_Class_Deq.deq=
  {
    FStarC_Class_Deq.op_Equals_Question =
      (fun x y ->
         match (x, y) with
         | (NoDelta, NoDelta) -> true
         | (InliningDelta, InliningDelta) -> true
         | (Eager_unfolding_only, Eager_unfolding_only) -> true
         | (Unfold x1, Unfold y1) ->
             FStarC_Class_Deq.op_Equals_Question
               FStarC_Syntax_Syntax.deq_delta_depth x1 y1
         | uu___ -> false)
  }
let showable_delta_level : delta_level FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | NoDelta -> "NoDelta"
         | InliningDelta -> "Inlining"
         | Eager_unfolding_only -> "Eager_unfolding_only"
         | Unfold d ->
             let uu___1 =
               FStarC_Class_Show.show
                 FStarC_Syntax_Syntax.showable_delta_depth d in
             Prims.strcat "Unfold " uu___1)
  }
type name_prefix = FStarC_Ident.path
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ),
    (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Pervasives.either * FStarC_Range_Type.t)
type goal = FStarC_Syntax_Syntax.term
type must_tot = Prims.bool
type mlift =
  {
  mlift_wp:
    env ->
      FStarC_Syntax_Syntax.comp ->
        (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Common.guard_t)
    ;
  mlift_term:
    (FStarC_Syntax_Syntax.universe ->
       FStarC_Syntax_Syntax.typ ->
         FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
and edge =
  {
  msource: FStarC_Ident.lident ;
  mtarget: FStarC_Ident.lident ;
  mlift: mlift ;
  mpath: FStarC_Ident.lident Prims.list }
and effects =
  {
  decls:
    (FStarC_Syntax_Syntax.eff_decl * FStarC_Syntax_Syntax.qualifier
      Prims.list) Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStarC_Ident.lident * FStarC_Ident.lident * FStarC_Ident.lident * mlift
      * mlift) Prims.list
    ;
  polymonadic_binds:
    (FStarC_Ident.lident * FStarC_Ident.lident * FStarC_Ident.lident *
      (env ->
         FStarC_Syntax_Syntax.comp_typ ->
           FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStarC_Syntax_Syntax.comp_typ ->
               FStarC_Syntax_Syntax.cflag Prims.list ->
                 FStarC_Range_Type.t ->
                   (FStarC_Syntax_Syntax.comp *
                     FStarC_TypeChecker_Common.guard_t)))
      Prims.list
    ;
  polymonadic_subcomps:
    (FStarC_Ident.lident * FStarC_Ident.lident * FStarC_Syntax_Syntax.tscheme
      * FStarC_Syntax_Syntax.indexed_effect_combinator_kind) Prims.list
    }
and env =
  {
  solver: solver_t ;
  range: FStarC_Range_Type.t ;
  curmodule: FStarC_Ident.lident ;
  gamma: FStarC_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
  gamma_cache: cached_elt FStarC_SMap.t ;
  modules: FStarC_Syntax_Syntax.modul Prims.list ;
  expected_typ:
    (FStarC_Syntax_Syntax.typ * Prims.bool) FStar_Pervasives_Native.option ;
  sigtab: FStarC_Syntax_Syntax.sigelt FStarC_SMap.t ;
  attrtab: FStarC_Syntax_Syntax.sigelt Prims.list FStarC_SMap.t ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStarC_Syntax_Syntax.lbname * Prims.int * FStarC_Syntax_Syntax.typ *
      FStarC_Syntax_Syntax.univ_names) Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq_strict: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  flychecking: Prims.bool ;
  uvar_subtyping: Prims.bool ;
  intactics: Prims.bool ;
  nocoerce: Prims.bool ;
  tc_term:
    env ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
          FStarC_TypeChecker_Common.guard_t)
    ;
  typeof_tot_or_gtot_term:
    env ->
      FStarC_Syntax_Syntax.term ->
        must_tot ->
          (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ *
            FStarC_TypeChecker_Common.guard_t)
    ;
  universe_of:
    env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.universe ;
  typeof_well_typed_tot_or_gtot_term:
    env ->
      FStarC_Syntax_Syntax.term ->
        must_tot ->
          (FStarC_Syntax_Syntax.typ * FStarC_TypeChecker_Common.guard_t)
    ;
  teq_nosmt_force:
    env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool
    ;
  subtype_nosmt_force:
    env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool
    ;
  qtbl_name_and_index:
    ((FStarC_Ident.lident * FStarC_Syntax_Syntax.typ * Prims.int)
      FStar_Pervasives_Native.option * Prims.int FStarC_SMap.t)
    ;
  normalized_eff_names: FStarC_Ident.lident FStarC_SMap.t ;
  fv_delta_depths: FStarC_Syntax_Syntax.delta_depth FStarC_SMap.t ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Range_Type.t -> FStarC_Syntax_Syntax.term
    ;
  try_solve_implicits_hook:
    env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_TypeChecker_Common.implicits -> unit
    ;
  splice:
    env ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        FStarC_Syntax_Syntax.attribute Prims.list ->
          Prims.bool ->
            FStarC_Ident.lident Prims.list ->
              FStarC_Syntax_Syntax.term ->
                FStarC_Range_Type.t -> FStarC_Syntax_Syntax.sigelt Prims.list
    ;
  mpreprocess:
    env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term
    ;
  postprocess:
    env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term
    ;
  identifier_info: FStarC_TypeChecker_Common.id_info_table FStarC_Effect.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStarC_Syntax_DsEnv.env ;
  nbe:
    step Prims.list ->
      env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term
    ;
  strict_args_tab:
    Prims.int Prims.list FStar_Pervasives_Native.option FStarC_SMap.t ;
  erasable_types_tab: Prims.bool FStarC_SMap.t ;
  enable_defer_to_tac: Prims.bool ;
  unif_allow_ref_guards: Prims.bool ;
  erase_erasable_args: Prims.bool ;
  core_check:
    env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.typ ->
          Prims.bool ->
            ((FStarC_Syntax_Syntax.typ * (unit -> unit))
               FStar_Pervasives_Native.option,
              Prims.bool -> Prims.string) FStar_Pervasives.either
    ;
  missing_decl: FStarC_Ident.lident FStarC_RBSet.t }
and solver_t =
  {
  init: env -> unit ;
  snapshot: Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit) ;
  rollback:
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit
    ;
  encode_sig: env -> FStarC_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (Prims.bool * (env * goal * FStarC_Options.optionstate) Prims.list)
    ;
  spinoff_strictly_positive_goals:
    (env -> goal -> (env * goal) Prims.list) FStar_Pervasives_Native.option ;
  handle_smt_goal: env -> goal -> (env * goal) Prims.list ;
  solve:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> goal -> unit
    ;
  solve_sync:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> goal -> Prims.bool
    ;
  finish: unit -> unit ;
  refresh: proof_namespace FStar_Pervasives_Native.option -> unit }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStarC_Syntax_Syntax.binding, sig_binding) FStar_Pervasives.either ->
        unit
    }
let __proj__Mkmlift__item__mlift_wp (projectee : mlift) :
  env ->
    FStarC_Syntax_Syntax.comp ->
      (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Common.guard_t)=
  match projectee with | { mlift_wp; mlift_term;_} -> mlift_wp
let __proj__Mkmlift__item__mlift_term (projectee : mlift) :
  (FStarC_Syntax_Syntax.universe ->
     FStarC_Syntax_Syntax.typ ->
       FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
    FStar_Pervasives_Native.option=
  match projectee with | { mlift_wp; mlift_term;_} -> mlift_term
let __proj__Mkedge__item__msource (projectee : edge) : FStarC_Ident.lident=
  match projectee with
  | { msource; mtarget; mlift = mlift1; mpath;_} -> msource
let __proj__Mkedge__item__mtarget (projectee : edge) : FStarC_Ident.lident=
  match projectee with
  | { msource; mtarget; mlift = mlift1; mpath;_} -> mtarget
let __proj__Mkedge__item__mlift (projectee : edge) : mlift=
  match projectee with
  | { msource; mtarget; mlift = mlift1; mpath;_} -> mlift1
let __proj__Mkedge__item__mpath (projectee : edge) :
  FStarC_Ident.lident Prims.list=
  match projectee with
  | { msource; mtarget; mlift = mlift1; mpath;_} -> mpath
let __proj__Mkeffects__item__decls (projectee : effects) :
  (FStarC_Syntax_Syntax.eff_decl * FStarC_Syntax_Syntax.qualifier Prims.list)
    Prims.list=
  match projectee with
  | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
      decls
let __proj__Mkeffects__item__order (projectee : effects) : edge Prims.list=
  match projectee with
  | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
      order
let __proj__Mkeffects__item__joins (projectee : effects) :
  (FStarC_Ident.lident * FStarC_Ident.lident * FStarC_Ident.lident * mlift *
    mlift) Prims.list=
  match projectee with
  | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
      joins
let __proj__Mkeffects__item__polymonadic_binds (projectee : effects) :
  (FStarC_Ident.lident * FStarC_Ident.lident * FStarC_Ident.lident *
    (env ->
       FStarC_Syntax_Syntax.comp_typ ->
         FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
           FStarC_Syntax_Syntax.comp_typ ->
             FStarC_Syntax_Syntax.cflag Prims.list ->
               FStarC_Range_Type.t ->
                 (FStarC_Syntax_Syntax.comp *
                   FStarC_TypeChecker_Common.guard_t)))
    Prims.list=
  match projectee with
  | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
      polymonadic_binds
let __proj__Mkeffects__item__polymonadic_subcomps (projectee : effects) :
  (FStarC_Ident.lident * FStarC_Ident.lident * FStarC_Syntax_Syntax.tscheme *
    FStarC_Syntax_Syntax.indexed_effect_combinator_kind) Prims.list=
  match projectee with
  | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
      polymonadic_subcomps
let __proj__Mkenv__item__solver (projectee : env) : solver_t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> solver
let __proj__Mkenv__item__range (projectee : env) : FStarC_Range_Type.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> range
let __proj__Mkenv__item__curmodule (projectee : env) : FStarC_Ident.lident=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> curmodule
let __proj__Mkenv__item__gamma (projectee : env) :
  FStarC_Syntax_Syntax.binding Prims.list=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> gamma
let __proj__Mkenv__item__gamma_sig (projectee : env) :
  sig_binding Prims.list=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> gamma_sig
let __proj__Mkenv__item__gamma_cache (projectee : env) :
  cached_elt FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> gamma_cache
let __proj__Mkenv__item__modules (projectee : env) :
  FStarC_Syntax_Syntax.modul Prims.list=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> modules
let __proj__Mkenv__item__expected_typ (projectee : env) :
  (FStarC_Syntax_Syntax.typ * Prims.bool) FStar_Pervasives_Native.option=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> expected_typ
let __proj__Mkenv__item__sigtab (projectee : env) :
  FStarC_Syntax_Syntax.sigelt FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> sigtab
let __proj__Mkenv__item__attrtab (projectee : env) :
  FStarC_Syntax_Syntax.sigelt Prims.list FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> attrtab
let __proj__Mkenv__item__instantiate_imp (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> instantiate_imp
let __proj__Mkenv__item__effects (projectee : env) : effects=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> effects1
let __proj__Mkenv__item__generalize (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> generalize
let __proj__Mkenv__item__letrecs (projectee : env) :
  (FStarC_Syntax_Syntax.lbname * Prims.int * FStarC_Syntax_Syntax.typ *
    FStarC_Syntax_Syntax.univ_names) Prims.list=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> letrecs
let __proj__Mkenv__item__top_level (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> top_level
let __proj__Mkenv__item__check_uvars (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> check_uvars
let __proj__Mkenv__item__use_eq_strict (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> use_eq_strict
let __proj__Mkenv__item__is_iface (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> is_iface
let __proj__Mkenv__item__admit (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> admit
let __proj__Mkenv__item__phase1 (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> phase1
let __proj__Mkenv__item__failhard (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> failhard
let __proj__Mkenv__item__flychecking (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> flychecking
let __proj__Mkenv__item__uvar_subtyping (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> uvar_subtyping
let __proj__Mkenv__item__intactics (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> intactics
let __proj__Mkenv__item__nocoerce (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> nocoerce
let __proj__Mkenv__item__tc_term (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
        FStarC_TypeChecker_Common.guard_t)=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> tc_term
let __proj__Mkenv__item__typeof_tot_or_gtot_term (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.term ->
      must_tot ->
        (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ *
          FStarC_TypeChecker_Common.guard_t)=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> typeof_tot_or_gtot_term
let __proj__Mkenv__item__universe_of (projectee : env) :
  env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.universe=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> universe_of
let __proj__Mkenv__item__typeof_well_typed_tot_or_gtot_term (projectee : env)
  :
  env ->
    FStarC_Syntax_Syntax.term ->
      must_tot ->
        (FStarC_Syntax_Syntax.typ * FStarC_TypeChecker_Common.guard_t)=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> typeof_well_typed_tot_or_gtot_term
let __proj__Mkenv__item__teq_nosmt_force (projectee : env) :
  env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> teq_nosmt_force
let __proj__Mkenv__item__subtype_nosmt_force (projectee : env) :
  env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> subtype_nosmt_force
let __proj__Mkenv__item__qtbl_name_and_index (projectee : env) :
  ((FStarC_Ident.lident * FStarC_Syntax_Syntax.typ * Prims.int)
    FStar_Pervasives_Native.option * Prims.int FStarC_SMap.t)=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> qtbl_name_and_index
let __proj__Mkenv__item__normalized_eff_names (projectee : env) :
  FStarC_Ident.lident FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> normalized_eff_names
let __proj__Mkenv__item__fv_delta_depths (projectee : env) :
  FStarC_Syntax_Syntax.delta_depth FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> fv_delta_depths
let __proj__Mkenv__item__proof_ns (projectee : env) : proof_namespace=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> proof_ns
let __proj__Mkenv__item__synth_hook (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Range_Type.t -> FStarC_Syntax_Syntax.term=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> synth_hook
let __proj__Mkenv__item__try_solve_implicits_hook (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.term -> FStarC_TypeChecker_Common.implicits -> unit=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> try_solve_implicits_hook
let __proj__Mkenv__item__splice (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.qualifier Prims.list ->
      FStarC_Syntax_Syntax.attribute Prims.list ->
        Prims.bool ->
          FStarC_Ident.lident Prims.list ->
            FStarC_Syntax_Syntax.term ->
              FStarC_Range_Type.t -> FStarC_Syntax_Syntax.sigelt Prims.list=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> splice
let __proj__Mkenv__item__mpreprocess (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> mpreprocess
let __proj__Mkenv__item__postprocess (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> postprocess
let __proj__Mkenv__item__identifier_info (projectee : env) :
  FStarC_TypeChecker_Common.id_info_table FStarC_Effect.ref=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> identifier_info
let __proj__Mkenv__item__tc_hooks (projectee : env) : tcenv_hooks=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> tc_hooks
let __proj__Mkenv__item__dsenv (projectee : env) : FStarC_Syntax_DsEnv.env=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> dsenv
let __proj__Mkenv__item__nbe (projectee : env) :
  step Prims.list ->
    env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> nbe
let __proj__Mkenv__item__strict_args_tab (projectee : env) :
  Prims.int Prims.list FStar_Pervasives_Native.option FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> strict_args_tab
let __proj__Mkenv__item__erasable_types_tab (projectee : env) :
  Prims.bool FStarC_SMap.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> erasable_types_tab
let __proj__Mkenv__item__enable_defer_to_tac (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> enable_defer_to_tac
let __proj__Mkenv__item__unif_allow_ref_guards (projectee : env) :
  Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> unif_allow_ref_guards
let __proj__Mkenv__item__erase_erasable_args (projectee : env) : Prims.bool=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> erase_erasable_args
let __proj__Mkenv__item__core_check (projectee : env) :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        Prims.bool ->
          ((FStarC_Syntax_Syntax.typ * (unit -> unit))
             FStar_Pervasives_Native.option,
            Prims.bool -> Prims.string) FStar_Pervasives.either=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> core_check
let __proj__Mkenv__item__missing_decl (projectee : env) :
  FStarC_Ident.lident FStarC_RBSet.t=
  match projectee with
  | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
      expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
      generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
      admit; phase1; failhard; flychecking; uvar_subtyping; intactics;
      nocoerce; tc_term; typeof_tot_or_gtot_term; universe_of;
      typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
      subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
      fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
      splice; mpreprocess; postprocess; identifier_info; tc_hooks; dsenv;
      nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
      unif_allow_ref_guards; erase_erasable_args; core_check; missing_decl;_}
      -> missing_decl
let __proj__Mksolver_t__item__init (projectee : solver_t) : env -> unit=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> init
let __proj__Mksolver_t__item__snapshot (projectee : solver_t) :
  Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> snapshot
let __proj__Mksolver_t__item__rollback (projectee : solver_t) :
  Prims.string ->
    (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      unit=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> rollback
let __proj__Mksolver_t__item__encode_sig (projectee : solver_t) :
  env -> FStarC_Syntax_Syntax.sigelt -> unit=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> encode_sig
let __proj__Mksolver_t__item__preprocess (projectee : solver_t) :
  env ->
    goal ->
      (Prims.bool * (env * goal * FStarC_Options.optionstate) Prims.list)=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> preprocess
let __proj__Mksolver_t__item__spinoff_strictly_positive_goals
  (projectee : solver_t) :
  (env -> goal -> (env * goal) Prims.list) FStar_Pervasives_Native.option=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> spinoff_strictly_positive_goals
let __proj__Mksolver_t__item__handle_smt_goal (projectee : solver_t) :
  env -> goal -> (env * goal) Prims.list=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> handle_smt_goal
let __proj__Mksolver_t__item__solve (projectee : solver_t) :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    env -> goal -> unit=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> solve
let __proj__Mksolver_t__item__solve_sync (projectee : solver_t) :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    env -> goal -> Prims.bool=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> solve_sync
let __proj__Mksolver_t__item__finish (projectee : solver_t) : unit -> unit=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> finish
let __proj__Mksolver_t__item__refresh (projectee : solver_t) :
  proof_namespace FStar_Pervasives_Native.option -> unit=
  match projectee with
  | { init; snapshot; rollback; encode_sig; preprocess;
      spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
      finish; refresh;_} -> refresh
let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook
  (projectee : tcenv_hooks) :
  env ->
    (FStarC_Syntax_Syntax.binding, sig_binding) FStar_Pervasives.either ->
      unit=
  match projectee with | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
type lift_comp_t =
  env ->
    FStarC_Syntax_Syntax.comp ->
      (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Common.guard_t)
type polymonadic_bind_t =
  env ->
    FStarC_Syntax_Syntax.comp_typ ->
      FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStarC_Syntax_Syntax.comp_typ ->
          FStarC_Syntax_Syntax.cflag Prims.list ->
            FStarC_Range_Type.t ->
              (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Common.guard_t)
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type core_check_t =
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        Prims.bool ->
          ((FStarC_Syntax_Syntax.typ * (unit -> unit))
             FStar_Pervasives_Native.option,
            Prims.bool -> Prims.string) FStar_Pervasives.either
type splice_t =
  env ->
    FStarC_Syntax_Syntax.qualifier Prims.list ->
      FStarC_Syntax_Syntax.attribute Prims.list ->
        Prims.bool ->
          FStarC_Ident.lident Prims.list ->
            FStarC_Syntax_Syntax.term ->
              FStarC_Range_Type.t -> FStarC_Syntax_Syntax.sigelt Prims.list
let preprocess (env1 : env) (tau : FStarC_Syntax_Syntax.term)
  (tm : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  env1.mpreprocess env1 tau tm
let postprocess (env1 : env) (tau : FStarC_Syntax_Syntax.term)
  (ty : FStarC_Syntax_Syntax.typ) (tm : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term= env1.postprocess env1 tau ty tm
let rename_gamma (subst : FStarC_Syntax_Syntax.subst_t)
  (gamma : FStarC_Syntax_Syntax.gamma) : FStarC_Syntax_Syntax.gamma=
  FStarC_List.map
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.Binding_var x ->
           let y =
             let uu___1 = FStarC_Syntax_Syntax.bv_to_name x in
             FStarC_Syntax_Subst.subst subst uu___1 in
           let uu___1 =
             let uu___2 = FStarC_Syntax_Subst.compress y in
             uu___2.FStarC_Syntax_Syntax.n in
           (match uu___1 with
            | FStarC_Syntax_Syntax.Tm_name y1 ->
                let uu___2 =
                  let uu___3 =
                    FStarC_Syntax_Subst.subst subst
                      x.FStarC_Syntax_Syntax.sort in
                  {
                    FStarC_Syntax_Syntax.ppname =
                      (y1.FStarC_Syntax_Syntax.ppname);
                    FStarC_Syntax_Syntax.index =
                      (y1.FStarC_Syntax_Syntax.index);
                    FStarC_Syntax_Syntax.sort = uu___3
                  } in
                FStarC_Syntax_Syntax.Binding_var uu___2
            | uu___2 -> failwith "Not a renaming")
       | b -> b) gamma
let rename_env (subst : FStarC_Syntax_Syntax.subst_t) (env1 : env) : 
  env=
  let uu___ = rename_gamma subst env1.gamma in
  {
    solver = (env1.solver);
    range = (env1.range);
    curmodule = (env1.curmodule);
    gamma = uu___;
    gamma_sig = (env1.gamma_sig);
    gamma_cache = (env1.gamma_cache);
    modules = (env1.modules);
    expected_typ = (env1.expected_typ);
    sigtab = (env1.sigtab);
    attrtab = (env1.attrtab);
    instantiate_imp = (env1.instantiate_imp);
    effects = (env1.effects);
    generalize = (env1.generalize);
    letrecs = (env1.letrecs);
    top_level = (env1.top_level);
    check_uvars = (env1.check_uvars);
    use_eq_strict = (env1.use_eq_strict);
    is_iface = (env1.is_iface);
    admit = (env1.admit);
    phase1 = (env1.phase1);
    failhard = (env1.failhard);
    flychecking = (env1.flychecking);
    uvar_subtyping = (env1.uvar_subtyping);
    intactics = (env1.intactics);
    nocoerce = (env1.nocoerce);
    tc_term = (env1.tc_term);
    typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
    universe_of = (env1.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env1.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env1.teq_nosmt_force);
    subtype_nosmt_force = (env1.subtype_nosmt_force);
    qtbl_name_and_index = (env1.qtbl_name_and_index);
    normalized_eff_names = (env1.normalized_eff_names);
    fv_delta_depths = (env1.fv_delta_depths);
    proof_ns = (env1.proof_ns);
    synth_hook = (env1.synth_hook);
    try_solve_implicits_hook = (env1.try_solve_implicits_hook);
    splice = (env1.splice);
    mpreprocess = (env1.mpreprocess);
    postprocess = (env1.postprocess);
    identifier_info = (env1.identifier_info);
    tc_hooks = (env1.tc_hooks);
    dsenv = (env1.dsenv);
    nbe = (env1.nbe);
    strict_args_tab = (env1.strict_args_tab);
    erasable_types_tab = (env1.erasable_types_tab);
    enable_defer_to_tac = (env1.enable_defer_to_tac);
    unif_allow_ref_guards = (env1.unif_allow_ref_guards);
    erase_erasable_args = (env1.erase_erasable_args);
    core_check = (env1.core_check);
    missing_decl = (env1.missing_decl)
  }
let default_tc_hooks : tcenv_hooks=
  { tc_push_in_gamma_hook = (fun uu___ uu___1 -> ()) }
let tc_hooks (env1 : env) : tcenv_hooks= env1.tc_hooks
let set_tc_hooks (env1 : env) (hooks : tcenv_hooks) : env=
  {
    solver = (env1.solver);
    range = (env1.range);
    curmodule = (env1.curmodule);
    gamma = (env1.gamma);
    gamma_sig = (env1.gamma_sig);
    gamma_cache = (env1.gamma_cache);
    modules = (env1.modules);
    expected_typ = (env1.expected_typ);
    sigtab = (env1.sigtab);
    attrtab = (env1.attrtab);
    instantiate_imp = (env1.instantiate_imp);
    effects = (env1.effects);
    generalize = (env1.generalize);
    letrecs = (env1.letrecs);
    top_level = (env1.top_level);
    check_uvars = (env1.check_uvars);
    use_eq_strict = (env1.use_eq_strict);
    is_iface = (env1.is_iface);
    admit = (env1.admit);
    phase1 = (env1.phase1);
    failhard = (env1.failhard);
    flychecking = (env1.flychecking);
    uvar_subtyping = (env1.uvar_subtyping);
    intactics = (env1.intactics);
    nocoerce = (env1.nocoerce);
    tc_term = (env1.tc_term);
    typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
    universe_of = (env1.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env1.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env1.teq_nosmt_force);
    subtype_nosmt_force = (env1.subtype_nosmt_force);
    qtbl_name_and_index = (env1.qtbl_name_and_index);
    normalized_eff_names = (env1.normalized_eff_names);
    fv_delta_depths = (env1.fv_delta_depths);
    proof_ns = (env1.proof_ns);
    synth_hook = (env1.synth_hook);
    try_solve_implicits_hook = (env1.try_solve_implicits_hook);
    splice = (env1.splice);
    mpreprocess = (env1.mpreprocess);
    postprocess = (env1.postprocess);
    identifier_info = (env1.identifier_info);
    tc_hooks = hooks;
    dsenv = (env1.dsenv);
    nbe = (env1.nbe);
    strict_args_tab = (env1.strict_args_tab);
    erasable_types_tab = (env1.erasable_types_tab);
    enable_defer_to_tac = (env1.enable_defer_to_tac);
    unif_allow_ref_guards = (env1.unif_allow_ref_guards);
    erase_erasable_args = (env1.erase_erasable_args);
    core_check = (env1.core_check);
    missing_decl = (env1.missing_decl)
  }
let set_dep_graph (e : env) (g : FStarC_Parser_Dep.deps) : env=
  let uu___ = FStarC_Syntax_DsEnv.set_dep_graph e.dsenv g in
  {
    solver = (e.solver);
    range = (e.range);
    curmodule = (e.curmodule);
    gamma = (e.gamma);
    gamma_sig = (e.gamma_sig);
    gamma_cache = (e.gamma_cache);
    modules = (e.modules);
    expected_typ = (e.expected_typ);
    sigtab = (e.sigtab);
    attrtab = (e.attrtab);
    instantiate_imp = (e.instantiate_imp);
    effects = (e.effects);
    generalize = (e.generalize);
    letrecs = (e.letrecs);
    top_level = (e.top_level);
    check_uvars = (e.check_uvars);
    use_eq_strict = (e.use_eq_strict);
    is_iface = (e.is_iface);
    admit = (e.admit);
    phase1 = (e.phase1);
    failhard = (e.failhard);
    flychecking = (e.flychecking);
    uvar_subtyping = (e.uvar_subtyping);
    intactics = (e.intactics);
    nocoerce = (e.nocoerce);
    tc_term = (e.tc_term);
    typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
    universe_of = (e.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (e.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (e.teq_nosmt_force);
    subtype_nosmt_force = (e.subtype_nosmt_force);
    qtbl_name_and_index = (e.qtbl_name_and_index);
    normalized_eff_names = (e.normalized_eff_names);
    fv_delta_depths = (e.fv_delta_depths);
    proof_ns = (e.proof_ns);
    synth_hook = (e.synth_hook);
    try_solve_implicits_hook = (e.try_solve_implicits_hook);
    splice = (e.splice);
    mpreprocess = (e.mpreprocess);
    postprocess = (e.postprocess);
    identifier_info = (e.identifier_info);
    tc_hooks = (e.tc_hooks);
    dsenv = uu___;
    nbe = (e.nbe);
    strict_args_tab = (e.strict_args_tab);
    erasable_types_tab = (e.erasable_types_tab);
    enable_defer_to_tac = (e.enable_defer_to_tac);
    unif_allow_ref_guards = (e.unif_allow_ref_guards);
    erase_erasable_args = (e.erase_erasable_args);
    core_check = (e.core_check);
    missing_decl = (e.missing_decl)
  }
let dep_graph (e : env) : FStarC_Parser_Dep.deps=
  FStarC_Syntax_DsEnv.dep_graph e.dsenv
let with_restored_scope (e : env) (f : env -> ('a * env)) : ('a * env)=
  let env1 =
    {
      solver = (e.solver);
      range = (e.range);
      curmodule = (e.curmodule);
      gamma = [];
      gamma_sig = [];
      gamma_cache = (e.gamma_cache);
      modules = (e.modules);
      expected_typ = (e.expected_typ);
      sigtab = (e.sigtab);
      attrtab = (e.attrtab);
      instantiate_imp = (e.instantiate_imp);
      effects = (e.effects);
      generalize = (e.generalize);
      letrecs = (e.letrecs);
      top_level = (e.top_level);
      check_uvars = (e.check_uvars);
      use_eq_strict = (e.use_eq_strict);
      is_iface = (e.is_iface);
      admit = (e.admit);
      phase1 = (e.phase1);
      failhard = (e.failhard);
      flychecking = (e.flychecking);
      uvar_subtyping = (e.uvar_subtyping);
      intactics = (e.intactics);
      nocoerce = (e.nocoerce);
      tc_term = (e.tc_term);
      typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
      universe_of = (e.universe_of);
      typeof_well_typed_tot_or_gtot_term =
        (e.typeof_well_typed_tot_or_gtot_term);
      teq_nosmt_force = (e.teq_nosmt_force);
      subtype_nosmt_force = (e.subtype_nosmt_force);
      qtbl_name_and_index = (e.qtbl_name_and_index);
      normalized_eff_names = (e.normalized_eff_names);
      fv_delta_depths = (e.fv_delta_depths);
      proof_ns = [];
      synth_hook = (e.synth_hook);
      try_solve_implicits_hook = (e.try_solve_implicits_hook);
      splice = (e.splice);
      mpreprocess = (e.mpreprocess);
      postprocess = (e.postprocess);
      identifier_info = (e.identifier_info);
      tc_hooks = (e.tc_hooks);
      dsenv = (e.dsenv);
      nbe = (e.nbe);
      strict_args_tab = (e.strict_args_tab);
      erasable_types_tab = (e.erasable_types_tab);
      enable_defer_to_tac = (e.enable_defer_to_tac);
      unif_allow_ref_guards = (e.unif_allow_ref_guards);
      erase_erasable_args = (e.erase_erasable_args);
      core_check = (e.core_check);
      missing_decl = (e.missing_decl)
    } in
  (env1.solver).refresh FStar_Pervasives_Native.None;
  (let uu___1 =
     FStarC_Options.with_restored_cmd_line_options
       (fun uu___2 ->
          let uu___3 =
            FStarC_Syntax_DsEnv.with_restored_scope env1.dsenv
              (fun dsenv ->
                 let uu___4 = f env1 in
                 match uu___4 with
                 | (res, env2) -> ((res, env2), (env2.dsenv))) in
          match uu___3 with
          | ((res, env2), dsenv) ->
              (res,
                {
                  solver = (env2.solver);
                  range = (env2.range);
                  curmodule = (e.curmodule);
                  gamma = (e.gamma);
                  gamma_sig = (e.gamma_sig);
                  gamma_cache = (env2.gamma_cache);
                  modules = (env2.modules);
                  expected_typ = (env2.expected_typ);
                  sigtab = (env2.sigtab);
                  attrtab = (env2.attrtab);
                  instantiate_imp = (env2.instantiate_imp);
                  effects = (env2.effects);
                  generalize = (env2.generalize);
                  letrecs = (env2.letrecs);
                  top_level = (env2.top_level);
                  check_uvars = (env2.check_uvars);
                  use_eq_strict = (env2.use_eq_strict);
                  is_iface = (e.is_iface);
                  admit = (e.admit);
                  phase1 = (env2.phase1);
                  failhard = (env2.failhard);
                  flychecking = (env2.flychecking);
                  uvar_subtyping = (env2.uvar_subtyping);
                  intactics = (env2.intactics);
                  nocoerce = (env2.nocoerce);
                  tc_term = (env2.tc_term);
                  typeof_tot_or_gtot_term = (env2.typeof_tot_or_gtot_term);
                  universe_of = (env2.universe_of);
                  typeof_well_typed_tot_or_gtot_term =
                    (env2.typeof_well_typed_tot_or_gtot_term);
                  teq_nosmt_force = (env2.teq_nosmt_force);
                  subtype_nosmt_force = (env2.subtype_nosmt_force);
                  qtbl_name_and_index = (env2.qtbl_name_and_index);
                  normalized_eff_names = (env2.normalized_eff_names);
                  fv_delta_depths = (env2.fv_delta_depths);
                  proof_ns = (e.proof_ns);
                  synth_hook = (env2.synth_hook);
                  try_solve_implicits_hook = (env2.try_solve_implicits_hook);
                  splice = (env2.splice);
                  mpreprocess = (env2.mpreprocess);
                  postprocess = (env2.postprocess);
                  identifier_info = (env2.identifier_info);
                  tc_hooks = (env2.tc_hooks);
                  dsenv;
                  nbe = (env2.nbe);
                  strict_args_tab = (env2.strict_args_tab);
                  erasable_types_tab = (env2.erasable_types_tab);
                  enable_defer_to_tac = (env2.enable_defer_to_tac);
                  unif_allow_ref_guards = (env2.unif_allow_ref_guards);
                  erase_erasable_args = (env2.erase_erasable_args);
                  core_check = (env2.core_check);
                  missing_decl = (env2.missing_decl)
                })) in
   match uu___1 with
   | (res, env2) ->
       ((env2.solver).refresh (FStar_Pervasives_Native.Some (env2.proof_ns));
        (res, env2)))
let record_val_for (e : env) (l : FStarC_Ident.lident) : env=
  let uu___ =
    Obj.magic
      (FStarC_Class_Setlike.add ()
         (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv))
         l (Obj.magic e.missing_decl)) in
  {
    solver = (e.solver);
    range = (e.range);
    curmodule = (e.curmodule);
    gamma = (e.gamma);
    gamma_sig = (e.gamma_sig);
    gamma_cache = (e.gamma_cache);
    modules = (e.modules);
    expected_typ = (e.expected_typ);
    sigtab = (e.sigtab);
    attrtab = (e.attrtab);
    instantiate_imp = (e.instantiate_imp);
    effects = (e.effects);
    generalize = (e.generalize);
    letrecs = (e.letrecs);
    top_level = (e.top_level);
    check_uvars = (e.check_uvars);
    use_eq_strict = (e.use_eq_strict);
    is_iface = (e.is_iface);
    admit = (e.admit);
    phase1 = (e.phase1);
    failhard = (e.failhard);
    flychecking = (e.flychecking);
    uvar_subtyping = (e.uvar_subtyping);
    intactics = (e.intactics);
    nocoerce = (e.nocoerce);
    tc_term = (e.tc_term);
    typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
    universe_of = (e.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (e.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (e.teq_nosmt_force);
    subtype_nosmt_force = (e.subtype_nosmt_force);
    qtbl_name_and_index = (e.qtbl_name_and_index);
    normalized_eff_names = (e.normalized_eff_names);
    fv_delta_depths = (e.fv_delta_depths);
    proof_ns = (e.proof_ns);
    synth_hook = (e.synth_hook);
    try_solve_implicits_hook = (e.try_solve_implicits_hook);
    splice = (e.splice);
    mpreprocess = (e.mpreprocess);
    postprocess = (e.postprocess);
    identifier_info = (e.identifier_info);
    tc_hooks = (e.tc_hooks);
    dsenv = (e.dsenv);
    nbe = (e.nbe);
    strict_args_tab = (e.strict_args_tab);
    erasable_types_tab = (e.erasable_types_tab);
    enable_defer_to_tac = (e.enable_defer_to_tac);
    unif_allow_ref_guards = (e.unif_allow_ref_guards);
    erase_erasable_args = (e.erase_erasable_args);
    core_check = (e.core_check);
    missing_decl = uu___
  }
let record_definition_for (e : env) (l : FStarC_Ident.lident) : env=
  let uu___ =
    Obj.magic
      (FStarC_Class_Setlike.remove ()
         (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv))
         l (Obj.magic e.missing_decl)) in
  {
    solver = (e.solver);
    range = (e.range);
    curmodule = (e.curmodule);
    gamma = (e.gamma);
    gamma_sig = (e.gamma_sig);
    gamma_cache = (e.gamma_cache);
    modules = (e.modules);
    expected_typ = (e.expected_typ);
    sigtab = (e.sigtab);
    attrtab = (e.attrtab);
    instantiate_imp = (e.instantiate_imp);
    effects = (e.effects);
    generalize = (e.generalize);
    letrecs = (e.letrecs);
    top_level = (e.top_level);
    check_uvars = (e.check_uvars);
    use_eq_strict = (e.use_eq_strict);
    is_iface = (e.is_iface);
    admit = (e.admit);
    phase1 = (e.phase1);
    failhard = (e.failhard);
    flychecking = (e.flychecking);
    uvar_subtyping = (e.uvar_subtyping);
    intactics = (e.intactics);
    nocoerce = (e.nocoerce);
    tc_term = (e.tc_term);
    typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
    universe_of = (e.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (e.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (e.teq_nosmt_force);
    subtype_nosmt_force = (e.subtype_nosmt_force);
    qtbl_name_and_index = (e.qtbl_name_and_index);
    normalized_eff_names = (e.normalized_eff_names);
    fv_delta_depths = (e.fv_delta_depths);
    proof_ns = (e.proof_ns);
    synth_hook = (e.synth_hook);
    try_solve_implicits_hook = (e.try_solve_implicits_hook);
    splice = (e.splice);
    mpreprocess = (e.mpreprocess);
    postprocess = (e.postprocess);
    identifier_info = (e.identifier_info);
    tc_hooks = (e.tc_hooks);
    dsenv = (e.dsenv);
    nbe = (e.nbe);
    strict_args_tab = (e.strict_args_tab);
    erasable_types_tab = (e.erasable_types_tab);
    enable_defer_to_tac = (e.enable_defer_to_tac);
    unif_allow_ref_guards = (e.unif_allow_ref_guards);
    erase_erasable_args = (e.erase_erasable_args);
    core_check = (e.core_check);
    missing_decl = uu___
  }
let missing_definition_list (e : env) : FStarC_Ident.lident Prims.list=
  FStarC_Class_Setlike.elems ()
    (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv))
    (Obj.magic e.missing_decl)
type implicit = FStarC_TypeChecker_Common.implicit
type implicits = FStarC_TypeChecker_Common.implicits
type guard_t = FStarC_TypeChecker_Common.guard_t
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
type qninfo =
  (((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ),
    (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Pervasives.either * FStarC_Range_Type.t)
    FStar_Pervasives_Native.option
type env_t = env
type sigtable = FStarC_Syntax_Syntax.sigelt FStarC_SMap.t
let should_verify (env1 : env) : Prims.bool=
  ((let uu___ = FStarC_Options.lax () in Prims.op_Negation uu___) &&
     (Prims.op_Negation env1.admit))
    &&
    (let uu___ = FStarC_Ident.string_of_lid env1.curmodule in
     FStarC_Options.should_verify uu___)
let visible_at (d : delta_level) (q : FStarC_Syntax_Syntax.qualifier) :
  Prims.bool=
  match (d, q) with
  | (NoDelta, uu___) -> true
  | (Eager_unfolding_only,
     FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
  | (Unfold uu___, FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen) ->
      true
  | (Unfold uu___, FStarC_Syntax_Syntax.Visible_default) -> true
  | (InliningDelta, FStarC_Syntax_Syntax.Inline_for_extraction) -> true
  | uu___ -> false
let default_table_size : Prims.int= (Prims.of_int (200))
let new_sigtab (uu___ : unit) : 'uuuuu FStarC_SMap.t=
  FStarC_SMap.create default_table_size
let new_gamma_cache (uu___ : unit) : 'uuuuu FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (100))
let initial_env (deps : FStarC_Parser_Dep.deps)
  (tc_term :
    env ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
          guard_t))
  (typeof_tot_or_gtot_term :
    env ->
      FStarC_Syntax_Syntax.term ->
        must_tot ->
          (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ * guard_t))
  (typeof_tot_or_gtot_term_fastpath :
    env ->
      FStarC_Syntax_Syntax.term ->
        must_tot -> FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  (universe_of :
    env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.universe)
  (teq_nosmt_force :
    env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool)
  (subtype_nosmt_force :
    env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool)
  (solver : solver_t) (module_lid : FStarC_Ident.lident)
  (nbe :
    step Prims.list ->
      env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  (core_check : core_check_t) : env=
  let uu___ = new_gamma_cache () in
  let uu___1 = new_sigtab () in
  let uu___2 = new_sigtab () in
  let uu___3 =
    let uu___4 = FStarC_SMap.create (Prims.of_int (10)) in
    (FStar_Pervasives_Native.None, uu___4) in
  let uu___4 = FStarC_SMap.create (Prims.of_int (20)) in
  let uu___5 = FStarC_SMap.create (Prims.of_int (50)) in
  let uu___6 = FStarC_Options.using_facts_from () in
  let uu___7 =
    FStarC_Effect.mk_ref FStarC_TypeChecker_Common.id_info_table_empty in
  let uu___8 =
    let uu___9 = FStarC_Syntax_DsEnv.empty_env deps in
    FStarC_Syntax_DsEnv.set_current_module uu___9 module_lid in
  let uu___9 = FStarC_SMap.create (Prims.of_int (20)) in
  let uu___10 = FStarC_SMap.create (Prims.of_int (20)) in
  let uu___11 =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv))
         ()) in
  {
    solver;
    range = FStarC_Range_Type.dummyRange;
    curmodule = module_lid;
    gamma = [];
    gamma_sig = [];
    gamma_cache = uu___;
    modules = [];
    expected_typ = FStar_Pervasives_Native.None;
    sigtab = uu___1;
    attrtab = uu___2;
    instantiate_imp = true;
    effects =
      {
        decls = [];
        order = [];
        joins = [];
        polymonadic_binds = [];
        polymonadic_subcomps = []
      };
    generalize = true;
    letrecs = [];
    top_level = false;
    check_uvars = false;
    use_eq_strict = false;
    is_iface = false;
    admit = false;
    phase1 = false;
    failhard = false;
    flychecking = false;
    uvar_subtyping = true;
    intactics = false;
    nocoerce = false;
    tc_term;
    typeof_tot_or_gtot_term;
    universe_of;
    typeof_well_typed_tot_or_gtot_term =
      (fun env1 t must_tot1 ->
         let uu___12 = typeof_tot_or_gtot_term_fastpath env1 t must_tot1 in
         match uu___12 with
         | FStar_Pervasives_Native.Some k ->
             (k, FStarC_TypeChecker_Common.trivial_guard)
         | FStar_Pervasives_Native.None ->
             let uu___13 = typeof_tot_or_gtot_term env1 t must_tot1 in
             (match uu___13 with | (t', k, g) -> (k, g)));
    teq_nosmt_force;
    subtype_nosmt_force;
    qtbl_name_and_index = uu___3;
    normalized_eff_names = uu___4;
    fv_delta_depths = uu___5;
    proof_ns = uu___6;
    synth_hook = (fun e g tau rng -> failwith "no synthesizer available");
    try_solve_implicits_hook =
      (fun e tau imps -> failwith "no implicit hook available");
    splice =
      (fun e is_typed _quals _attrs lids tau range ->
         failwith "no splicer available");
    mpreprocess = (fun e tau tm -> failwith "no preprocessor available");
    postprocess = (fun e tau typ tm -> failwith "no postprocessor available");
    identifier_info = uu___7;
    tc_hooks = default_tc_hooks;
    dsenv = uu___8;
    nbe;
    strict_args_tab = uu___9;
    erasable_types_tab = uu___10;
    enable_defer_to_tac = true;
    unif_allow_ref_guards = false;
    erase_erasable_args = false;
    core_check;
    missing_decl = uu___11
  }
let dsenv (env1 : env) : FStarC_Syntax_DsEnv.env= env1.dsenv
let sigtab (env1 : env) : FStarC_Syntax_Syntax.sigelt FStarC_SMap.t=
  env1.sigtab
let attrtab (env1 : env) :
  FStarC_Syntax_Syntax.sigelt Prims.list FStarC_SMap.t= env1.attrtab
let gamma_cache (env1 : env) : cached_elt FStarC_SMap.t= env1.gamma_cache
let query_indices :
  (FStarC_Ident.lident * Prims.int) Prims.list Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref [[]]
let push_query_indices (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang query_indices in
  match uu___1 with
  | [] -> failwith "Empty query indices!"
  | uu___2 ->
      let uu___3 =
        let uu___4 =
          let uu___5 = FStarC_Effect.op_Bang query_indices in
          FStarC_List.hd uu___5 in
        let uu___5 = FStarC_Effect.op_Bang query_indices in uu___4 :: uu___5 in
      FStarC_Effect.op_Colon_Equals query_indices uu___3
let pop_query_indices (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang query_indices in
  match uu___1 with
  | [] -> failwith "Empty query indices!"
  | hd::tl -> FStarC_Effect.op_Colon_Equals query_indices tl
let snapshot_query_indices (uu___ : unit) : (Prims.int * unit)=
  FStarC_Common.snapshot "TcEnv.query_indices" push_query_indices
    query_indices ()
let rollback_query_indices (depth : Prims.int FStar_Pervasives_Native.option)
  : unit=
  FStarC_Common.rollback "TcEnv.query_indices" pop_query_indices
    query_indices depth
let add_query_index (uu___ : (FStarC_Ident.lident * Prims.int)) : unit=
  match uu___ with
  | (l, n) ->
      let uu___1 = FStarC_Effect.op_Bang query_indices in
      (match uu___1 with
       | hd::tl ->
           FStarC_Effect.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
       | uu___2 -> failwith "Empty query indices")
let peek_query_indices (uu___ : unit) :
  (FStarC_Ident.lident * Prims.int) Prims.list=
  let uu___1 = FStarC_Effect.op_Bang query_indices in FStarC_List.hd uu___1
let stack : env Prims.list FStarC_Effect.ref= FStarC_Effect.mk_ref []
let push_stack (env1 : env) : env=
  (let uu___1 = let uu___2 = FStarC_Effect.op_Bang stack in env1 :: uu___2 in
   FStarC_Effect.op_Colon_Equals stack uu___1);
  (let uu___1 = FStarC_SMap.copy (gamma_cache env1) in
   let uu___2 = FStarC_SMap.copy (sigtab env1) in
   let uu___3 = FStarC_SMap.copy (attrtab env1) in
   let uu___4 =
     let uu___5 =
       FStarC_SMap.copy
         (FStar_Pervasives_Native.snd env1.qtbl_name_and_index) in
     ((FStar_Pervasives_Native.fst env1.qtbl_name_and_index), uu___5) in
   let uu___5 = FStarC_SMap.copy env1.normalized_eff_names in
   let uu___6 = FStarC_SMap.copy env1.fv_delta_depths in
   let uu___7 =
     let uu___8 = FStarC_Effect.op_Bang env1.identifier_info in
     FStarC_Effect.mk_ref uu___8 in
   let uu___8 = FStarC_SMap.copy env1.strict_args_tab in
   let uu___9 = FStarC_SMap.copy env1.erasable_types_tab in
   {
     solver = (env1.solver);
     range = (env1.range);
     curmodule = (env1.curmodule);
     gamma = (env1.gamma);
     gamma_sig = (env1.gamma_sig);
     gamma_cache = uu___1;
     modules = (env1.modules);
     expected_typ = (env1.expected_typ);
     sigtab = uu___2;
     attrtab = uu___3;
     instantiate_imp = (env1.instantiate_imp);
     effects = (env1.effects);
     generalize = (env1.generalize);
     letrecs = (env1.letrecs);
     top_level = (env1.top_level);
     check_uvars = (env1.check_uvars);
     use_eq_strict = (env1.use_eq_strict);
     is_iface = (env1.is_iface);
     admit = (env1.admit);
     phase1 = (env1.phase1);
     failhard = (env1.failhard);
     flychecking = (env1.flychecking);
     uvar_subtyping = (env1.uvar_subtyping);
     intactics = (env1.intactics);
     nocoerce = (env1.nocoerce);
     tc_term = (env1.tc_term);
     typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
     universe_of = (env1.universe_of);
     typeof_well_typed_tot_or_gtot_term =
       (env1.typeof_well_typed_tot_or_gtot_term);
     teq_nosmt_force = (env1.teq_nosmt_force);
     subtype_nosmt_force = (env1.subtype_nosmt_force);
     qtbl_name_and_index = uu___4;
     normalized_eff_names = uu___5;
     fv_delta_depths = uu___6;
     proof_ns = (env1.proof_ns);
     synth_hook = (env1.synth_hook);
     try_solve_implicits_hook = (env1.try_solve_implicits_hook);
     splice = (env1.splice);
     mpreprocess = (env1.mpreprocess);
     postprocess = (env1.postprocess);
     identifier_info = uu___7;
     tc_hooks = (env1.tc_hooks);
     dsenv = (env1.dsenv);
     nbe = (env1.nbe);
     strict_args_tab = uu___8;
     erasable_types_tab = uu___9;
     enable_defer_to_tac = (env1.enable_defer_to_tac);
     unif_allow_ref_guards = (env1.unif_allow_ref_guards);
     erase_erasable_args = (env1.erase_erasable_args);
     core_check = (env1.core_check);
     missing_decl = (env1.missing_decl)
   })
let pop_stack (uu___ : unit) : env=
  let uu___1 = FStarC_Effect.op_Bang stack in
  match uu___1 with
  | env1::tl -> (FStarC_Effect.op_Colon_Equals stack tl; env1)
  | uu___2 -> failwith "Impossible: Too many pops"
let snapshot_stack (env1 : env) : (Prims.int * env)=
  FStarC_Common.snapshot "TcEnv.stack" push_stack stack env1
let rollback_stack (depth : Prims.int FStar_Pervasives_Native.option) : 
  env= FStarC_Common.rollback "TcEnv.stack" pop_stack stack depth
let snapshot (env1 : env) (msg : Prims.string) : (tcenv_depth_t * env)=
  FStarC_Util.atomically
    (fun uu___ ->
       let uu___1 = snapshot_stack env1 in
       match uu___1 with
       | (stack_depth, env2) ->
           let uu___2 = snapshot_query_indices () in
           (match uu___2 with
            | (query_indices_depth, ()) ->
                let uu___3 = (env2.solver).snapshot msg in
                (match uu___3 with
                 | (solver_depth, ()) ->
                     let uu___4 = FStarC_Syntax_DsEnv.snapshot env2.dsenv in
                     (match uu___4 with
                      | (dsenv_depth, dsenv1) ->
                          ((stack_depth, query_indices_depth, solver_depth,
                             dsenv_depth),
                            {
                              solver = (env2.solver);
                              range = (env2.range);
                              curmodule = (env2.curmodule);
                              gamma = (env2.gamma);
                              gamma_sig = (env2.gamma_sig);
                              gamma_cache = (env2.gamma_cache);
                              modules = (env2.modules);
                              expected_typ = (env2.expected_typ);
                              sigtab = (env2.sigtab);
                              attrtab = (env2.attrtab);
                              instantiate_imp = (env2.instantiate_imp);
                              effects = (env2.effects);
                              generalize = (env2.generalize);
                              letrecs = (env2.letrecs);
                              top_level = (env2.top_level);
                              check_uvars = (env2.check_uvars);
                              use_eq_strict = (env2.use_eq_strict);
                              is_iface = (env2.is_iface);
                              admit = (env2.admit);
                              phase1 = (env2.phase1);
                              failhard = (env2.failhard);
                              flychecking = (env2.flychecking);
                              uvar_subtyping = (env2.uvar_subtyping);
                              intactics = (env2.intactics);
                              nocoerce = (env2.nocoerce);
                              tc_term = (env2.tc_term);
                              typeof_tot_or_gtot_term =
                                (env2.typeof_tot_or_gtot_term);
                              universe_of = (env2.universe_of);
                              typeof_well_typed_tot_or_gtot_term =
                                (env2.typeof_well_typed_tot_or_gtot_term);
                              teq_nosmt_force = (env2.teq_nosmt_force);
                              subtype_nosmt_force =
                                (env2.subtype_nosmt_force);
                              qtbl_name_and_index =
                                (env2.qtbl_name_and_index);
                              normalized_eff_names =
                                (env2.normalized_eff_names);
                              fv_delta_depths = (env2.fv_delta_depths);
                              proof_ns = (env2.proof_ns);
                              synth_hook = (env2.synth_hook);
                              try_solve_implicits_hook =
                                (env2.try_solve_implicits_hook);
                              splice = (env2.splice);
                              mpreprocess = (env2.mpreprocess);
                              postprocess = (env2.postprocess);
                              identifier_info = (env2.identifier_info);
                              tc_hooks = (env2.tc_hooks);
                              dsenv = dsenv1;
                              nbe = (env2.nbe);
                              strict_args_tab = (env2.strict_args_tab);
                              erasable_types_tab = (env2.erasable_types_tab);
                              enable_defer_to_tac =
                                (env2.enable_defer_to_tac);
                              unif_allow_ref_guards =
                                (env2.unif_allow_ref_guards);
                              erase_erasable_args =
                                (env2.erase_erasable_args);
                              core_check = (env2.core_check);
                              missing_decl = (env2.missing_decl)
                            })))))
let rollback (solver : solver_t) (msg : Prims.string)
  (depth : tcenv_depth_t FStar_Pervasives_Native.option) : env=
  FStarC_Util.atomically
    (fun uu___ ->
       let uu___1 =
         match depth with
         | FStar_Pervasives_Native.Some (s1, s2, s3, s4) ->
             ((FStar_Pervasives_Native.Some s1),
               (FStar_Pervasives_Native.Some s2),
               (FStar_Pervasives_Native.Some s3),
               (FStar_Pervasives_Native.Some s4))
         | FStar_Pervasives_Native.None ->
             (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
               FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
       match uu___1 with
       | (stack_depth, query_indices_depth, solver_depth, dsenv_depth) ->
           (solver.rollback msg solver_depth;
            (match () with
             | () ->
                 (rollback_query_indices query_indices_depth;
                  (match () with
                   | () ->
                       let tcenv = rollback_stack stack_depth in
                       let dsenv1 = FStarC_Syntax_DsEnv.rollback dsenv_depth in
                       ((let uu___5 =
                           FStarC_Util.physical_equality tcenv.dsenv dsenv1 in
                         FStarC_Common.runtime_assert uu___5
                           "Inconsistent stack state");
                        tcenv))))))
let push (env1 : env) (msg : Prims.string) : env=
  let uu___ = snapshot env1 msg in FStar_Pervasives_Native.snd uu___
let pop (env1 : env) (msg : Prims.string) : env=
  rollback env1.solver msg FStar_Pervasives_Native.None
let incr_query_index (env1 : env) : env=
  let qix = peek_query_indices () in
  match env1.qtbl_name_and_index with
  | (FStar_Pervasives_Native.None, uu___) -> env1
  | (FStar_Pervasives_Native.Some (l, typ, n), tbl) ->
      let uu___ =
        FStarC_List.tryFind
          (fun uu___1 ->
             match uu___1 with | (m, uu___2) -> FStarC_Ident.lid_equals l m)
          qix in
      (match uu___ with
       | FStar_Pervasives_Native.None ->
           let next = n + Prims.int_one in
           (add_query_index (l, next);
            (let uu___3 = FStarC_Ident.string_of_lid l in
             FStarC_SMap.add tbl uu___3 next);
            {
              solver = (env1.solver);
              range = (env1.range);
              curmodule = (env1.curmodule);
              gamma = (env1.gamma);
              gamma_sig = (env1.gamma_sig);
              gamma_cache = (env1.gamma_cache);
              modules = (env1.modules);
              expected_typ = (env1.expected_typ);
              sigtab = (env1.sigtab);
              attrtab = (env1.attrtab);
              instantiate_imp = (env1.instantiate_imp);
              effects = (env1.effects);
              generalize = (env1.generalize);
              letrecs = (env1.letrecs);
              top_level = (env1.top_level);
              check_uvars = (env1.check_uvars);
              use_eq_strict = (env1.use_eq_strict);
              is_iface = (env1.is_iface);
              admit = (env1.admit);
              phase1 = (env1.phase1);
              failhard = (env1.failhard);
              flychecking = (env1.flychecking);
              uvar_subtyping = (env1.uvar_subtyping);
              intactics = (env1.intactics);
              nocoerce = (env1.nocoerce);
              tc_term = (env1.tc_term);
              typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
              universe_of = (env1.universe_of);
              typeof_well_typed_tot_or_gtot_term =
                (env1.typeof_well_typed_tot_or_gtot_term);
              teq_nosmt_force = (env1.teq_nosmt_force);
              subtype_nosmt_force = (env1.subtype_nosmt_force);
              qtbl_name_and_index =
                ((FStar_Pervasives_Native.Some (l, typ, next)), tbl);
              normalized_eff_names = (env1.normalized_eff_names);
              fv_delta_depths = (env1.fv_delta_depths);
              proof_ns = (env1.proof_ns);
              synth_hook = (env1.synth_hook);
              try_solve_implicits_hook = (env1.try_solve_implicits_hook);
              splice = (env1.splice);
              mpreprocess = (env1.mpreprocess);
              postprocess = (env1.postprocess);
              identifier_info = (env1.identifier_info);
              tc_hooks = (env1.tc_hooks);
              dsenv = (env1.dsenv);
              nbe = (env1.nbe);
              strict_args_tab = (env1.strict_args_tab);
              erasable_types_tab = (env1.erasable_types_tab);
              enable_defer_to_tac = (env1.enable_defer_to_tac);
              unif_allow_ref_guards = (env1.unif_allow_ref_guards);
              erase_erasable_args = (env1.erase_erasable_args);
              core_check = (env1.core_check);
              missing_decl = (env1.missing_decl)
            })
       | FStar_Pervasives_Native.Some (uu___1, m) ->
           let next = m + Prims.int_one in
           (add_query_index (l, next);
            (let uu___4 = FStarC_Ident.string_of_lid l in
             FStarC_SMap.add tbl uu___4 next);
            {
              solver = (env1.solver);
              range = (env1.range);
              curmodule = (env1.curmodule);
              gamma = (env1.gamma);
              gamma_sig = (env1.gamma_sig);
              gamma_cache = (env1.gamma_cache);
              modules = (env1.modules);
              expected_typ = (env1.expected_typ);
              sigtab = (env1.sigtab);
              attrtab = (env1.attrtab);
              instantiate_imp = (env1.instantiate_imp);
              effects = (env1.effects);
              generalize = (env1.generalize);
              letrecs = (env1.letrecs);
              top_level = (env1.top_level);
              check_uvars = (env1.check_uvars);
              use_eq_strict = (env1.use_eq_strict);
              is_iface = (env1.is_iface);
              admit = (env1.admit);
              phase1 = (env1.phase1);
              failhard = (env1.failhard);
              flychecking = (env1.flychecking);
              uvar_subtyping = (env1.uvar_subtyping);
              intactics = (env1.intactics);
              nocoerce = (env1.nocoerce);
              tc_term = (env1.tc_term);
              typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
              universe_of = (env1.universe_of);
              typeof_well_typed_tot_or_gtot_term =
                (env1.typeof_well_typed_tot_or_gtot_term);
              teq_nosmt_force = (env1.teq_nosmt_force);
              subtype_nosmt_force = (env1.subtype_nosmt_force);
              qtbl_name_and_index =
                ((FStar_Pervasives_Native.Some (l, typ, next)), tbl);
              normalized_eff_names = (env1.normalized_eff_names);
              fv_delta_depths = (env1.fv_delta_depths);
              proof_ns = (env1.proof_ns);
              synth_hook = (env1.synth_hook);
              try_solve_implicits_hook = (env1.try_solve_implicits_hook);
              splice = (env1.splice);
              mpreprocess = (env1.mpreprocess);
              postprocess = (env1.postprocess);
              identifier_info = (env1.identifier_info);
              tc_hooks = (env1.tc_hooks);
              dsenv = (env1.dsenv);
              nbe = (env1.nbe);
              strict_args_tab = (env1.strict_args_tab);
              erasable_types_tab = (env1.erasable_types_tab);
              enable_defer_to_tac = (env1.enable_defer_to_tac);
              unif_allow_ref_guards = (env1.unif_allow_ref_guards);
              erase_erasable_args = (env1.erase_erasable_args);
              core_check = (env1.core_check);
              missing_decl = (env1.missing_decl)
            }))
let set_range (e : env) (r : FStarC_Range_Type.t) : env=
  if r = FStarC_Range_Type.dummyRange
  then e
  else
    {
      solver = (e.solver);
      range = r;
      curmodule = (e.curmodule);
      gamma = (e.gamma);
      gamma_sig = (e.gamma_sig);
      gamma_cache = (e.gamma_cache);
      modules = (e.modules);
      expected_typ = (e.expected_typ);
      sigtab = (e.sigtab);
      attrtab = (e.attrtab);
      instantiate_imp = (e.instantiate_imp);
      effects = (e.effects);
      generalize = (e.generalize);
      letrecs = (e.letrecs);
      top_level = (e.top_level);
      check_uvars = (e.check_uvars);
      use_eq_strict = (e.use_eq_strict);
      is_iface = (e.is_iface);
      admit = (e.admit);
      phase1 = (e.phase1);
      failhard = (e.failhard);
      flychecking = (e.flychecking);
      uvar_subtyping = (e.uvar_subtyping);
      intactics = (e.intactics);
      nocoerce = (e.nocoerce);
      tc_term = (e.tc_term);
      typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
      universe_of = (e.universe_of);
      typeof_well_typed_tot_or_gtot_term =
        (e.typeof_well_typed_tot_or_gtot_term);
      teq_nosmt_force = (e.teq_nosmt_force);
      subtype_nosmt_force = (e.subtype_nosmt_force);
      qtbl_name_and_index = (e.qtbl_name_and_index);
      normalized_eff_names = (e.normalized_eff_names);
      fv_delta_depths = (e.fv_delta_depths);
      proof_ns = (e.proof_ns);
      synth_hook = (e.synth_hook);
      try_solve_implicits_hook = (e.try_solve_implicits_hook);
      splice = (e.splice);
      mpreprocess = (e.mpreprocess);
      postprocess = (e.postprocess);
      identifier_info = (e.identifier_info);
      tc_hooks = (e.tc_hooks);
      dsenv = (e.dsenv);
      nbe = (e.nbe);
      strict_args_tab = (e.strict_args_tab);
      erasable_types_tab = (e.erasable_types_tab);
      enable_defer_to_tac = (e.enable_defer_to_tac);
      unif_allow_ref_guards = (e.unif_allow_ref_guards);
      erase_erasable_args = (e.erase_erasable_args);
      core_check = (e.core_check);
      missing_decl = (e.missing_decl)
    }
let get_range (e : env) : FStarC_Range_Type.t= e.range
let hasRange_env : env FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos = get_range;
    FStarC_Class_HasRange.setPos = (fun r e -> set_range e r)
  }
let toggle_id_info (env1 : env) (enabled : Prims.bool) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang env1.identifier_info in
    FStarC_TypeChecker_Common.id_info_toggle uu___1 enabled in
  FStarC_Effect.op_Colon_Equals env1.identifier_info uu___
let insert_bv_info (env1 : env) (bv : FStarC_Syntax_Syntax.bv)
  (ty : FStarC_Syntax_Syntax.typ) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang env1.identifier_info in
    FStarC_TypeChecker_Common.id_info_insert_bv uu___1 bv ty in
  FStarC_Effect.op_Colon_Equals env1.identifier_info uu___
let insert_fv_info (env1 : env) (fv : FStarC_Syntax_Syntax.fv)
  (ty : FStarC_Syntax_Syntax.typ) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang env1.identifier_info in
    FStarC_TypeChecker_Common.id_info_insert_fv uu___1 fv ty in
  FStarC_Effect.op_Colon_Equals env1.identifier_info uu___
let promote_id_info (env1 : env)
  (ty_map :
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang env1.identifier_info in
    FStarC_TypeChecker_Common.id_info_promote uu___1 ty_map in
  FStarC_Effect.op_Colon_Equals env1.identifier_info uu___
let modules (env1 : env) : FStarC_Syntax_Syntax.modul Prims.list=
  env1.modules
let current_module (env1 : env) : FStarC_Ident.lident= env1.curmodule
let set_current_module (env1 : env) (lid : FStarC_Ident.lident) : env=
  let env2 =
    {
      solver = (env1.solver);
      range = (env1.range);
      curmodule = lid;
      gamma = (env1.gamma);
      gamma_sig = (env1.gamma_sig);
      gamma_cache = (env1.gamma_cache);
      modules = (env1.modules);
      expected_typ = (env1.expected_typ);
      sigtab = (env1.sigtab);
      attrtab = (env1.attrtab);
      instantiate_imp = (env1.instantiate_imp);
      effects = (env1.effects);
      generalize = (env1.generalize);
      letrecs = (env1.letrecs);
      top_level = (env1.top_level);
      check_uvars = (env1.check_uvars);
      use_eq_strict = (env1.use_eq_strict);
      is_iface = (env1.is_iface);
      admit = (env1.admit);
      phase1 = (env1.phase1);
      failhard = (env1.failhard);
      flychecking = (env1.flychecking);
      uvar_subtyping = (env1.uvar_subtyping);
      intactics = (env1.intactics);
      nocoerce = (env1.nocoerce);
      tc_term = (env1.tc_term);
      typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
      universe_of = (env1.universe_of);
      typeof_well_typed_tot_or_gtot_term =
        (env1.typeof_well_typed_tot_or_gtot_term);
      teq_nosmt_force = (env1.teq_nosmt_force);
      subtype_nosmt_force = (env1.subtype_nosmt_force);
      qtbl_name_and_index = (env1.qtbl_name_and_index);
      normalized_eff_names = (env1.normalized_eff_names);
      fv_delta_depths = (env1.fv_delta_depths);
      proof_ns = (env1.proof_ns);
      synth_hook = (env1.synth_hook);
      try_solve_implicits_hook = (env1.try_solve_implicits_hook);
      splice = (env1.splice);
      mpreprocess = (env1.mpreprocess);
      postprocess = (env1.postprocess);
      identifier_info = (env1.identifier_info);
      tc_hooks = (env1.tc_hooks);
      dsenv = (env1.dsenv);
      nbe = (env1.nbe);
      strict_args_tab = (env1.strict_args_tab);
      erasable_types_tab = (env1.erasable_types_tab);
      enable_defer_to_tac = (env1.enable_defer_to_tac);
      unif_allow_ref_guards = (env1.unif_allow_ref_guards);
      erase_erasable_args = (env1.erase_erasable_args);
      core_check = (env1.core_check);
      missing_decl = (env1.missing_decl)
    } in
  let uu___ = FStarC_Syntax_DsEnv.set_current_module env2.dsenv lid in
  {
    solver = (env2.solver);
    range = (env2.range);
    curmodule = (env2.curmodule);
    gamma = (env2.gamma);
    gamma_sig = (env2.gamma_sig);
    gamma_cache = (env2.gamma_cache);
    modules = (env2.modules);
    expected_typ = (env2.expected_typ);
    sigtab = (env2.sigtab);
    attrtab = (env2.attrtab);
    instantiate_imp = (env2.instantiate_imp);
    effects = (env2.effects);
    generalize = (env2.generalize);
    letrecs = (env2.letrecs);
    top_level = (env2.top_level);
    check_uvars = (env2.check_uvars);
    use_eq_strict = (env2.use_eq_strict);
    is_iface = (env2.is_iface);
    admit = (env2.admit);
    phase1 = (env2.phase1);
    failhard = (env2.failhard);
    flychecking = (env2.flychecking);
    uvar_subtyping = (env2.uvar_subtyping);
    intactics = (env2.intactics);
    nocoerce = (env2.nocoerce);
    tc_term = (env2.tc_term);
    typeof_tot_or_gtot_term = (env2.typeof_tot_or_gtot_term);
    universe_of = (env2.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env2.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env2.teq_nosmt_force);
    subtype_nosmt_force = (env2.subtype_nosmt_force);
    qtbl_name_and_index = (env2.qtbl_name_and_index);
    normalized_eff_names = (env2.normalized_eff_names);
    fv_delta_depths = (env2.fv_delta_depths);
    proof_ns = (env2.proof_ns);
    synth_hook = (env2.synth_hook);
    try_solve_implicits_hook = (env2.try_solve_implicits_hook);
    splice = (env2.splice);
    mpreprocess = (env2.mpreprocess);
    postprocess = (env2.postprocess);
    identifier_info = (env2.identifier_info);
    tc_hooks = (env2.tc_hooks);
    dsenv = uu___;
    nbe = (env2.nbe);
    strict_args_tab = (env2.strict_args_tab);
    erasable_types_tab = (env2.erasable_types_tab);
    enable_defer_to_tac = (env2.enable_defer_to_tac);
    unif_allow_ref_guards = (env2.unif_allow_ref_guards);
    erase_erasable_args = (env2.erase_erasable_args);
    core_check = (env2.core_check);
    missing_decl = (env2.missing_decl)
  }
let has_interface (env1 : env) (l : FStarC_Ident.lident) : Prims.bool=
  FStarC_Util.for_some
    (fun m ->
       m.FStarC_Syntax_Syntax.is_interface &&
         (FStarC_Ident.lid_equals m.FStarC_Syntax_Syntax.name l))
    env1.modules
let find_in_sigtab (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option=
  let uu___ = FStarC_Ident.string_of_lid lid in
  FStarC_SMap.try_find (sigtab env1) uu___
let new_u_univ (uu___ : unit) : FStarC_Syntax_Syntax.universe=
  let uu___1 =
    FStarC_Syntax_Unionfind.univ_fresh FStarC_Range_Type.dummyRange in
  FStarC_Syntax_Syntax.U_unif uu___1
let mk_univ_subst (formals : FStarC_Syntax_Syntax.univ_name Prims.list)
  (us : FStarC_Syntax_Syntax.universes) :
  FStarC_Syntax_Syntax.subst_elt Prims.list=
  let n = (FStarC_List.length formals) - Prims.int_one in
  FStarC_List.mapi (fun i u -> FStarC_Syntax_Syntax.UN ((n - i), u)) us
let inst_tscheme_with (ts : FStarC_Syntax_Syntax.tscheme)
  (us : FStarC_Syntax_Syntax.universes) :
  (FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.term)=
  match (ts, us) with
  | (([], t), []) -> ([], t)
  | ((formals, t), uu___) ->
      let vs = mk_univ_subst formals us in
      let uu___1 = FStarC_Syntax_Subst.subst vs t in (us, uu___1)
let inst_tscheme (uu___ : FStarC_Syntax_Syntax.tscheme) :
  (FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.term)=
  match uu___ with
  | ([], t) -> ([], t)
  | (us, t) ->
      let us' = FStarC_List.map (fun uu___1 -> new_u_univ ()) us in
      inst_tscheme_with (us, t) us'
let inst_tscheme_with_range (r : FStarC_Range_Type.range)
  (t : FStarC_Syntax_Syntax.tscheme) :
  (FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.term)=
  let uu___ = inst_tscheme t in
  match uu___ with
  | (us, t1) ->
      let uu___1 = FStarC_Syntax_Subst.set_use_range r t1 in (us, uu___1)
let check_effect_is_not_a_template (ed : FStarC_Syntax_Syntax.eff_decl)
  (rng : FStarC_Range_Type.t) : unit=
  if
    ((FStarC_List.length ed.FStarC_Syntax_Syntax.univs) <> Prims.int_zero) ||
      ((FStarC_List.length ed.FStarC_Syntax_Syntax.binders) <> Prims.int_zero)
  then
    let msg =
      let uu___ =
        FStarC_Class_Show.show FStarC_Ident.showable_lident
          ed.FStarC_Syntax_Syntax.mname in
      let uu___1 =
        let uu___2 =
          FStarC_List.map FStarC_Syntax_Print.binder_to_string_with_type
            ed.FStarC_Syntax_Syntax.binders in
        FStarC_String.concat "," uu___2 in
      FStarC_Format.fmt2
        "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
        uu___ uu___1 in
    FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
      FStarC_Errors_Codes.Fatal_NotEnoughArgumentsForEffect ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_string) (Obj.magic msg)
  else ()
let inst_effect_fun_with (insts : FStarC_Syntax_Syntax.universes)
  (env1 : env) (ed : FStarC_Syntax_Syntax.eff_decl)
  (uu___ : FStarC_Syntax_Syntax.tscheme) : FStarC_Syntax_Syntax.term=
  match uu___ with
  | (us, t) ->
      (check_effect_is_not_a_template ed env1.range;
       if (FStarC_List.length insts) <> (FStarC_List.length us)
       then
         (let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                (FStarC_List.length us) in
            let uu___5 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                (FStarC_List.length insts) in
            let uu___6 =
              FStarC_Class_Show.show FStarC_Ident.showable_lident
                ed.FStarC_Syntax_Syntax.mname in
            let uu___7 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
            FStarC_Format.fmt4
              "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
              uu___4 uu___5 uu___6 uu___7 in
          failwith uu___3)
       else ();
       (let uu___3 = inst_tscheme_with (us, t) insts in
        FStar_Pervasives_Native.snd uu___3))
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes (projectee : tri) : Prims.bool=
  match projectee with | Yes -> true | uu___ -> false
let uu___is_No (projectee : tri) : Prims.bool=
  match projectee with | No -> true | uu___ -> false
let uu___is_Maybe (projectee : tri) : Prims.bool=
  match projectee with | Maybe -> true | uu___ -> false
let in_cur_mod (env1 : env) (l : FStarC_Ident.lident) : tri=
  let cur = current_module env1 in
  let uu___ =
    let uu___1 = FStarC_Ident.nsstr l in
    let uu___2 = FStarC_Ident.string_of_lid cur in uu___1 = uu___2 in
  if uu___
  then Yes
  else
    (let uu___2 =
       let uu___3 = FStarC_Ident.nsstr l in
       let uu___4 = FStarC_Ident.string_of_lid cur in
       FStarC_Util.starts_with uu___3 uu___4 in
     if uu___2
     then
       let lns =
         let uu___3 = FStarC_Ident.ns_of_lid l in
         let uu___4 = let uu___5 = FStarC_Ident.ident_of_lid l in [uu___5] in
         FStarC_List.op_At uu___3 uu___4 in
       let cur1 =
         let uu___3 = FStarC_Ident.ns_of_lid cur in
         let uu___4 = let uu___5 = FStarC_Ident.ident_of_lid cur in [uu___5] in
         FStarC_List.op_At uu___3 uu___4 in
       let rec aux c l1 =
         match (c, l1) with
         | ([], uu___3) -> Maybe
         | (uu___3, []) -> No
         | (hd::tl, hd'::tl') when
             let uu___3 = FStarC_Ident.string_of_id hd in
             let uu___4 = FStarC_Ident.string_of_id hd' in uu___3 = uu___4 ->
             aux tl tl'
         | uu___3 -> No in
       aux cur1 lns
     else No)
let lookup_qname (env1 : env) (lid : FStarC_Ident.lident) : qninfo=
  let cur_mod = in_cur_mod env1 lid in
  let cache t =
    (let uu___1 = FStarC_Ident.string_of_lid lid in
     FStarC_SMap.add (gamma_cache env1) uu___1 t);
    FStar_Pervasives_Native.Some t in
  let found =
    if cur_mod <> No
    then
      let uu___ =
        let uu___1 = FStarC_Ident.string_of_lid lid in
        FStarC_SMap.try_find (gamma_cache env1) uu___1 in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStarC_Util.find_map env1.gamma
            (fun uu___1 ->
               match uu___1 with
               | FStarC_Syntax_Syntax.Binding_lid (l, (us_names, t)) when
                   FStarC_Ident.lid_equals lid l ->
                   let us =
                     FStarC_List.map
                       (fun uu___2 -> FStarC_Syntax_Syntax.U_name uu___2)
                       us_names in
                   let uu___2 =
                     let uu___3 = FStarC_Ident.range_of_lid l in
                     ((FStar_Pervasives.Inl (us, t)), uu___3) in
                   FStar_Pervasives_Native.Some uu___2
               | uu___2 -> FStar_Pervasives_Native.None)
      | se -> se
    else FStar_Pervasives_Native.None in
  if FStar_Pervasives_Native.uu___is_Some found
  then found
  else
    (let uu___1 = find_in_sigtab env1 lid in
     match uu___1 with
     | FStar_Pervasives_Native.Some se ->
         let uu___2 =
           let uu___3 = FStarC_Syntax_Util.range_of_sigelt se in
           ((FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None)),
             uu___3) in
         FStar_Pervasives_Native.Some uu___2
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let lookup_sigelt (env1 : env) (lid : FStarC_Ident.lid) :
  FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl uu___1, rng) ->
      FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, us), rng) ->
      FStar_Pervasives_Native.Some se
let lookup_attr (env1 : env) (attr : Prims.string) :
  FStarC_Syntax_Syntax.sigelt Prims.list=
  let uu___ = FStarC_SMap.try_find (attrtab env1) attr in
  match uu___ with
  | FStar_Pervasives_Native.Some ses -> ses
  | FStar_Pervasives_Native.None -> []
let add_se_to_attrtab (env1 : env) (se : FStarC_Syntax_Syntax.sigelt) : 
  unit=
  let add_one env2 se1 attr =
    let uu___ = let uu___1 = lookup_attr env2 attr in se1 :: uu___1 in
    FStarC_SMap.add (attrtab env2) attr uu___ in
  FStarC_List.iter
    (fun attr ->
       let uu___ = FStarC_Syntax_Util.head_and_args attr in
       match uu___ with
       | (hd, uu___1) ->
           let uu___2 =
             let uu___3 = FStarC_Syntax_Subst.compress hd in
             uu___3.FStarC_Syntax_Syntax.n in
           (match uu___2 with
            | FStarC_Syntax_Syntax.Tm_fvar fv ->
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Syntax.lid_of_fv fv in
                  FStarC_Ident.string_of_lid uu___4 in
                add_one env1 se uu___3
            | uu___3 -> ())) se.FStarC_Syntax_Syntax.sigattrs
let try_add_sigelt (force : Prims.bool) (env1 : env)
  (se : FStarC_Syntax_Syntax.sigelt) (l : FStarC_Ident.lident) : unit=
  let s = FStarC_Ident.string_of_lid l in
  (let uu___1 =
     (Prims.op_Negation force) &&
       (let uu___2 = FStarC_SMap.try_find (sigtab env1) s in
        FStar_Pervasives_Native.uu___is_Some uu___2) in
   if uu___1
   then
     let old_se =
       let uu___2 = FStarC_SMap.try_find (sigtab env1) s in
       FStar_Pervasives_Native.__proj__Some__item__v uu___2 in
     (if
        (FStarC_Syntax_Syntax.uu___is_Sig_declare_typ
           old_se.FStarC_Syntax_Syntax.sigel)
          &&
          (((FStarC_Syntax_Syntax.uu___is_Sig_let
               se.FStarC_Syntax_Syntax.sigel)
              ||
              (FStarC_Syntax_Syntax.uu___is_Sig_inductive_typ
                 se.FStarC_Syntax_Syntax.sigel))
             ||
             (FStarC_Syntax_Syntax.uu___is_Sig_datacon
                se.FStarC_Syntax_Syntax.sigel))
      then ()
      else
        (let uu___3 =
           let uu___4 =
             let uu___5 = FStarC_Errors_Msg.text "Duplicate top-level names" in
             FStar_Pprint.op_Hat_Slash_Hat uu___5
               (FStar_Pprint.arbitrary_string s) in
           let uu___5 =
             let uu___6 =
               let uu___7 = FStarC_Errors_Msg.text "Previously declared at" in
               let uu___8 =
                 let uu___9 =
                   let uu___10 = FStarC_Ident.range_of_lid l in
                   FStarC_Range_Ops.string_of_range uu___10 in
                 FStar_Pprint.arbitrary_string uu___9 in
               FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
             [uu___6] in
           uu___4 :: uu___5 in
         FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
           FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
           (Obj.magic uu___3)))
   else ());
  FStarC_SMap.add (sigtab env1) s se
let rec add_sigelt (force : Prims.bool) (env1 : env)
  (se : FStarC_Syntax_Syntax.sigelt) : unit=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_bundle
      { FStarC_Syntax_Syntax.ses = ses; FStarC_Syntax_Syntax.lids = uu___;_}
      -> add_sigelts force env1 ses
  | uu___ ->
      let lids = FStarC_Syntax_Util.lids_of_sigelt se in
      (FStarC_List.iter (try_add_sigelt force env1 se) lids;
       add_se_to_attrtab env1 se)
and add_sigelts (force : Prims.bool) (env1 : env)
  (ses : FStarC_Syntax_Syntax.sigelt Prims.list) : unit=
  FStarC_List.iter (add_sigelt force env1) ses
let try_lookup_bv (env1 : env) (bv : FStarC_Syntax_Syntax.bv) :
  (FStarC_Syntax_Syntax.typ * FStarC_Range_Type.t)
    FStar_Pervasives_Native.option=
  let r =
    FStarC_Util.find_map env1.gamma
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Binding_var id when
             FStarC_Syntax_Syntax.bv_eq id bv ->
             let uu___1 =
               let uu___2 =
                 FStarC_Class_HasRange.pos FStarC_Ident.hasrange_ident
                   id.FStarC_Syntax_Syntax.ppname in
               ((id.FStarC_Syntax_Syntax.sort), uu___2) in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None) in
  (let uu___1 = FStarC_Debug.extreme () in
   if uu___1
   then
     let uu___2 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv bv in
     let uu___3 =
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_option
            (FStarC_Class_Show.show_tuple2 FStarC_Syntax_Print.showable_term
               FStarC_Range_Ops.showable_range)) r in
     FStarC_Format.print2 "lookup_bv %s -> %s\n" uu___2 uu___3
   else ());
  r
let lookup_type_of_let
  (us_opt : FStarC_Syntax_Syntax.universes FStar_Pervasives_Native.option)
  (se : FStarC_Syntax_Syntax.sigelt) (lid : FStarC_Ident.lident) :
  ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.term) *
    FStarC_Range_Type.range) FStar_Pervasives_Native.option=
  let inst_tscheme1 ts =
    match us_opt with
    | FStar_Pervasives_Native.None -> inst_tscheme ts
    | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (uu___, lb::[]);
        FStarC_Syntax_Syntax.lids1 = uu___1;_}
      ->
      let uu___2 =
        let uu___3 =
          inst_tscheme1
            ((lb.FStarC_Syntax_Syntax.lbunivs),
              (lb.FStarC_Syntax_Syntax.lbtyp)) in
        let uu___4 =
          FStarC_Syntax_Syntax.range_of_lbname lb.FStarC_Syntax_Syntax.lbname in
        (uu___3, uu___4) in
      FStar_Pervasives_Native.Some uu___2
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (uu___, lbs);
        FStarC_Syntax_Syntax.lids1 = uu___1;_}
      ->
      FStarC_Util.find_map lbs
        (fun lb ->
           match lb.FStarC_Syntax_Syntax.lbname with
           | FStar_Pervasives.Inl uu___2 -> failwith "impossible"
           | FStar_Pervasives.Inr fv ->
               let uu___2 = FStarC_Syntax_Syntax.fv_eq_lid fv lid in
               if uu___2
               then
                 let uu___3 =
                   let uu___4 =
                     inst_tscheme1
                       ((lb.FStarC_Syntax_Syntax.lbunivs),
                         (lb.FStarC_Syntax_Syntax.lbtyp)) in
                   let uu___5 = FStarC_Syntax_Syntax.range_of_fv fv in
                   (uu___4, uu___5) in
                 FStar_Pervasives_Native.Some uu___3
               else FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let effect_signature
  (us_opt : FStarC_Syntax_Syntax.universes FStar_Pervasives_Native.option)
  (se : FStarC_Syntax_Syntax.sigelt) (rng : FStarC_Range_Type.t) :
  ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ) *
    FStarC_Range_Type.t) FStar_Pervasives_Native.option=
  let inst_ts us_opt1 ts =
    match us_opt1 with
    | FStar_Pervasives_Native.None -> inst_tscheme ts
    | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_new_effect ne ->
      let sig_ts =
        FStarC_Syntax_Util.effect_sig_ts ne.FStarC_Syntax_Syntax.signature in
      (check_effect_is_not_a_template ne rng;
       (match us_opt with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some us ->
            if
              (FStarC_List.length us) <>
                (FStarC_List.length (FStar_Pervasives_Native.fst sig_ts))
            then
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStarC_Ident.string_of_lid ne.FStarC_Syntax_Syntax.mname in
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                          (FStarC_List.length
                             (FStar_Pervasives_Native.fst sig_ts)) in
                      let uu___8 =
                        let uu___9 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_nat
                            (FStarC_List.length us) in
                        Prims.strcat ", got " uu___9 in
                      Prims.strcat uu___7 uu___8 in
                    Prims.strcat ", expected " uu___6 in
                  Prims.strcat uu___4 uu___5 in
                Prims.strcat
                  "effect_signature: incorrect number of universes for the signature of "
                  uu___3 in
              failwith uu___2
            else ());
       (let uu___2 =
          let uu___3 = inst_ts us_opt sig_ts in
          (uu___3, (se.FStarC_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu___2))
  | FStarC_Syntax_Syntax.Sig_effect_abbrev
      { FStarC_Syntax_Syntax.lid4 = lid; FStarC_Syntax_Syntax.us4 = us;
        FStarC_Syntax_Syntax.bs2 = binders;
        FStarC_Syntax_Syntax.comp1 = uu___;
        FStarC_Syntax_Syntax.cflags = uu___1;_}
      ->
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                FStarC_Syntax_Syntax.mk_Total FStarC_Syntax_Syntax.teff in
              FStarC_Syntax_Util.arrow binders uu___6 in
            (us, uu___5) in
          inst_ts us_opt uu___4 in
        (uu___3, (se.FStarC_Syntax_Syntax.sigrng)) in
      FStar_Pervasives_Native.Some uu___2
  | uu___ -> FStar_Pervasives_Native.None
let try_lookup_lid_aux
  (us_opt : FStarC_Syntax_Syntax.universes FStar_Pervasives_Native.option)
  (env1 : env) (lid : FStarC_Ident.lident) :
  ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.term) *
    FStarC_Range_Type.range) FStar_Pervasives_Native.option=
  let inst_tscheme1 ts =
    match us_opt with
    | FStar_Pervasives_Native.None -> inst_tscheme ts
    | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
  let mapper uu___ =
    match uu___ with
    | (lr, rng) ->
        (match lr with
         | FStar_Pervasives.Inl t -> FStar_Pervasives_Native.Some (t, rng)
         | FStar_Pervasives.Inr
             ({
                FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
                  { FStarC_Syntax_Syntax.lid1 = uu___1;
                    FStarC_Syntax_Syntax.us1 = uvs;
                    FStarC_Syntax_Syntax.t1 = t;
                    FStarC_Syntax_Syntax.ty_lid = uu___2;
                    FStarC_Syntax_Syntax.num_ty_params = uu___3;
                    FStarC_Syntax_Syntax.mutuals1 = uu___4;
                    FStarC_Syntax_Syntax.injective_type_params1 = uu___5;
                    FStarC_Syntax_Syntax.proj_disc_lids = uu___6;_};
                FStarC_Syntax_Syntax.sigrng = uu___7;
                FStarC_Syntax_Syntax.sigquals = uu___8;
                FStarC_Syntax_Syntax.sigmeta = uu___9;
                FStarC_Syntax_Syntax.sigattrs = uu___10;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
                FStarC_Syntax_Syntax.sigopts = uu___12;_},
              FStar_Pervasives_Native.None)
             ->
             let uu___13 =
               let uu___14 = inst_tscheme1 (uvs, t) in (uu___14, rng) in
             FStar_Pervasives_Native.Some uu___13
         | FStar_Pervasives.Inr
             ({
                FStarC_Syntax_Syntax.sigel =
                  FStarC_Syntax_Syntax.Sig_declare_typ
                  { FStarC_Syntax_Syntax.lid2 = l;
                    FStarC_Syntax_Syntax.us2 = uvs;
                    FStarC_Syntax_Syntax.t2 = t;_};
                FStarC_Syntax_Syntax.sigrng = uu___1;
                FStarC_Syntax_Syntax.sigquals = qs;
                FStarC_Syntax_Syntax.sigmeta = uu___2;
                FStarC_Syntax_Syntax.sigattrs = uu___3;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
                FStarC_Syntax_Syntax.sigopts = uu___5;_},
              FStar_Pervasives_Native.None)
             ->
             let uu___6 = let uu___7 = in_cur_mod env1 l in uu___7 = Yes in
             if uu___6
             then
               (if
                  (FStarC_List.contains FStarC_Syntax_Syntax.Assumption qs)
                    || env1.is_iface
                then
                  let uu___7 =
                    let uu___8 = inst_tscheme1 (uvs, t) in (uu___8, rng) in
                  FStar_Pervasives_Native.Some uu___7
                else FStar_Pervasives_Native.None)
             else
               (let uu___8 =
                  let uu___9 = inst_tscheme1 (uvs, t) in (uu___9, rng) in
                FStar_Pervasives_Native.Some uu___8)
         | FStar_Pervasives.Inr
             ({
                FStarC_Syntax_Syntax.sigel =
                  FStarC_Syntax_Syntax.Sig_inductive_typ
                  { FStarC_Syntax_Syntax.lid = lid1;
                    FStarC_Syntax_Syntax.us = uvs;
                    FStarC_Syntax_Syntax.params = tps;
                    FStarC_Syntax_Syntax.num_uniform_params = uu___1;
                    FStarC_Syntax_Syntax.t = k;
                    FStarC_Syntax_Syntax.mutuals = uu___2;
                    FStarC_Syntax_Syntax.ds = uu___3;
                    FStarC_Syntax_Syntax.injective_type_params = uu___4;_};
                FStarC_Syntax_Syntax.sigrng = uu___5;
                FStarC_Syntax_Syntax.sigquals = uu___6;
                FStarC_Syntax_Syntax.sigmeta = uu___7;
                FStarC_Syntax_Syntax.sigattrs = uu___8;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
                FStarC_Syntax_Syntax.sigopts = uu___10;_},
              FStar_Pervasives_Native.None)
             ->
             (match tps with
              | [] ->
                  let uu___11 =
                    let uu___12 = inst_tscheme1 (uvs, k) in (uu___12, rng) in
                  FStar_Pervasives_Native.Some uu___11
              | uu___11 ->
                  let uu___12 =
                    let uu___13 =
                      let uu___14 =
                        let uu___15 =
                          let uu___16 = FStarC_Syntax_Syntax.mk_Total k in
                          FStarC_Syntax_Util.flat_arrow tps uu___16 in
                        (uvs, uu___15) in
                      inst_tscheme1 uu___14 in
                    (uu___13, rng) in
                  FStar_Pervasives_Native.Some uu___12)
         | FStar_Pervasives.Inr
             ({
                FStarC_Syntax_Syntax.sigel =
                  FStarC_Syntax_Syntax.Sig_inductive_typ
                  { FStarC_Syntax_Syntax.lid = lid1;
                    FStarC_Syntax_Syntax.us = uvs;
                    FStarC_Syntax_Syntax.params = tps;
                    FStarC_Syntax_Syntax.num_uniform_params = uu___1;
                    FStarC_Syntax_Syntax.t = k;
                    FStarC_Syntax_Syntax.mutuals = uu___2;
                    FStarC_Syntax_Syntax.ds = uu___3;
                    FStarC_Syntax_Syntax.injective_type_params = uu___4;_};
                FStarC_Syntax_Syntax.sigrng = uu___5;
                FStarC_Syntax_Syntax.sigquals = uu___6;
                FStarC_Syntax_Syntax.sigmeta = uu___7;
                FStarC_Syntax_Syntax.sigattrs = uu___8;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
                FStarC_Syntax_Syntax.sigopts = uu___10;_},
              FStar_Pervasives_Native.Some us)
             ->
             (match tps with
              | [] ->
                  let uu___11 =
                    let uu___12 = inst_tscheme_with (uvs, k) us in
                    (uu___12, rng) in
                  FStar_Pervasives_Native.Some uu___11
              | uu___11 ->
                  let uu___12 =
                    let uu___13 =
                      let uu___14 =
                        let uu___15 =
                          let uu___16 = FStarC_Syntax_Syntax.mk_Total k in
                          FStarC_Syntax_Util.flat_arrow tps uu___16 in
                        (uvs, uu___15) in
                      inst_tscheme_with uu___14 us in
                    (uu___13, rng) in
                  FStar_Pervasives_Native.Some uu___12)
         | FStar_Pervasives.Inr se ->
             let uu___1 =
               match se with
               | ({
                    FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
                      uu___2;
                    FStarC_Syntax_Syntax.sigrng = uu___3;
                    FStarC_Syntax_Syntax.sigquals = uu___4;
                    FStarC_Syntax_Syntax.sigmeta = uu___5;
                    FStarC_Syntax_Syntax.sigattrs = uu___6;
                    FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                    FStarC_Syntax_Syntax.sigopts = uu___8;_},
                  FStar_Pervasives_Native.None) ->
                   lookup_type_of_let us_opt (FStar_Pervasives_Native.fst se)
                     lid
               | uu___2 ->
                   effect_signature us_opt (FStar_Pervasives_Native.fst se)
                     env1.range in
             FStarC_Option.map
               (fun uu___2 ->
                  match uu___2 with | (us_t, rng1) -> (us_t, rng1)) uu___1) in
  let uu___ =
    let uu___1 = lookup_qname env1 lid in FStarC_Option.bind uu___1 mapper in
  match uu___ with
  | FStar_Pervasives_Native.Some ((us, t), r) ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_HasRange.pos FStarC_Ident.hasrange_lident lid in
            FStarC_Class_HasRange.setPos
              (FStarC_Syntax_Syntax.has_range_syntax ()) uu___4 t in
          (us, uu___3) in
        (uu___2, r) in
      FStar_Pervasives_Native.Some uu___1
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let lid_exists (env1 : env) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lookup_qname env1 l in
  match uu___ with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some uu___1 -> true
let lookup_bv (env1 : env) (bv : FStarC_Syntax_Syntax.bv) :
  (FStarC_Syntax_Syntax.typ * FStarC_Range_Type.t)=
  let bvr = FStarC_Syntax_Syntax.range_of_bv bv in
  let uu___ = try_lookup_bv env1 bv in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv bv in
        FStarC_Format.fmt1 "Variable \"%s\" not found" uu___2 in
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range bvr
        FStarC_Errors_Codes.Fatal_VariableNotFound ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___1)
  | FStar_Pervasives_Native.Some (t, r) ->
      let uu___1 = FStarC_Syntax_Subst.set_use_range bvr t in
      let uu___2 =
        let uu___3 = FStarC_Range_Type.use_range bvr in
        FStarC_Range_Type.set_use_range r uu___3 in
      (uu___1, uu___2)
let try_lookup_lid (env1 : env) (l : FStarC_Ident.lident) :
  ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ) *
    FStarC_Range_Type.t) FStar_Pervasives_Native.option=
  let uu___ = try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ((us, t), r) ->
      let use_range = FStarC_Ident.range_of_lid l in
      let r1 =
        let uu___1 = FStarC_Range_Type.use_range use_range in
        FStarC_Range_Type.set_use_range r uu___1 in
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Subst.set_use_range use_range t in
          (us, uu___3) in
        (uu___2, r1) in
      FStar_Pervasives_Native.Some uu___1
let try_lookup_and_inst_lid (env1 : env)
  (us : FStarC_Syntax_Syntax.universes) (l : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.typ * FStarC_Range_Type.t)
    FStar_Pervasives_Native.option=
  let uu___ = try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ((uu___1, t), r) ->
      let use_range = FStarC_Ident.range_of_lid l in
      let r1 =
        let uu___2 = FStarC_Range_Type.use_range use_range in
        FStarC_Range_Type.set_use_range r uu___2 in
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.set_use_range use_range t in
        (uu___3, r1) in
      FStar_Pervasives_Native.Some uu___2
let name_not_found (l : FStarC_Ident.lid) : 'a=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid l in
    FStarC_Format.fmt1 "Name \"%s\" not found" uu___1 in
  FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
    FStarC_Errors_Codes.Fatal_NameNotFound ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_string) (Obj.magic uu___)
let lookup_lid (env1 : env) (l : FStarC_Ident.lident) :
  ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ) *
    FStarC_Range_Type.t)=
  let uu___ = try_lookup_lid env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None -> name_not_found l
let lookup_univ (env1 : env) (x : FStarC_Syntax_Syntax.univ_name) :
  Prims.bool=
  let uu___ =
    FStarC_List.find
      (fun uu___1 ->
         match uu___1 with
         | FStarC_Syntax_Syntax.Binding_univ y ->
             let uu___2 = FStarC_Ident.string_of_id x in
             let uu___3 = FStarC_Ident.string_of_id y in uu___2 = uu___3
         | uu___2 -> false) env1.gamma in
  FStar_Pervasives_Native.uu___is_Some uu___
let try_lookup_val_decl (env1 : env) (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.tscheme * FStarC_Syntax_Syntax.qualifier Prims.list)
    FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_declare_typ
            { FStarC_Syntax_Syntax.lid2 = uu___1;
              FStarC_Syntax_Syntax.us2 = uvs; FStarC_Syntax_Syntax.t2 = t;_};
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = q;
          FStarC_Syntax_Syntax.sigmeta = uu___3;
          FStarC_Syntax_Syntax.sigattrs = uu___4;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
          FStarC_Syntax_Syntax.sigopts = uu___6;_},
        FStar_Pervasives_Native.None),
       uu___7)
      ->
      let uu___8 =
        let uu___9 =
          let uu___10 =
            let uu___11 = FStarC_Ident.range_of_lid lid in
            FStarC_Syntax_Subst.set_use_range uu___11 t in
          (uvs, uu___10) in
        (uu___9, q) in
      FStar_Pervasives_Native.Some uu___8
  | uu___1 -> FStar_Pervasives_Native.None
let lookup_val_decl (env1 : env) (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ)=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_declare_typ
            { FStarC_Syntax_Syntax.lid2 = uu___1;
              FStarC_Syntax_Syntax.us2 = uvs; FStarC_Syntax_Syntax.t2 = t;_};
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = uu___3;
          FStarC_Syntax_Syntax.sigmeta = uu___4;
          FStarC_Syntax_Syntax.sigattrs = uu___5;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
          FStarC_Syntax_Syntax.sigopts = uu___7;_},
        FStar_Pervasives_Native.None),
       uu___8)
      ->
      let uu___9 = FStarC_Ident.range_of_lid lid in
      inst_tscheme_with_range uu___9 (uvs, t)
  | uu___1 -> name_not_found lid
let lookup_datacon (env1 : env) (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ)=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
            { FStarC_Syntax_Syntax.lid1 = uu___1;
              FStarC_Syntax_Syntax.us1 = uvs; FStarC_Syntax_Syntax.t1 = t;
              FStarC_Syntax_Syntax.ty_lid = uu___2;
              FStarC_Syntax_Syntax.num_ty_params = uu___3;
              FStarC_Syntax_Syntax.mutuals1 = uu___4;
              FStarC_Syntax_Syntax.injective_type_params1 = uu___5;
              FStarC_Syntax_Syntax.proj_disc_lids = uu___6;_};
          FStarC_Syntax_Syntax.sigrng = uu___7;
          FStarC_Syntax_Syntax.sigquals = uu___8;
          FStarC_Syntax_Syntax.sigmeta = uu___9;
          FStarC_Syntax_Syntax.sigattrs = uu___10;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
          FStarC_Syntax_Syntax.sigopts = uu___12;_},
        FStar_Pervasives_Native.None),
       uu___13)
      ->
      let uu___14 = FStarC_Ident.range_of_lid lid in
      inst_tscheme_with_range uu___14 (uvs, t)
  | uu___1 -> name_not_found lid
let lookup_and_inst_datacon (env1 : env)
  (us : FStarC_Syntax_Syntax.universes) (lid : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.typ=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
            { FStarC_Syntax_Syntax.lid1 = uu___1;
              FStarC_Syntax_Syntax.us1 = uvs; FStarC_Syntax_Syntax.t1 = t;
              FStarC_Syntax_Syntax.ty_lid = uu___2;
              FStarC_Syntax_Syntax.num_ty_params = uu___3;
              FStarC_Syntax_Syntax.mutuals1 = uu___4;
              FStarC_Syntax_Syntax.injective_type_params1 = uu___5;
              FStarC_Syntax_Syntax.proj_disc_lids = uu___6;_};
          FStarC_Syntax_Syntax.sigrng = uu___7;
          FStarC_Syntax_Syntax.sigquals = uu___8;
          FStarC_Syntax_Syntax.sigmeta = uu___9;
          FStarC_Syntax_Syntax.sigattrs = uu___10;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
          FStarC_Syntax_Syntax.sigopts = uu___12;_},
        FStar_Pervasives_Native.None),
       uu___13)
      ->
      let uu___14 = inst_tscheme_with (uvs, t) us in
      FStar_Pervasives_Native.snd uu___14
  | uu___1 -> name_not_found lid
let datacons_of_typ (env1 : env) (lid : FStarC_Ident.lident) :
  (Prims.bool * FStarC_Ident.lident Prims.list)=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
            { FStarC_Syntax_Syntax.lid = uu___1;
              FStarC_Syntax_Syntax.us = uu___2;
              FStarC_Syntax_Syntax.params = uu___3;
              FStarC_Syntax_Syntax.num_uniform_params = uu___4;
              FStarC_Syntax_Syntax.t = uu___5;
              FStarC_Syntax_Syntax.mutuals = uu___6;
              FStarC_Syntax_Syntax.ds = dcs;
              FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
          FStarC_Syntax_Syntax.sigrng = uu___8;
          FStarC_Syntax_Syntax.sigquals = uu___9;
          FStarC_Syntax_Syntax.sigmeta = uu___10;
          FStarC_Syntax_Syntax.sigattrs = uu___11;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
          FStarC_Syntax_Syntax.sigopts = uu___13;_},
        uu___14),
       uu___15)
      -> (true, dcs)
  | uu___1 -> (false, [])
let typ_of_datacon (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Ident.lident=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
            { FStarC_Syntax_Syntax.lid1 = uu___1;
              FStarC_Syntax_Syntax.us1 = uu___2;
              FStarC_Syntax_Syntax.t1 = uu___3;
              FStarC_Syntax_Syntax.ty_lid = l;
              FStarC_Syntax_Syntax.num_ty_params = uu___4;
              FStarC_Syntax_Syntax.mutuals1 = uu___5;
              FStarC_Syntax_Syntax.injective_type_params1 = uu___6;
              FStarC_Syntax_Syntax.proj_disc_lids = uu___7;_};
          FStarC_Syntax_Syntax.sigrng = uu___8;
          FStarC_Syntax_Syntax.sigquals = uu___9;
          FStarC_Syntax_Syntax.sigmeta = uu___10;
          FStarC_Syntax_Syntax.sigattrs = uu___11;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
          FStarC_Syntax_Syntax.sigopts = uu___13;_},
        uu___14),
       uu___15)
      -> l
  | uu___1 ->
      let uu___2 =
        let uu___3 = FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
        FStarC_Format.fmt1 "Not a datacon: %s" uu___3 in
      failwith uu___2
let num_datacon_non_injective_ty_params (env1 : env)
  (lid : FStarC_Ident.lident) : Prims.int FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
            { FStarC_Syntax_Syntax.lid1 = uu___1;
              FStarC_Syntax_Syntax.us1 = uu___2;
              FStarC_Syntax_Syntax.t1 = uu___3;
              FStarC_Syntax_Syntax.ty_lid = uu___4;
              FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
              FStarC_Syntax_Syntax.mutuals1 = uu___5;
              FStarC_Syntax_Syntax.injective_type_params1 =
                injective_type_params;
              FStarC_Syntax_Syntax.proj_disc_lids = uu___6;_};
          FStarC_Syntax_Syntax.sigrng = uu___7;
          FStarC_Syntax_Syntax.sigquals = uu___8;
          FStarC_Syntax_Syntax.sigmeta = uu___9;
          FStarC_Syntax_Syntax.sigattrs = uu___10;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
          FStarC_Syntax_Syntax.sigopts = uu___12;_},
        uu___13),
       uu___14)
      ->
      if injective_type_params
      then FStar_Pervasives_Native.Some Prims.int_zero
      else FStar_Pervasives_Native.Some num_ty_params
  | uu___1 -> FStar_Pervasives_Native.None
let visible_with (delta_levels : delta_level Prims.list)
  (quals : FStarC_Syntax_Syntax.qualifier Prims.list) : Prims.bool=
  FStarC_Util.for_some (fun dl -> FStarC_Util.for_some (visible_at dl) quals)
    delta_levels
let lookup_definition_qninfo_aux (rec_ok : Prims.bool)
  (delta_levels : delta_level Prims.list) (lid : FStarC_Ident.lident)
  (qninfo1 : qninfo) :
  (FStarC_Syntax_Syntax.univ_name Prims.list * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax) FStar_Pervasives_Native.option=
  match qninfo1 with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None), uu___) ->
      (match se.FStarC_Syntax_Syntax.sigel with
       | FStarC_Syntax_Syntax.Sig_let
           { FStarC_Syntax_Syntax.lbs1 = (is_rec, lbs);
             FStarC_Syntax_Syntax.lids1 = uu___1;_}
           when
           (visible_with delta_levels se.FStarC_Syntax_Syntax.sigquals) &&
             ((Prims.op_Negation is_rec) || rec_ok)
           ->
           FStarC_Util.find_map lbs
             (fun lb ->
                let fv =
                  FStar_Pervasives.__proj__Inr__item__v
                    lb.FStarC_Syntax_Syntax.lbname in
                let uu___2 = FStarC_Syntax_Syntax.fv_eq_lid fv lid in
                if uu___2
                then
                  FStar_Pervasives_Native.Some
                    ((lb.FStarC_Syntax_Syntax.lbunivs),
                      (lb.FStarC_Syntax_Syntax.lbdef))
                else FStar_Pervasives_Native.None)
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let lookup_definition_qninfo (delta_levels : delta_level Prims.list)
  (lid : FStarC_Ident.lident) (qninfo1 : qninfo) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term)
    FStar_Pervasives_Native.option=
  lookup_definition_qninfo_aux true delta_levels lid qninfo1
let lookup_definition (delta_levels : delta_level Prims.list) (env1 : env)
  (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term)
    FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  lookup_definition_qninfo delta_levels lid uu___
let lookup_nonrec_definition (delta_levels : delta_level Prims.list)
  (env1 : env) (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term)
    FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  lookup_definition_qninfo_aux false delta_levels lid uu___
let rec delta_depth_of_qninfo_lid (env1 : env) (lid : FStarC_Ident.lident)
  (qn : qninfo) : FStarC_Syntax_Syntax.delta_depth=
  match qn with
  | FStar_Pervasives_Native.None -> FStarC_Syntax_Syntax.delta_constant
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl uu___, uu___1) ->
      FStarC_Syntax_Syntax.delta_constant
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, uu___), uu___1)
      ->
      (match se.FStarC_Syntax_Syntax.sigel with
       | FStarC_Syntax_Syntax.Sig_inductive_typ uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_bundle uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_datacon uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_declare_typ uu___2 ->
           let d0 =
             let uu___3 = FStarC_Syntax_Util.is_primop_lid lid in
             if uu___3
             then FStarC_Syntax_Syntax.delta_equational
             else FStarC_Syntax_Syntax.delta_constant in
           let uu___3 =
             (FStarC_Util.for_some FStarC_Syntax_Syntax.uu___is_Assumption
                se.FStarC_Syntax_Syntax.sigquals)
               &&
               (let uu___4 =
                  FStarC_Util.for_some FStarC_Syntax_Syntax.uu___is_New
                    se.FStarC_Syntax_Syntax.sigquals in
                Prims.op_Negation uu___4) in
           if uu___3 then FStarC_Syntax_Syntax.Delta_abstract d0 else d0
       | FStarC_Syntax_Syntax.Sig_let
           { FStarC_Syntax_Syntax.lbs1 = (uu___2, lbs);
             FStarC_Syntax_Syntax.lids1 = uu___3;_}
           ->
           let uu___4 =
             FStarC_Util.find_map lbs
               (fun lb ->
                  let fv =
                    FStar_Pervasives.__proj__Inr__item__v
                      lb.FStarC_Syntax_Syntax.lbname in
                  let uu___5 = FStarC_Syntax_Syntax.fv_eq_lid fv lid in
                  if uu___5
                  then
                    let uu___6 =
                      let uu___7 =
                        delta_depth_of_term env1
                          lb.FStarC_Syntax_Syntax.lbdef in
                      FStarC_Syntax_Util.incr_delta_depth uu___7 in
                    FStar_Pervasives_Native.Some uu___6
                  else FStar_Pervasives_Native.None) in
           FStarC_Option.must uu___4
       | FStarC_Syntax_Syntax.Sig_fail uu___2 ->
           failwith "impossible: delta_depth_of_qninfo"
       | FStarC_Syntax_Syntax.Sig_splice uu___2 ->
           failwith "impossible: delta_depth_of_qninfo"
       | FStarC_Syntax_Syntax.Sig_assume uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_new_effect uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_sub_effect uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_pragma uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_polymonadic_bind uu___2 ->
           FStarC_Syntax_Syntax.delta_constant
       | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp uu___2 ->
           FStarC_Syntax_Syntax.delta_constant)
and delta_depth_of_qninfo (env1 : env) (fv : FStarC_Syntax_Syntax.fv)
  (qn : qninfo) : FStarC_Syntax_Syntax.delta_depth=
  delta_depth_of_qninfo_lid env1 fv.FStarC_Syntax_Syntax.fv_name qn
and delta_depth_of_fv (env1 : env) (fv : FStarC_Syntax_Syntax.fv) :
  FStarC_Syntax_Syntax.delta_depth=
  let lid = fv.FStarC_Syntax_Syntax.fv_name in
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid lid in
    FStarC_SMap.try_find env1.fv_delta_depths uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some dd -> dd
  | FStar_Pervasives_Native.None ->
      ((let uu___2 = FStarC_Ident.string_of_lid lid in
        FStarC_SMap.add env1.fv_delta_depths uu___2
          FStarC_Syntax_Syntax.delta_equational);
       (let d =
          let uu___2 = lookup_qname env1 fv.FStarC_Syntax_Syntax.fv_name in
          delta_depth_of_qninfo env1 fv uu___2 in
        (let uu___3 = FStarC_Ident.string_of_lid lid in
         FStarC_SMap.add env1.fv_delta_depths uu___3 d);
        d))
and fv_delta_depth (env1 : env) (fv : FStarC_Syntax_Syntax.fv) :
  FStarC_Syntax_Syntax.delta_depth=
  let d = delta_depth_of_fv env1 fv in
  match d with
  | FStarC_Syntax_Syntax.Delta_abstract
      (FStarC_Syntax_Syntax.Delta_constant_at_level l) ->
      let uu___ =
        (let uu___1 = FStarC_Ident.string_of_lid env1.curmodule in
         let uu___2 = FStarC_Ident.nsstr fv.FStarC_Syntax_Syntax.fv_name in
         uu___1 = uu___2) && (Prims.op_Negation env1.is_iface) in
      if uu___
      then FStarC_Syntax_Syntax.Delta_constant_at_level l
      else FStarC_Syntax_Syntax.delta_constant
  | d1 -> d1
and delta_depth_of_term (env1 : env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.delta_depth=
  let t1 = FStarC_Syntax_Util.unmeta t in
  match t1.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_meta uu___ ->
      failwith "Impossible (delta depth of term)"
  | FStarC_Syntax_Syntax.Tm_delayed uu___ ->
      failwith "Impossible (delta depth of term)"
  | FStarC_Syntax_Syntax.Tm_lazy i ->
      let uu___ = FStarC_Syntax_Util.unfold_lazy i in
      delta_depth_of_term env1 uu___
  | FStarC_Syntax_Syntax.Tm_fvar fv -> fv_delta_depth env1 fv
  | FStarC_Syntax_Syntax.Tm_bvar uu___ ->
      FStarC_Syntax_Syntax.delta_equational
  | FStarC_Syntax_Syntax.Tm_name uu___ ->
      FStarC_Syntax_Syntax.delta_equational
  | FStarC_Syntax_Syntax.Tm_match uu___ ->
      FStarC_Syntax_Syntax.delta_equational
  | FStarC_Syntax_Syntax.Tm_uvar uu___ ->
      FStarC_Syntax_Syntax.delta_equational
  | FStarC_Syntax_Syntax.Tm_unknown -> FStarC_Syntax_Syntax.delta_equational
  | FStarC_Syntax_Syntax.Tm_type uu___ -> FStarC_Syntax_Syntax.delta_constant
  | FStarC_Syntax_Syntax.Tm_quoted uu___ ->
      FStarC_Syntax_Syntax.delta_constant
  | FStarC_Syntax_Syntax.Tm_constant uu___ ->
      FStarC_Syntax_Syntax.delta_constant
  | FStarC_Syntax_Syntax.Tm_arrow uu___ ->
      FStarC_Syntax_Syntax.delta_constant
  | FStarC_Syntax_Syntax.Tm_uinst (t2, uu___) -> delta_depth_of_term env1 t2
  | FStarC_Syntax_Syntax.Tm_refine
      {
        FStarC_Syntax_Syntax.b =
          { FStarC_Syntax_Syntax.ppname = uu___;
            FStarC_Syntax_Syntax.index = uu___1;
            FStarC_Syntax_Syntax.sort = t2;_};
        FStarC_Syntax_Syntax.phi = uu___2;_}
      -> delta_depth_of_term env1 t2
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = t2; FStarC_Syntax_Syntax.asc = uu___;
        FStarC_Syntax_Syntax.eff_opt = uu___1;_}
      -> delta_depth_of_term env1 t2
  | FStarC_Syntax_Syntax.Tm_app
      { FStarC_Syntax_Syntax.hd = t2; FStarC_Syntax_Syntax.args = uu___;_} ->
      delta_depth_of_term env1 t2
  | FStarC_Syntax_Syntax.Tm_abs
      { FStarC_Syntax_Syntax.bs = uu___; FStarC_Syntax_Syntax.body = t2;
        FStarC_Syntax_Syntax.rc_opt = uu___1;_}
      -> delta_depth_of_term env1 t2
  | FStarC_Syntax_Syntax.Tm_let
      { FStarC_Syntax_Syntax.lbs = uu___; FStarC_Syntax_Syntax.body1 = t2;_}
      -> delta_depth_of_term env1 t2
let quals_of_qninfo (qninfo1 : qninfo) :
  FStarC_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option=
  match qninfo1 with
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, uu___), uu___1)
      -> FStar_Pervasives_Native.Some (se.FStarC_Syntax_Syntax.sigquals)
  | uu___ -> FStar_Pervasives_Native.None
let attrs_of_qninfo (qninfo1 : qninfo) :
  FStarC_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option=
  match qninfo1 with
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, uu___), uu___1)
      -> FStar_Pervasives_Native.Some (se.FStarC_Syntax_Syntax.sigattrs)
  | uu___ -> FStar_Pervasives_Native.None
let lookup_attrs_of_lid (env1 : env) (lid : FStarC_Ident.lid) :
  FStarC_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in attrs_of_qninfo uu___
let fv_exists_and_has_attr (env1 : env) (fv_lid : FStarC_Ident.lid)
  (attr_lid : FStarC_Ident.lident) : (Prims.bool * Prims.bool)=
  let uu___ = lookup_attrs_of_lid env1 fv_lid in
  match uu___ with
  | FStar_Pervasives_Native.None -> (false, false)
  | FStar_Pervasives_Native.Some attrs ->
      let uu___1 =
        FStarC_Util.for_some
          (fun tm ->
             let uu___2 =
               let uu___3 = FStarC_Syntax_Util.un_uinst tm in
               uu___3.FStarC_Syntax_Syntax.n in
             match uu___2 with
             | FStarC_Syntax_Syntax.Tm_fvar fv ->
                 FStarC_Syntax_Syntax.fv_eq_lid fv attr_lid
             | uu___3 -> false) attrs in
      (true, uu___1)
let fv_with_lid_has_attr (env1 : env) (fv_lid : FStarC_Ident.lid)
  (attr_lid : FStarC_Ident.lid) : Prims.bool=
  let uu___ = fv_exists_and_has_attr env1 fv_lid attr_lid in
  FStar_Pervasives_Native.snd uu___
let fv_has_attr (env1 : env) (fv : FStarC_Syntax_Syntax.fv)
  (attr_lid : FStarC_Ident.lid) : Prims.bool=
  fv_with_lid_has_attr env1 fv.FStarC_Syntax_Syntax.fv_name attr_lid
let cache_in_fv_tab (tab : 'a FStarC_SMap.t) (fv : FStarC_Syntax_Syntax.fv)
  (f : unit -> (Prims.bool * 'a)) : 'a=
  let s =
    let uu___ = FStarC_Syntax_Syntax.lid_of_fv fv in
    FStarC_Ident.string_of_lid uu___ in
  let uu___ = FStarC_SMap.try_find tab s in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 = f () in
      (match uu___1 with
       | (should_cache, res) ->
           (if should_cache then FStarC_SMap.add tab s res else (); res))
  | FStar_Pervasives_Native.Some r -> r
let fv_has_erasable_attr (env1 : env) (fv : FStarC_Syntax_Syntax.fv) :
  Prims.bool=
  let f uu___ =
    let uu___1 =
      fv_exists_and_has_attr env1 fv.FStarC_Syntax_Syntax.fv_name
        FStarC_Parser_Const.erasable_attr in
    match uu___1 with | (ex, erasable) -> (ex, erasable) in
  cache_in_fv_tab env1.erasable_types_tab fv f
let fv_has_strict_args (env1 : env) (fv : FStarC_Syntax_Syntax.fv) :
  Prims.int Prims.list FStar_Pervasives_Native.option=
  let f uu___ =
    let attrs =
      let uu___1 = FStarC_Syntax_Syntax.lid_of_fv fv in
      lookup_attrs_of_lid env1 uu___1 in
    match attrs with
    | FStar_Pervasives_Native.None -> (false, FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.Some attrs1 ->
        let res =
          FStarC_Util.find_map attrs1
            (fun x ->
               let uu___1 =
                 FStarC_ToSyntax_ToSyntax.parse_attr_with_list false x
                   FStarC_Parser_Const.strict_on_arguments_attr in
               FStar_Pervasives_Native.fst uu___1) in
        let uu___1 = FStarC_Option.map FStar_Pervasives_Native.fst res in
        (true, uu___1) in
  cache_in_fv_tab env1.strict_args_tab fv f
let try_lookup_effect_lid (env1 : env) (ftv : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 ftv in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None), uu___1) ->
      let uu___2 =
        effect_signature FStar_Pervasives_Native.None se env1.range in
      (match uu___2 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ((uu___3, t), r) ->
           let uu___4 =
             let uu___5 = FStarC_Ident.range_of_lid ftv in
             FStarC_Syntax_Subst.set_use_range uu___5 t in
           FStar_Pervasives_Native.Some uu___4)
  | uu___1 -> FStar_Pervasives_Native.None
let lookup_effect_lid (env1 : env) (ftv : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term=
  let uu___ = try_lookup_effect_lid env1 ftv in
  match uu___ with
  | FStar_Pervasives_Native.None -> name_not_found ftv
  | FStar_Pervasives_Native.Some k -> k
let lookup_effect_abbrev (env1 : env)
  (univ_insts : FStarC_Syntax_Syntax.universes) (lid0 : FStarC_Ident.lident)
  :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp)
    FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid0 in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_effect_abbrev
            { FStarC_Syntax_Syntax.lid4 = lid;
              FStarC_Syntax_Syntax.us4 = univs;
              FStarC_Syntax_Syntax.bs2 = binders;
              FStarC_Syntax_Syntax.comp1 = c;
              FStarC_Syntax_Syntax.cflags = uu___1;_};
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = quals;
          FStarC_Syntax_Syntax.sigmeta = uu___3;
          FStarC_Syntax_Syntax.sigattrs = uu___4;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
          FStarC_Syntax_Syntax.sigopts = uu___6;_},
        FStar_Pervasives_Native.None),
       uu___7)
      ->
      let lid1 =
        let uu___8 =
          let uu___9 = FStarC_Ident.range_of_lid lid in
          let uu___10 =
            let uu___11 = FStarC_Ident.range_of_lid lid0 in
            FStarC_Range_Type.use_range uu___11 in
          FStarC_Range_Type.set_use_range uu___9 uu___10 in
        FStarC_Ident.set_lid_range lid uu___8 in
      let uu___8 =
        FStarC_Util.for_some
          (fun uu___9 ->
             match uu___9 with
             | FStarC_Syntax_Syntax.Irreducible -> true
             | uu___10 -> false) quals in
      if uu___8
      then FStar_Pervasives_Native.None
      else
        (let insts =
           if (FStarC_List.length univ_insts) = (FStarC_List.length univs)
           then univ_insts
           else
             (let uu___11 =
                let uu___12 =
                  let uu___13 = get_range env1 in
                  FStarC_Range_Ops.string_of_range uu___13 in
                let uu___13 =
                  FStarC_Class_Show.show FStarC_Ident.showable_lident lid1 in
                let uu___14 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                    (FStarC_List.length univ_insts) in
                FStarC_Format.fmt3
                  "(%s) Unexpected instantiation of effect %s with %s universes"
                  uu___12 uu___13 uu___14 in
              failwith uu___11) in
         match (binders, univs) with
         | ([], uu___10) ->
             failwith "Unexpected effect abbreviation with no arguments"
         | (uu___10, uu___11::uu___12::uu___13) ->
             let uu___14 =
               let uu___15 =
                 FStarC_Class_Show.show FStarC_Ident.showable_lident lid1 in
               let uu___16 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                   (FStarC_List.length univs) in
               FStarC_Format.fmt2
                 "Unexpected effect abbreviation %s; polymorphic in %s universes"
                 uu___15 uu___16 in
             failwith uu___14
         | uu___10 ->
             let uu___11 =
               let uu___12 =
                 let uu___13 = FStarC_Syntax_Util.arrow binders c in
                 (univs, uu___13) in
               inst_tscheme_with uu___12 insts in
             (match uu___11 with
              | (uu___12, t) ->
                  let t1 =
                    let uu___13 = FStarC_Ident.range_of_lid lid1 in
                    FStarC_Syntax_Subst.set_use_range uu___13 t in
                  let uu___13 =
                    let uu___14 = FStarC_Syntax_Subst.compress t1 in
                    uu___14.FStarC_Syntax_Syntax.n in
                  (match uu___13 with
                   | FStarC_Syntax_Syntax.Tm_arrow
                       { FStarC_Syntax_Syntax.bs1 = binders1;
                         FStarC_Syntax_Syntax.comp = c1;_}
                       -> FStar_Pervasives_Native.Some (binders1, c1)
                   | uu___14 -> failwith "Impossible")))
  | uu___1 -> FStar_Pervasives_Native.None
let norm_eff_name (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Ident.lident=
  let rec find l1 =
    let uu___ = lookup_effect_abbrev env1 [FStarC_Syntax_Syntax.U_unknown] l1 in
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (uu___1, c) ->
        let l2 = FStarC_Syntax_Util.comp_effect_name c in
        let uu___2 = find l2 in
        (match uu___2 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some l2
         | FStar_Pervasives_Native.Some l' -> FStar_Pervasives_Native.Some l') in
  let res =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_lid l in
      FStarC_SMap.try_find env1.normalized_eff_names uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let uu___1 = find l in
        (match uu___1 with
         | FStar_Pervasives_Native.None -> l
         | FStar_Pervasives_Native.Some m ->
             ((let uu___3 = FStarC_Ident.string_of_lid l in
               FStarC_SMap.add env1.normalized_eff_names uu___3 m);
              m)) in
  let uu___ = FStarC_Ident.range_of_lid l in
  FStarC_Ident.set_lid_range res uu___
let is_erasable_effect (env1 : env) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = norm_eff_name env1 l in
  (FStarC_Ident.lid_equals uu___ FStarC_Parser_Const.effect_GHOST_lid) ||
    (let uu___1 =
       FStarC_Syntax_Syntax.lid_as_fv uu___ FStar_Pervasives_Native.None in
     fv_has_erasable_attr env1 uu___1)
let rec non_informative (env1 : env) (t : FStarC_Syntax_Syntax.typ) :
  Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Syntax_Util.unrefine t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_type uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      (((FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.unit_lid) ||
          (FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.squash_lid))
         ||
         (FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.erased_lid))
        || (fv_has_erasable_attr env1 fv)
  | FStarC_Syntax_Syntax.Tm_app
      { FStarC_Syntax_Syntax.hd = head; FStarC_Syntax_Syntax.args = uu___1;_}
      -> non_informative env1 head
  | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) -> non_informative env1 t1
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = uu___1; FStarC_Syntax_Syntax.comp = c;_}
      ->
      ((FStarC_Syntax_Util.is_pure_or_ghost_comp c) &&
         (let uu___2 = FStarC_Syntax_Util.comp_result c in
          non_informative env1 uu___2))
        ||
        (let uu___2 = FStarC_Syntax_Util.comp_effect_name c in
         is_erasable_effect env1 uu___2)
  | uu___1 -> false
let num_effect_indices (env1 : env) (name : FStarC_Ident.lident)
  (r : FStarC_Range_Type.t) : Prims.int=
  let sig_t =
    let uu___ = lookup_effect_lid env1 name in
    FStarC_Syntax_Subst.compress uu___ in
  match sig_t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = _a::bs;
        FStarC_Syntax_Syntax.comp = uu___;_}
      -> FStarC_List.length bs
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Ident.showable_lident name in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term sig_t in
        FStarC_Format.fmt2 "Signature for %s not an arrow (%s)" uu___2 uu___3 in
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Fatal_UnexpectedSignatureForMonad ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___1)
let lookup_effect_quals (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.qualifier Prims.list=
  let l1 = norm_eff_name env1 l in
  let uu___ = lookup_qname env1 l1 in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_new_effect
            uu___1;
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = q;
          FStarC_Syntax_Syntax.sigmeta = uu___3;
          FStarC_Syntax_Syntax.sigattrs = uu___4;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
          FStarC_Syntax_Syntax.sigopts = uu___6;_},
        uu___7),
       uu___8)
      -> q
  | uu___1 -> []
let lookup_projector (env1 : env) (lid : FStarC_Ident.lident) (i : Prims.int)
  : FStarC_Ident.lident=
  let fail uu___ =
    let uu___1 =
      let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      let uu___3 = FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
      FStarC_Format.fmt2
        "Impossible: projecting field #%s from constructor %s is undefined"
        uu___2 uu___3 in
    failwith uu___1 in
  let uu___ = lookup_datacon env1 lid in
  match uu___ with
  | (uu___1, t) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.compress t in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_arrow
           { FStarC_Syntax_Syntax.bs1 = binders;
             FStarC_Syntax_Syntax.comp = uu___3;_}
           ->
           if (i < Prims.int_zero) || (i >= (FStarC_List.length binders))
           then fail ()
           else
             (let b = FStarC_List.nth binders i in
              FStarC_Syntax_Util.mk_field_projector_name lid
                b.FStarC_Syntax_Syntax.binder_bv i)
       | uu___3 -> fail ())
let is_projector (env1 : env) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lookup_qname env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_declare_typ
            uu___1;
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = quals;
          FStarC_Syntax_Syntax.sigmeta = uu___3;
          FStarC_Syntax_Syntax.sigattrs = uu___4;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
          FStarC_Syntax_Syntax.sigopts = uu___6;_},
        uu___7),
       uu___8)
      ->
      FStarC_Util.for_some
        (fun uu___9 ->
           match uu___9 with
           | FStarC_Syntax_Syntax.Projector uu___10 -> true
           | uu___10 -> false) quals
  | uu___1 -> false
let is_datacon (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
            uu___1;
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = uu___3;
          FStarC_Syntax_Syntax.sigmeta = uu___4;
          FStarC_Syntax_Syntax.sigattrs = uu___5;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
          FStarC_Syntax_Syntax.sigopts = uu___7;_},
        uu___8),
       uu___9)
      -> true
  | uu___1 -> false
let is_record (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
            uu___1;
          FStarC_Syntax_Syntax.sigrng = uu___2;
          FStarC_Syntax_Syntax.sigquals = quals;
          FStarC_Syntax_Syntax.sigmeta = uu___3;
          FStarC_Syntax_Syntax.sigattrs = uu___4;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
          FStarC_Syntax_Syntax.sigopts = uu___6;_},
        uu___7),
       uu___8)
      ->
      FStarC_Util.for_some
        (fun uu___9 ->
           match uu___9 with
           | FStarC_Syntax_Syntax.RecordType uu___10 -> true
           | FStarC_Syntax_Syntax.RecordConstructor uu___10 -> true
           | uu___10 -> false) quals
  | uu___1 -> false
let qninfo_is_action (qninfo1 : qninfo) : Prims.bool=
  match qninfo1 with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({ FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let uu___;
          FStarC_Syntax_Syntax.sigrng = uu___1;
          FStarC_Syntax_Syntax.sigquals = quals;
          FStarC_Syntax_Syntax.sigmeta = uu___2;
          FStarC_Syntax_Syntax.sigattrs = uu___3;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
          FStarC_Syntax_Syntax.sigopts = uu___5;_},
        uu___6),
       uu___7)
      ->
      FStarC_Util.for_some
        (fun uu___8 ->
           match uu___8 with
           | FStarC_Syntax_Syntax.Action uu___9 -> true
           | uu___9 -> false) quals
  | uu___ -> false
let is_action (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lookup_qname env1 lid in qninfo_is_action uu___
let is_interpreted : env -> FStarC_Syntax_Syntax.term -> Prims.bool=
  let interpreted_symbols =
    [FStarC_Parser_Const.op_Eq;
    FStarC_Parser_Const.op_notEq;
    FStarC_Parser_Const.op_LT;
    FStarC_Parser_Const.op_LTE;
    FStarC_Parser_Const.op_GT;
    FStarC_Parser_Const.op_GTE;
    FStarC_Parser_Const.op_Subtraction;
    FStarC_Parser_Const.op_Minus;
    FStarC_Parser_Const.op_Addition;
    FStarC_Parser_Const.op_Multiply;
    FStarC_Parser_Const.op_Division;
    FStarC_Parser_Const.op_Modulus;
    FStarC_Parser_Const.op_And;
    FStarC_Parser_Const.op_Or;
    FStarC_Parser_Const.op_Negation] in
  fun env1 head ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Util.un_uinst head in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        (FStarC_Util.for_some
           (FStarC_Ident.lid_equals fv.FStarC_Syntax_Syntax.fv_name)
           interpreted_symbols)
          ||
          (let uu___1 = delta_depth_of_fv env1 fv in
           (match uu___1 with
            | FStarC_Syntax_Syntax.Delta_equational_at_level uu___2 -> true
            | uu___2 -> false))
    | uu___1 -> false
let is_irreducible (env1 : env) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lookup_qname env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, uu___1), uu___2)
      ->
      FStarC_Util.for_some
        (fun uu___3 ->
           match uu___3 with
           | FStarC_Syntax_Syntax.Irreducible -> true
           | uu___4 -> false) se.FStarC_Syntax_Syntax.sigquals
  | uu___1 -> false
let is_type_constructor (env1 : env) (lid : FStarC_Ident.lident) :
  Prims.bool=
  let mapper x =
    match FStar_Pervasives_Native.fst x with
    | FStar_Pervasives.Inl uu___ -> FStar_Pervasives_Native.Some false
    | FStar_Pervasives.Inr (se, uu___) ->
        (match se.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_declare_typ uu___1 ->
             FStar_Pervasives_Native.Some
               (FStarC_List.contains FStarC_Syntax_Syntax.New
                  se.FStarC_Syntax_Syntax.sigquals)
         | FStarC_Syntax_Syntax.Sig_inductive_typ uu___1 ->
             FStar_Pervasives_Native.Some true
         | uu___1 -> FStar_Pervasives_Native.Some false) in
  let uu___ =
    let uu___1 = lookup_qname env1 lid in FStarC_Option.bind uu___1 mapper in
  match uu___ with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let num_inductive_ty_params (env1 : env) (lid : FStarC_Ident.lident) :
  Prims.int FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
            { FStarC_Syntax_Syntax.lid = uu___1;
              FStarC_Syntax_Syntax.us = uu___2;
              FStarC_Syntax_Syntax.params = tps;
              FStarC_Syntax_Syntax.num_uniform_params = uu___3;
              FStarC_Syntax_Syntax.t = uu___4;
              FStarC_Syntax_Syntax.mutuals = uu___5;
              FStarC_Syntax_Syntax.ds = uu___6;
              FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
          FStarC_Syntax_Syntax.sigrng = uu___8;
          FStarC_Syntax_Syntax.sigquals = uu___9;
          FStarC_Syntax_Syntax.sigmeta = uu___10;
          FStarC_Syntax_Syntax.sigattrs = uu___11;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
          FStarC_Syntax_Syntax.sigopts = uu___13;_},
        uu___14),
       uu___15)
      -> FStar_Pervasives_Native.Some (FStarC_List.length tps)
  | uu___1 -> FStar_Pervasives_Native.None
let num_inductive_uniform_ty_params (env1 : env) (lid : FStarC_Ident.lident)
  : Prims.int FStar_Pervasives_Native.option=
  let uu___ = lookup_qname env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some
      (FStar_Pervasives.Inr
       ({
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
            { FStarC_Syntax_Syntax.lid = uu___1;
              FStarC_Syntax_Syntax.us = uu___2;
              FStarC_Syntax_Syntax.params = uu___3;
              FStarC_Syntax_Syntax.num_uniform_params = num_uniform;
              FStarC_Syntax_Syntax.t = uu___4;
              FStarC_Syntax_Syntax.mutuals = uu___5;
              FStarC_Syntax_Syntax.ds = uu___6;
              FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
          FStarC_Syntax_Syntax.sigrng = uu___8;
          FStarC_Syntax_Syntax.sigquals = uu___9;
          FStarC_Syntax_Syntax.sigmeta = uu___10;
          FStarC_Syntax_Syntax.sigattrs = uu___11;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
          FStarC_Syntax_Syntax.sigopts = uu___13;_},
        uu___14),
       uu___15)
      ->
      (match num_uniform with
       | FStar_Pervasives_Native.None ->
           let uu___16 =
             let uu___17 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
             FStarC_Format.fmt1
               "Internal error: Inductive %s is not decorated with its uniform type parameters"
               uu___17 in
           FStarC_Errors.raise_error FStarC_Ident.hasrange_lident lid
             FStarC_Errors_Codes.Fatal_UnexpectedInductivetype ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic uu___16)
       | FStar_Pervasives_Native.Some n -> FStar_Pervasives_Native.Some n)
  | uu___1 -> FStar_Pervasives_Native.None
let effect_decl_opt (env1 : env) (l : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.eff_decl * FStarC_Syntax_Syntax.qualifier Prims.list)
    FStar_Pervasives_Native.option=
  FStarC_Option.find
    (fun uu___ ->
       match uu___ with
       | (d, uu___1) ->
           FStarC_Ident.lid_equals d.FStarC_Syntax_Syntax.mname l)
    (env1.effects).decls
let get_effect_decl (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.eff_decl=
  let uu___ = effect_decl_opt env1 l in
  match uu___ with
  | FStar_Pervasives_Native.None -> name_not_found l
  | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let get_lid_valued_effect_attr (env1 : env) (eff_lid : FStarC_Ident.lident)
  (attr_name_lid : FStarC_Ident.lident)
  (default_if_attr_has_no_arg :
    FStarC_Ident.lident FStar_Pervasives_Native.option)
  : FStarC_Ident.lident FStar_Pervasives_Native.option=
  let attr_args =
    let uu___ =
      let uu___1 =
        let uu___2 = norm_eff_name env1 eff_lid in
        lookup_attrs_of_lid env1 uu___2 in
      FStarC_Option.dflt [] uu___1 in
    FStarC_Syntax_Util.get_attribute attr_name_lid uu___ in
  match attr_args with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some args ->
      if (FStarC_List.length args) = Prims.int_zero
      then default_if_attr_has_no_arg
      else
        (let uu___1 = FStarC_List.hd args in
         match uu___1 with
         | (t, uu___2) ->
             let uu___3 =
               let uu___4 = FStarC_Syntax_Subst.compress t in
               uu___4.FStarC_Syntax_Syntax.n in
             (match uu___3 with
              | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string
                  (s, uu___4)) ->
                  let uu___5 = FStarC_Ident.lid_of_str s in
                  FStar_Pervasives_Native.Some uu___5
              | uu___4 ->
                  let uu___5 =
                    let uu___6 =
                      FStarC_Class_Show.show FStarC_Ident.showable_lident
                        eff_lid in
                    let uu___7 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t in
                    FStarC_Format.fmt2
                      "The argument for the effect attribute for %s is not a constant string, it is %s\n"
                      uu___6 uu___7 in
                  FStarC_Errors.raise_error
                    (FStarC_Syntax_Syntax.has_range_syntax ()) t
                    FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___5)))
let get_default_effect (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  get_lid_valued_effect_attr env1 lid FStarC_Parser_Const.default_effect_attr
    FStar_Pervasives_Native.None
let get_top_level_effect (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  get_lid_valued_effect_attr env1 lid
    FStarC_Parser_Const.top_level_effect_attr
    (FStar_Pervasives_Native.Some lid)
let is_layered_effect (env1 : env) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = get_effect_decl env1 l in FStarC_Syntax_Util.is_layered uu___
let identity_mlift : mlift=
  {
    mlift_wp = (fun uu___ c -> (c, FStarC_TypeChecker_Common.trivial_guard));
    mlift_term = (FStar_Pervasives_Native.Some (fun uu___ uu___1 e -> e))
  }
let join_opt (env1 : env) (l1 : FStarC_Ident.lident)
  (l2 : FStarC_Ident.lident) :
  (FStarC_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option=
  let uu___ = FStarC_Ident.lid_equals l1 l2 in
  if uu___
  then FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
  else
    (let uu___2 =
       ((FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_GTot_lid) &&
          (FStarC_Ident.lid_equals l2 FStarC_Parser_Const.effect_Tot_lid))
         ||
         ((FStarC_Ident.lid_equals l2 FStarC_Parser_Const.effect_GTot_lid) &&
            (FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_Tot_lid)) in
     if uu___2
     then
       FStar_Pervasives_Native.Some
         (FStarC_Parser_Const.effect_GTot_lid, identity_mlift,
           identity_mlift)
     else
       (let uu___4 =
          FStarC_Option.find
            (fun uu___5 ->
               match uu___5 with
               | (m1, m2, uu___6, uu___7, uu___8) ->
                   (FStarC_Ident.lid_equals l1 m1) &&
                     (FStarC_Ident.lid_equals l2 m2)) (env1.effects).joins in
        match uu___4 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu___5, uu___6, m3, j1, j2) ->
            FStar_Pervasives_Native.Some (m3, j1, j2)))
let join (env1 : env) (l1 : FStarC_Ident.lident) (l2 : FStarC_Ident.lident) :
  (FStarC_Ident.lident * mlift * mlift)=
  let uu___ = join_opt env1 l1 l2 in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Ident.showable_lident l1 in
        let uu___3 = FStarC_Class_Show.show FStarC_Ident.showable_lident l2 in
        FStarC_Format.fmt2 "Effects %s and %s cannot be composed" uu___2
          uu___3 in
      FStarC_Errors.raise_error hasRange_env env1
        FStarC_Errors_Codes.Fatal_EffectsCannotBeComposed ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___1)
  | FStar_Pervasives_Native.Some t -> t
let monad_leq (env1 : env) (l1 : FStarC_Ident.lident)
  (l2 : FStarC_Ident.lident) : edge FStar_Pervasives_Native.option=
  let uu___ =
    (FStarC_Ident.lid_equals l1 l2) ||
      ((FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_Tot_lid) &&
         (FStarC_Ident.lid_equals l2 FStarC_Parser_Const.effect_GTot_lid)) in
  if uu___
  then
    FStar_Pervasives_Native.Some
      { msource = l1; mtarget = l2; mlift = identity_mlift; mpath = [] }
  else
    FStarC_Option.find
      (fun e ->
         (FStarC_Ident.lid_equals l1 e.msource) &&
           (FStarC_Ident.lid_equals l2 e.mtarget)) (env1.effects).order
let wp_sig_aux (decls : (FStarC_Syntax_Syntax.eff_decl * 'uuuuu) Prims.list)
  (m : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax)=
  let uu___ =
    FStarC_Option.find
      (fun uu___1 ->
         match uu___1 with
         | (d, uu___2) ->
             FStarC_Ident.lid_equals d.FStarC_Syntax_Syntax.mname m) decls in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid m in
        FStarC_Format.fmt1 "Impossible: declaration for monad %s not found"
          uu___2 in
      failwith uu___1
  | FStar_Pervasives_Native.Some (md, _q) ->
      let uu___1 =
        let uu___2 =
          FStarC_Syntax_Util.effect_sig_ts md.FStarC_Syntax_Syntax.signature in
        inst_tscheme uu___2 in
      (match uu___1 with
       | (uu___2, s) ->
           let s1 = FStarC_Syntax_Subst.compress s in
           (match ((md.FStarC_Syntax_Syntax.binders),
                    (s1.FStarC_Syntax_Syntax.n))
            with
            | ([], FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = b::wp_b::[];
                 FStarC_Syntax_Syntax.comp = c;_})
                when
                let uu___3 = FStarC_Syntax_Util.comp_result c in
                FStarC_Syntax_Syntax.is_teff uu___3 ->
                ((b.FStarC_Syntax_Syntax.binder_bv),
                  ((wp_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort))
            | uu___3 -> failwith "Impossible"))
let wp_signature (env1 : env) (m : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term)=
  wp_sig_aux (env1.effects).decls m
let bound_vars_of_bindings (bs : FStarC_Syntax_Syntax.binding Prims.list) :
  FStarC_Syntax_Syntax.bv Prims.list=
  FStarC_List.collect
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.Binding_var x -> [x]
       | FStarC_Syntax_Syntax.Binding_lid uu___1 -> []
       | FStarC_Syntax_Syntax.Binding_univ uu___1 -> []) bs
let binders_of_bindings (bs : FStarC_Syntax_Syntax.binding Prims.list) :
  FStarC_Syntax_Syntax.binders=
  let uu___ =
    let uu___1 = bound_vars_of_bindings bs in
    FStarC_List.map FStarC_Syntax_Syntax.mk_binder uu___1 in
  FStarC_List.rev uu___
let all_binders (env1 : env) : FStarC_Syntax_Syntax.binders=
  binders_of_bindings env1.gamma
let bound_vars (env1 : env) : FStarC_Syntax_Syntax.bv Prims.list=
  bound_vars_of_bindings env1.gamma
let hasBinders_env : env FStarC_Class_Binders.hasBinders=
  {
    FStarC_Class_Binders.boundNames =
      (fun uu___ ->
         (fun e ->
            let uu___ = bound_vars e in
            Obj.magic
              (FStarC_Class_Setlike.from_list ()
                 (Obj.magic
                    (FStarC_FlatSet.setlike_flat_set
                       FStarC_Syntax_Syntax.ord_bv)) uu___)) uu___)
  }
let hasNames_lcomp :
  FStarC_TypeChecker_Common.lcomp FStarC_Class_Binders.hasNames=
  {
    FStarC_Class_Binders.freeNames =
      (fun lc ->
         let uu___ =
           let uu___1 = FStarC_TypeChecker_Common.lcomp_comp lc in
           FStar_Pervasives_Native.fst uu___1 in
         FStarC_Class_Binders.freeNames FStarC_Class_Binders.hasNames_comp
           uu___)
  }
let pretty_lcomp : FStarC_TypeChecker_Common.lcomp FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = (fun lc -> FStar_Pprint.empty) }
let hasNames_guard : guard_t FStarC_Class_Binders.hasNames=
  {
    FStarC_Class_Binders.freeNames =
      (fun uu___ ->
         (fun g ->
            match g.FStarC_TypeChecker_Common.guard_f with
            | FStarC_TypeChecker_Common.Trivial ->
                Obj.magic
                  (Obj.repr
                     (FStarC_Class_Setlike.empty ()
                        (Obj.magic
                           (FStarC_FlatSet.setlike_flat_set
                              FStarC_Syntax_Syntax.ord_bv)) ()))
            | FStarC_TypeChecker_Common.NonTrivial f ->
                Obj.magic
                  (Obj.repr
                     (FStarC_Class_Binders.freeNames
                        FStarC_Class_Binders.hasNames_term f))) uu___)
  }
let pretty_guard : guard_t FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun g ->
         match g.FStarC_TypeChecker_Common.guard_f with
         | FStarC_TypeChecker_Common.Trivial ->
             FStar_Pprint.doc_of_string "Trivial"
         | FStarC_TypeChecker_Common.NonTrivial f ->
             let uu___ = FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term f in
             FStar_Pprint.op_Hat_Slash_Hat
               (FStar_Pprint.doc_of_string "NonTrivial") uu___)
  }
let comp_to_comp_typ (env1 : env) (c : FStarC_Syntax_Syntax.comp) :
  FStarC_Syntax_Syntax.comp_typ=
  FStarC_Defensive.def_check_scoped hasBinders_env
    FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
    c.FStarC_Syntax_Syntax.pos "comp_to_comp_typ" env1 c;
  (match c.FStarC_Syntax_Syntax.n with
   | FStarC_Syntax_Syntax.Comp ct -> ct
   | uu___1 ->
       let uu___2 =
         match c.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Total t ->
             (FStarC_Parser_Const.effect_Tot_lid, t)
         | FStarC_Syntax_Syntax.GTotal t ->
             (FStarC_Parser_Const.effect_GTot_lid, t) in
       (match uu___2 with
        | (effect_name, result_typ) ->
            let uu___3 =
              let uu___4 = env1.universe_of env1 result_typ in [uu___4] in
            let uu___4 = FStarC_Syntax_Util.comp_flags c in
            {
              FStarC_Syntax_Syntax.comp_univs = uu___3;
              FStarC_Syntax_Syntax.effect_name = effect_name;
              FStarC_Syntax_Syntax.result_typ = result_typ;
              FStarC_Syntax_Syntax.effect_args = [];
              FStarC_Syntax_Syntax.flags = uu___4
            }))
let comp_set_flags (env1 : env) (c : FStarC_Syntax_Syntax.comp)
  (f : FStarC_Syntax_Syntax.cflag Prims.list) : FStarC_Syntax_Syntax.comp=
  FStarC_Defensive.def_check_scoped hasBinders_env
    FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
    c.FStarC_Syntax_Syntax.pos "comp_set_flags.IN" env1 c;
  (let r =
     let uu___1 =
       let uu___2 =
         let uu___3 = comp_to_comp_typ env1 c in
         {
           FStarC_Syntax_Syntax.comp_univs =
             (uu___3.FStarC_Syntax_Syntax.comp_univs);
           FStarC_Syntax_Syntax.effect_name =
             (uu___3.FStarC_Syntax_Syntax.effect_name);
           FStarC_Syntax_Syntax.result_typ =
             (uu___3.FStarC_Syntax_Syntax.result_typ);
           FStarC_Syntax_Syntax.effect_args =
             (uu___3.FStarC_Syntax_Syntax.effect_args);
           FStarC_Syntax_Syntax.flags = f
         } in
       FStarC_Syntax_Syntax.Comp uu___2 in
     {
       FStarC_Syntax_Syntax.n = uu___1;
       FStarC_Syntax_Syntax.pos = (c.FStarC_Syntax_Syntax.pos);
       FStarC_Syntax_Syntax.vars = (c.FStarC_Syntax_Syntax.vars);
       FStarC_Syntax_Syntax.hash_code = (c.FStarC_Syntax_Syntax.hash_code)
     } in
   FStarC_Defensive.def_check_scoped hasBinders_env
     FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
     c.FStarC_Syntax_Syntax.pos "comp_set_flags.OUT" env1 r;
   r)
let rec unfold_effect_abbrev (env1 : env) (comp : FStarC_Syntax_Syntax.comp)
  : FStarC_Syntax_Syntax.comp_typ=
  FStarC_Defensive.def_check_scoped hasBinders_env
    FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
    comp.FStarC_Syntax_Syntax.pos "unfold_effect_abbrev" env1 comp;
  (let c = comp_to_comp_typ env1 comp in
   let uu___1 =
     lookup_effect_abbrev env1 c.FStarC_Syntax_Syntax.comp_univs
       c.FStarC_Syntax_Syntax.effect_name in
   match uu___1 with
   | FStar_Pervasives_Native.None -> c
   | FStar_Pervasives_Native.Some (binders, cdef) ->
       let uu___2 = FStarC_Syntax_Subst.open_comp binders cdef in
       (match uu___2 with
        | (binders1, cdef1) ->
            (if
               (FStarC_List.length binders1) <>
                 ((FStarC_List.length c.FStarC_Syntax_Syntax.effect_args) +
                    Prims.int_one)
             then
               (let uu___4 =
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length binders1) in
                  let uu___6 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      ((FStarC_List.length c.FStarC_Syntax_Syntax.effect_args)
                         + Prims.int_one) in
                  let uu___7 =
                    let uu___8 = FStarC_Syntax_Syntax.mk_Comp c in
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp
                      uu___8 in
                  FStarC_Format.fmt3
                    "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                    uu___5 uu___6 uu___7 in
                FStarC_Errors.raise_error
                  (FStarC_Syntax_Syntax.has_range_syntax ()) comp
                  FStarC_Errors_Codes.Fatal_ConstructorArgLengthMismatch ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic uu___4))
             else ();
             (let inst =
                let uu___4 =
                  let uu___5 =
                    FStarC_Syntax_Syntax.as_arg
                      c.FStarC_Syntax_Syntax.result_typ in
                  uu___5 :: (c.FStarC_Syntax_Syntax.effect_args) in
                FStarC_List.map2
                  (fun b uu___5 ->
                     match uu___5 with
                     | (t, uu___6) ->
                         FStarC_Syntax_Syntax.NT
                           ((b.FStarC_Syntax_Syntax.binder_bv), t)) binders1
                  uu___4 in
              let c1 = FStarC_Syntax_Subst.subst_comp inst cdef1 in
              let c2 =
                let uu___4 =
                  let uu___5 = comp_to_comp_typ env1 c1 in
                  {
                    FStarC_Syntax_Syntax.comp_univs =
                      (uu___5.FStarC_Syntax_Syntax.comp_univs);
                    FStarC_Syntax_Syntax.effect_name =
                      (uu___5.FStarC_Syntax_Syntax.effect_name);
                    FStarC_Syntax_Syntax.result_typ =
                      (uu___5.FStarC_Syntax_Syntax.result_typ);
                    FStarC_Syntax_Syntax.effect_args =
                      (uu___5.FStarC_Syntax_Syntax.effect_args);
                    FStarC_Syntax_Syntax.flags =
                      (c.FStarC_Syntax_Syntax.flags)
                  } in
                FStarC_Syntax_Syntax.mk_Comp uu___4 in
              unfold_effect_abbrev env1 c2))))
let effect_repr_aux (only_reifiable : 'uuuuu) (env1 : env)
  (c : FStarC_Syntax_Syntax.comp) (u_res : FStarC_Syntax_Syntax.universe) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option=
  let check_partial_application eff_name args =
    let r = get_range env1 in
    let uu___ =
      let uu___1 = num_effect_indices env1 eff_name r in
      ((FStarC_List.length args), uu___1) in
    match uu___ with
    | (given, expected) ->
        if given = expected
        then ()
        else
          (let message =
             let uu___2 = FStarC_Ident.string_of_lid eff_name in
             let uu___3 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat given in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int expected in
             FStarC_Format.fmt3
               "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
               uu___2 uu___3 uu___4 in
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
             FStarC_Errors_Codes.Fatal_NotEnoughArgumentsForEffect ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic message)) in
  let effect_name =
    let uu___ = FStarC_Syntax_Util.comp_effect_name c in
    norm_eff_name env1 uu___ in
  let uu___ = effect_decl_opt env1 effect_name in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed, uu___1) ->
      let uu___2 = FStarC_Syntax_Util.get_eff_repr ed in
      (match uu___2 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ts ->
           let c1 = unfold_effect_abbrev env1 c in
           let res_typ = c1.FStarC_Syntax_Syntax.result_typ in
           let repr = inst_effect_fun_with [u_res] env1 ed ts in
           (check_partial_application effect_name
              c1.FStarC_Syntax_Syntax.effect_args;
            (let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = FStarC_Syntax_Syntax.as_arg res_typ in
                     uu___8 :: (c1.FStarC_Syntax_Syntax.effect_args) in
                   {
                     FStarC_Syntax_Syntax.hd = repr;
                     FStarC_Syntax_Syntax.args = uu___7
                   } in
                 FStarC_Syntax_Syntax.Tm_app uu___6 in
               let uu___6 = get_range env1 in
               FStarC_Syntax_Syntax.mk uu___5 uu___6 in
             FStar_Pervasives_Native.Some uu___4)))
let effect_repr (env1 : env) (c : FStarC_Syntax_Syntax.comp)
  (u_res : FStarC_Syntax_Syntax.universe) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  effect_repr_aux false env1 c u_res
let is_user_reifiable_effect (env1 : env) (effect_lid : FStarC_Ident.lident)
  : Prims.bool=
  let effect_lid1 = norm_eff_name env1 effect_lid in
  let quals = lookup_effect_quals env1 effect_lid1 in
  FStarC_List.contains FStarC_Syntax_Syntax.Reifiable quals
let is_user_reflectable_effect (env1 : env)
  (effect_lid : FStarC_Ident.lident) : Prims.bool=
  let effect_lid1 = norm_eff_name env1 effect_lid in
  let quals = lookup_effect_quals env1 effect_lid1 in
  FStarC_List.existsb
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.Reflectable uu___1 -> true
       | uu___1 -> false) quals
let is_total_effect (env1 : env) (effect_lid : FStarC_Ident.lident) :
  Prims.bool=
  let effect_lid1 = norm_eff_name env1 effect_lid in
  let quals = lookup_effect_quals env1 effect_lid1 in
  FStarC_List.contains FStarC_Syntax_Syntax.TotalEffect quals
let is_reifiable_effect (env1 : env) (effect_lid : FStarC_Ident.lident) :
  Prims.bool=
  let effect_lid1 = norm_eff_name env1 effect_lid in
  (is_user_reifiable_effect env1 effect_lid1) ||
    (FStarC_Ident.lid_equals effect_lid1 FStarC_Parser_Const.effect_TAC_lid)
let is_reifiable_rc (env1 : env) (c : FStarC_Syntax_Syntax.residual_comp) :
  Prims.bool= is_reifiable_effect env1 c.FStarC_Syntax_Syntax.residual_effect
let is_reifiable_comp (env1 : env) (c : FStarC_Syntax_Syntax.comp) :
  Prims.bool=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Comp ct ->
      is_reifiable_effect env1 ct.FStarC_Syntax_Syntax.effect_name
  | uu___ -> false
let is_reifiable_function (env1 : env) (t : FStarC_Syntax_Syntax.term) :
  Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = uu___1; FStarC_Syntax_Syntax.comp = c;_}
      -> is_reifiable_comp env1 c
  | uu___1 -> false
let reify_comp (env1 : env) (c : FStarC_Syntax_Syntax.comp)
  (u_c : FStarC_Syntax_Syntax.universe) : FStarC_Syntax_Syntax.term=
  let l = FStarC_Syntax_Util.comp_effect_name c in
  (let uu___1 =
     let uu___2 = is_reifiable_effect env1 l in Prims.op_Negation uu___2 in
   if uu___1
   then
     let uu___2 =
       let uu___3 = FStarC_Ident.string_of_lid l in
       FStarC_Format.fmt1 "Effect %s cannot be reified" uu___3 in
     FStarC_Errors.raise_error hasRange_env env1
       FStarC_Errors_Codes.Fatal_EffectCannotBeReified ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
       (Obj.magic uu___2)
   else ());
  (let uu___1 = effect_repr_aux true env1 c u_c in
   match uu___1 with
   | FStar_Pervasives_Native.None ->
       failwith "internal error: reifiable effect has no repr?"
   | FStar_Pervasives_Native.Some tm -> tm)
let rec record_vals_and_defns (g : env) (se : FStarC_Syntax_Syntax.sigelt) :
  env=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_declare_typ uu___ when
      FStarC_Util.for_some
        (fun uu___1 ->
           match uu___1 with
           | FStarC_Syntax_Syntax.OnlyName -> true
           | uu___2 -> false) se.FStarC_Syntax_Syntax.sigquals
      -> g
  | FStarC_Syntax_Syntax.Sig_let uu___ when
      FStarC_Util.for_some
        (fun uu___1 ->
           match uu___1 with
           | FStarC_Syntax_Syntax.OnlyName -> true
           | uu___2 -> false) se.FStarC_Syntax_Syntax.sigquals
      -> g
  | FStarC_Syntax_Syntax.Sig_declare_typ
      { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = uu___;
        FStarC_Syntax_Syntax.t2 = uu___1;_}
      ->
      if
        (FStarC_List.contains FStarC_Syntax_Syntax.Assumption
           se.FStarC_Syntax_Syntax.sigquals)
          || g.is_iface
      then g
      else record_val_for g lid
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = uu___;
        FStarC_Syntax_Syntax.lids1 = lids;_}
      -> FStarC_List.fold_left record_definition_for g lids
  | FStarC_Syntax_Syntax.Sig_datacon
      { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = uu___;
        FStarC_Syntax_Syntax.t1 = uu___1;
        FStarC_Syntax_Syntax.ty_lid = uu___2;
        FStarC_Syntax_Syntax.num_ty_params = uu___3;
        FStarC_Syntax_Syntax.mutuals1 = uu___4;
        FStarC_Syntax_Syntax.injective_type_params1 = uu___5;
        FStarC_Syntax_Syntax.proj_disc_lids = uu___6;_}
      -> record_definition_for g lid
  | FStarC_Syntax_Syntax.Sig_inductive_typ
      { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = uu___;
        FStarC_Syntax_Syntax.params = uu___1;
        FStarC_Syntax_Syntax.num_uniform_params = uu___2;
        FStarC_Syntax_Syntax.t = uu___3;
        FStarC_Syntax_Syntax.mutuals = uu___4;
        FStarC_Syntax_Syntax.ds = uu___5;
        FStarC_Syntax_Syntax.injective_type_params = uu___6;_}
      -> record_definition_for g lid
  | FStarC_Syntax_Syntax.Sig_bundle
      { FStarC_Syntax_Syntax.ses = ses; FStarC_Syntax_Syntax.lids = uu___;_}
      -> FStarC_List.fold_left record_vals_and_defns g ses
  | uu___ -> g
let push_sigelt' (force : Prims.bool) (env1 : env)
  (s : FStarC_Syntax_Syntax.sigelt) : env=
  let sb = let uu___ = FStarC_Syntax_Util.lids_of_sigelt s in (uu___, s) in
  let env2 =
    {
      solver = (env1.solver);
      range = (env1.range);
      curmodule = (env1.curmodule);
      gamma = (env1.gamma);
      gamma_sig = (sb :: (env1.gamma_sig));
      gamma_cache = (env1.gamma_cache);
      modules = (env1.modules);
      expected_typ = (env1.expected_typ);
      sigtab = (env1.sigtab);
      attrtab = (env1.attrtab);
      instantiate_imp = (env1.instantiate_imp);
      effects = (env1.effects);
      generalize = (env1.generalize);
      letrecs = (env1.letrecs);
      top_level = (env1.top_level);
      check_uvars = (env1.check_uvars);
      use_eq_strict = (env1.use_eq_strict);
      is_iface = (env1.is_iface);
      admit = (env1.admit);
      phase1 = (env1.phase1);
      failhard = (env1.failhard);
      flychecking = (env1.flychecking);
      uvar_subtyping = (env1.uvar_subtyping);
      intactics = (env1.intactics);
      nocoerce = (env1.nocoerce);
      tc_term = (env1.tc_term);
      typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
      universe_of = (env1.universe_of);
      typeof_well_typed_tot_or_gtot_term =
        (env1.typeof_well_typed_tot_or_gtot_term);
      teq_nosmt_force = (env1.teq_nosmt_force);
      subtype_nosmt_force = (env1.subtype_nosmt_force);
      qtbl_name_and_index = (env1.qtbl_name_and_index);
      normalized_eff_names = (env1.normalized_eff_names);
      fv_delta_depths = (env1.fv_delta_depths);
      proof_ns = (env1.proof_ns);
      synth_hook = (env1.synth_hook);
      try_solve_implicits_hook = (env1.try_solve_implicits_hook);
      splice = (env1.splice);
      mpreprocess = (env1.mpreprocess);
      postprocess = (env1.postprocess);
      identifier_info = (env1.identifier_info);
      tc_hooks = (env1.tc_hooks);
      dsenv = (env1.dsenv);
      nbe = (env1.nbe);
      strict_args_tab = (env1.strict_args_tab);
      erasable_types_tab = (env1.erasable_types_tab);
      enable_defer_to_tac = (env1.enable_defer_to_tac);
      unif_allow_ref_guards = (env1.unif_allow_ref_guards);
      erase_erasable_args = (env1.erase_erasable_args);
      core_check = (env1.core_check);
      missing_decl = (env1.missing_decl)
    } in
  add_sigelt force env2 s;
  (env2.tc_hooks).tc_push_in_gamma_hook env2 (FStar_Pervasives.Inr sb);
  (let env3 = record_vals_and_defns env2 s in env3)
let push_sigelt : env -> FStarC_Syntax_Syntax.sigelt -> env=
  push_sigelt' false
let push_sigelt_force : env -> FStarC_Syntax_Syntax.sigelt -> env=
  push_sigelt' true
let push_new_effect (env1 : env)
  (uu___ :
    (FStarC_Syntax_Syntax.eff_decl * FStarC_Syntax_Syntax.qualifier
      Prims.list))
  : env=
  match uu___ with
  | (ed, quals) ->
      let effects1 =
        let uu___1 = env1.effects in
        {
          decls = (FStarC_List.op_At (env1.effects).decls [(ed, quals)]);
          order = (uu___1.order);
          joins = (uu___1.joins);
          polymonadic_binds = (uu___1.polymonadic_binds);
          polymonadic_subcomps = (uu___1.polymonadic_subcomps)
        } in
      {
        solver = (env1.solver);
        range = (env1.range);
        curmodule = (env1.curmodule);
        gamma = (env1.gamma);
        gamma_sig = (env1.gamma_sig);
        gamma_cache = (env1.gamma_cache);
        modules = (env1.modules);
        expected_typ = (env1.expected_typ);
        sigtab = (env1.sigtab);
        attrtab = (env1.attrtab);
        instantiate_imp = (env1.instantiate_imp);
        effects = effects1;
        generalize = (env1.generalize);
        letrecs = (env1.letrecs);
        top_level = (env1.top_level);
        check_uvars = (env1.check_uvars);
        use_eq_strict = (env1.use_eq_strict);
        is_iface = (env1.is_iface);
        admit = (env1.admit);
        phase1 = (env1.phase1);
        failhard = (env1.failhard);
        flychecking = (env1.flychecking);
        uvar_subtyping = (env1.uvar_subtyping);
        intactics = (env1.intactics);
        nocoerce = (env1.nocoerce);
        tc_term = (env1.tc_term);
        typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
        universe_of = (env1.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (env1.typeof_well_typed_tot_or_gtot_term);
        teq_nosmt_force = (env1.teq_nosmt_force);
        subtype_nosmt_force = (env1.subtype_nosmt_force);
        qtbl_name_and_index = (env1.qtbl_name_and_index);
        normalized_eff_names = (env1.normalized_eff_names);
        fv_delta_depths = (env1.fv_delta_depths);
        proof_ns = (env1.proof_ns);
        synth_hook = (env1.synth_hook);
        try_solve_implicits_hook = (env1.try_solve_implicits_hook);
        splice = (env1.splice);
        mpreprocess = (env1.mpreprocess);
        postprocess = (env1.postprocess);
        identifier_info = (env1.identifier_info);
        tc_hooks = (env1.tc_hooks);
        dsenv = (env1.dsenv);
        nbe = (env1.nbe);
        strict_args_tab = (env1.strict_args_tab);
        erasable_types_tab = (env1.erasable_types_tab);
        enable_defer_to_tac = (env1.enable_defer_to_tac);
        unif_allow_ref_guards = (env1.unif_allow_ref_guards);
        erase_erasable_args = (env1.erase_erasable_args);
        core_check = (env1.core_check);
        missing_decl = (env1.missing_decl)
      }
let exists_polymonadic_bind (env1 : env) (m : FStarC_Ident.lident)
  (n : FStarC_Ident.lident) :
  (FStarC_Ident.lident * polymonadic_bind_t) FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Option.find
      (fun uu___1 ->
         match uu___1 with
         | (m1, n1, uu___2, uu___3) ->
             (FStarC_Ident.lid_equals m m1) && (FStarC_Ident.lid_equals n n1))
      (env1.effects).polymonadic_binds in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, uu___2, p, t) ->
      FStar_Pervasives_Native.Some (p, t)
  | uu___1 -> FStar_Pervasives_Native.None
let exists_polymonadic_subcomp (env1 : env) (m : FStarC_Ident.lident)
  (n : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.tscheme *
    FStarC_Syntax_Syntax.indexed_effect_combinator_kind)
    FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Option.find
      (fun uu___1 ->
         match uu___1 with
         | (m1, n1, uu___2, uu___3) ->
             (FStarC_Ident.lid_equals m m1) && (FStarC_Ident.lid_equals n n1))
      (env1.effects).polymonadic_subcomps in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, uu___2, ts, k) ->
      FStar_Pervasives_Native.Some (ts, k)
  | uu___1 -> FStar_Pervasives_Native.None
let print_effects_graph (env1 : env) : Prims.string=
  let eff_name lid =
    let uu___ = FStarC_Ident.ident_of_lid lid in
    FStarC_Ident.string_of_id uu___ in
  let path_str path =
    let uu___ = FStarC_List.map eff_name path in
    FStarC_String.concat ";" uu___ in
  let pbinds = FStarC_SMap.create (Prims.of_int (10)) in
  let lifts = FStarC_SMap.create (Prims.of_int (20)) in
  let psubcomps = FStarC_SMap.create (Prims.of_int (10)) in
  FStarC_List.iter
    (fun uu___1 ->
       match uu___1 with
       | { msource = src; mtarget = tgt; mlift = uu___2; mpath = path;_} ->
           let key = eff_name src in
           let m =
             let uu___3 = FStarC_SMap.try_find lifts key in
             match uu___3 with
             | FStar_Pervasives_Native.None ->
                 let m1 = FStarC_SMap.create (Prims.of_int (10)) in
                 (FStarC_SMap.add lifts key m1; m1)
             | FStar_Pervasives_Native.Some m1 -> m1 in
           let uu___3 =
             let uu___4 = eff_name tgt in FStarC_SMap.try_find m uu___4 in
           (match uu___3 with
            | FStar_Pervasives_Native.Some uu___4 -> ()
            | FStar_Pervasives_Native.None ->
                let uu___4 = eff_name tgt in
                let uu___5 = path_str path in FStarC_SMap.add m uu___4 uu___5))
    (env1.effects).order;
  FStarC_List.iter
    (fun uu___2 ->
       match uu___2 with
       | (m, n, p, uu___3) ->
           let key =
             let uu___4 = eff_name m in
             let uu___5 = eff_name n in
             let uu___6 = eff_name p in
             FStarC_Format.fmt3 "%s, %s |> %s" uu___4 uu___5 uu___6 in
           FStarC_SMap.add pbinds key "") (env1.effects).polymonadic_binds;
  FStarC_List.iter
    (fun uu___3 ->
       match uu___3 with
       | (m, n, uu___4, uu___5) ->
           let key =
             let uu___6 = eff_name m in
             let uu___7 = eff_name n in
             FStarC_Format.fmt2 "%s <: %s" uu___6 uu___7 in
           FStarC_SMap.add psubcomps key "")
    (env1.effects).polymonadic_subcomps;
  (let uu___3 =
     let uu___4 =
       FStarC_SMap.fold lifts
         (fun src m s ->
            FStarC_SMap.fold m
              (fun tgt path s1 ->
                 let uu___5 =
                   FStarC_Format.fmt3 "%s -> %s [label=\"%s\"]" src tgt path in
                 uu___5 :: s1) s) [] in
     FStarC_String.concat "\n" uu___4 in
   let uu___4 =
     let uu___5 =
       FStarC_SMap.fold pbinds
         (fun k uu___6 s ->
            let uu___7 = FStarC_Format.fmt1 "\"%s\" [shape=\"plaintext\"]" k in
            uu___7 :: s) [] in
     FStarC_String.concat "\n" uu___5 in
   let uu___5 =
     let uu___6 =
       FStarC_SMap.fold psubcomps
         (fun k uu___7 s ->
            let uu___8 = FStarC_Format.fmt1 "\"%s\" [shape=\"plaintext\"]" k in
            uu___8 :: s) [] in
     FStarC_String.concat "\n" uu___6 in
   FStarC_Format.fmt3
     "digraph {\nlabel=\"Effects ordering\"\nsubgraph cluster_lifts {\nlabel = \"Lifts\"\n\n      %s\n}\nsubgraph cluster_polymonadic_binds {\nlabel = \"Polymonadic binds\"\n%s\n}\nsubgraph cluster_polymonadic_subcomps {\nlabel = \"Polymonadic subcomps\"\n%s\n}}\n"
     uu___3 uu___4 uu___5)
let update_effect_lattice (env1 : env) (src : FStarC_Ident.lident)
  (tgt : FStarC_Ident.lident) (st_mlift : mlift) : env=
  let compose_edges e1 e2 =
    let composed_lift =
      let mlift_wp env2 c =
        let uu___ = (e1.mlift).mlift_wp env2 c in
        match uu___ with
        | (c1, g1) ->
            let uu___1 = (e2.mlift).mlift_wp env2 c1 in
            (match uu___1 with
             | (c2, g2) ->
                 let uu___2 = FStarC_TypeChecker_Common.conj_guard g1 g2 in
                 (c2, uu___2)) in
      let mlift_term =
        match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
        | (FStar_Pervasives_Native.Some l1, FStar_Pervasives_Native.Some l2)
            ->
            FStar_Pervasives_Native.Some
              ((fun u t e -> let uu___ = l1 u t e in l2 u t uu___))
        | uu___ -> FStar_Pervasives_Native.None in
      { mlift_wp; mlift_term } in
    {
      msource = (e1.msource);
      mtarget = (e2.mtarget);
      mlift = composed_lift;
      mpath =
        (FStarC_List.op_At e1.mpath (FStarC_List.op_At [e1.mtarget] e2.mpath))
    } in
  let edge1 = { msource = src; mtarget = tgt; mlift = st_mlift; mpath = [] } in
  let id_edge l =
    { msource = src; mtarget = tgt; mlift = identity_mlift; mpath = [] } in
  let find_edge order uu___ =
    match uu___ with
    | (i, j) ->
        let uu___1 = FStarC_Ident.lid_equals i j in
        if uu___1
        then FStar_Pervasives_Native.Some (id_edge i)
        else
          FStarC_Option.find
            (fun e ->
               (FStarC_Ident.lid_equals e.msource i) &&
                 (FStarC_Ident.lid_equals e.mtarget j)) order in
  let ms =
    FStarC_List.map
      (fun uu___ ->
         match uu___ with | (e, uu___1) -> e.FStarC_Syntax_Syntax.mname)
      (env1.effects).decls in
  let all_i_src =
    FStarC_List.fold_left
      (fun edges i ->
         let uu___ = FStarC_Ident.lid_equals i edge1.msource in
         if uu___
         then edges
         else
           (let uu___2 = find_edge (env1.effects).order (i, (edge1.msource)) in
            match uu___2 with
            | FStar_Pervasives_Native.Some e -> e :: edges
            | FStar_Pervasives_Native.None -> edges)) [] ms in
  let all_tgt_j =
    FStarC_List.fold_left
      (fun edges j ->
         let uu___ = FStarC_Ident.lid_equals edge1.mtarget j in
         if uu___
         then edges
         else
           (let uu___2 = find_edge (env1.effects).order ((edge1.mtarget), j) in
            match uu___2 with
            | FStar_Pervasives_Native.Some e -> e :: edges
            | FStar_Pervasives_Native.None -> edges)) [] ms in
  let check_cycle src1 tgt1 =
    let uu___ = FStarC_Ident.lid_equals src1 tgt1 in
    if uu___
    then
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Ident.showable_lident edge1.msource in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Ident.showable_lident edge1.mtarget in
        let uu___4 = FStarC_Class_Show.show FStarC_Ident.showable_lident src1 in
        FStarC_Format.fmt3 "Adding an edge %s~>%s induces a cycle %s" uu___2
          uu___3 uu___4 in
      FStarC_Errors.raise_error hasRange_env env1
        FStarC_Errors_Codes.Fatal_Effects_Ordering_Coherence ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___1)
    else () in
  let new_i_edge_target =
    FStarC_List.fold_left
      (fun edges i_src ->
         check_cycle i_src.msource edge1.mtarget;
         (let uu___1 = compose_edges i_src edge1 in uu___1 :: edges)) []
      all_i_src in
  let new_edge_source_j =
    FStarC_List.fold_left
      (fun edges tgt_j ->
         check_cycle edge1.msource tgt_j.mtarget;
         (let uu___1 = compose_edges edge1 tgt_j in uu___1 :: edges)) []
      all_tgt_j in
  let new_i_j =
    FStarC_List.fold_left
      (fun edges i_src ->
         FStarC_List.fold_left
           (fun edges1 tgt_j ->
              check_cycle i_src.msource tgt_j.mtarget;
              (let uu___1 =
                 let uu___2 = compose_edges i_src edge1 in
                 compose_edges uu___2 tgt_j in
               uu___1 :: edges1)) edges all_tgt_j) [] all_i_src in
  let new_edges = edge1 ::
    (FStarC_List.op_At new_i_edge_target
       (FStarC_List.op_At new_edge_source_j new_i_j)) in
  let order = FStarC_List.op_At new_edges (env1.effects).order in
  FStarC_List.iter
    (fun edge2 ->
       let uu___1 =
         (FStarC_Ident.lid_equals edge2.msource
            FStarC_Parser_Const.effect_DIV_lid)
           &&
           (let uu___2 = lookup_effect_quals env1 edge2.mtarget in
            FStarC_List.contains FStarC_Syntax_Syntax.TotalEffect uu___2) in
       if uu___1
       then
         let uu___2 =
           let uu___3 =
             FStarC_Class_Show.show FStarC_Ident.showable_lident
               edge2.mtarget in
           FStarC_Format.fmt1
             "Divergent computations cannot be included in an effect %s marked 'total'"
             uu___3 in
         FStarC_Errors.raise_error hasRange_env env1
           FStarC_Errors_Codes.Fatal_DivergentComputationCannotBeIncludedInTotal
           () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic uu___2)
       else ()) order;
  (let joins =
     let ubs = FStarC_SMap.create (Prims.of_int (10)) in
     let add_ub i j k ik jk =
       let key =
         let uu___1 = FStarC_Ident.string_of_lid i in
         let uu___2 =
           let uu___3 = FStarC_Ident.string_of_lid j in
           Prims.strcat ":" uu___3 in
         Prims.strcat uu___1 uu___2 in
       let v =
         let uu___1 = FStarC_SMap.try_find ubs key in
         match uu___1 with
         | FStar_Pervasives_Native.Some ubs1 -> (i, j, k, ik, jk) :: ubs1
         | FStar_Pervasives_Native.None -> [(i, j, k, ik, jk)] in
       FStarC_SMap.add ubs key v in
     FStarC_List.iter
       (fun i ->
          FStarC_List.iter
            (fun j ->
               let uu___2 = FStarC_Ident.lid_equals i j in
               if uu___2
               then ()
               else
                 FStarC_List.iter
                   (fun k ->
                      let uu___4 =
                        let uu___5 = find_edge order (i, k) in
                        let uu___6 = find_edge order (j, k) in
                        (uu___5, uu___6) in
                      match uu___4 with
                      | (FStar_Pervasives_Native.Some ik,
                         FStar_Pervasives_Native.Some jk) ->
                          add_ub i j k ik.mlift jk.mlift
                      | uu___5 -> ()) ms) ms) ms;
     FStarC_SMap.fold ubs
       (fun s l joins1 ->
          let lubs =
            FStarC_List.filter
              (fun uu___2 ->
                 match uu___2 with
                 | (i, j, k, ik, jk) ->
                     FStarC_List.for_all
                       (fun uu___3 ->
                          match uu___3 with
                          | (uu___4, uu___5, k', uu___6, uu___7) ->
                              let uu___8 = find_edge order (k, k') in
                              FStar_Pervasives_Native.uu___is_Some uu___8) l)
              l in
          if (FStarC_List.length lubs) <> Prims.int_one
          then
            let uu___2 =
              FStarC_Format.fmt1 "Effects %s have incomparable upper bounds"
                s in
            FStarC_Errors.raise_error hasRange_env env1
              FStarC_Errors_Codes.Fatal_Effects_Ordering_Coherence ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2)
          else FStarC_List.op_At lubs joins1) [] in
   let effects1 =
     let uu___1 = env1.effects in
     {
       decls = (uu___1.decls);
       order;
       joins;
       polymonadic_binds = (uu___1.polymonadic_binds);
       polymonadic_subcomps = (uu___1.polymonadic_subcomps)
     } in
   {
     solver = (env1.solver);
     range = (env1.range);
     curmodule = (env1.curmodule);
     gamma = (env1.gamma);
     gamma_sig = (env1.gamma_sig);
     gamma_cache = (env1.gamma_cache);
     modules = (env1.modules);
     expected_typ = (env1.expected_typ);
     sigtab = (env1.sigtab);
     attrtab = (env1.attrtab);
     instantiate_imp = (env1.instantiate_imp);
     effects = effects1;
     generalize = (env1.generalize);
     letrecs = (env1.letrecs);
     top_level = (env1.top_level);
     check_uvars = (env1.check_uvars);
     use_eq_strict = (env1.use_eq_strict);
     is_iface = (env1.is_iface);
     admit = (env1.admit);
     phase1 = (env1.phase1);
     failhard = (env1.failhard);
     flychecking = (env1.flychecking);
     uvar_subtyping = (env1.uvar_subtyping);
     intactics = (env1.intactics);
     nocoerce = (env1.nocoerce);
     tc_term = (env1.tc_term);
     typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
     universe_of = (env1.universe_of);
     typeof_well_typed_tot_or_gtot_term =
       (env1.typeof_well_typed_tot_or_gtot_term);
     teq_nosmt_force = (env1.teq_nosmt_force);
     subtype_nosmt_force = (env1.subtype_nosmt_force);
     qtbl_name_and_index = (env1.qtbl_name_and_index);
     normalized_eff_names = (env1.normalized_eff_names);
     fv_delta_depths = (env1.fv_delta_depths);
     proof_ns = (env1.proof_ns);
     synth_hook = (env1.synth_hook);
     try_solve_implicits_hook = (env1.try_solve_implicits_hook);
     splice = (env1.splice);
     mpreprocess = (env1.mpreprocess);
     postprocess = (env1.postprocess);
     identifier_info = (env1.identifier_info);
     tc_hooks = (env1.tc_hooks);
     dsenv = (env1.dsenv);
     nbe = (env1.nbe);
     strict_args_tab = (env1.strict_args_tab);
     erasable_types_tab = (env1.erasable_types_tab);
     enable_defer_to_tac = (env1.enable_defer_to_tac);
     unif_allow_ref_guards = (env1.unif_allow_ref_guards);
     erase_erasable_args = (env1.erase_erasable_args);
     core_check = (env1.core_check);
     missing_decl = (env1.missing_decl)
   })
let add_polymonadic_bind (env1 : env) (m : FStarC_Ident.lident)
  (n : FStarC_Ident.lident) (p : FStarC_Ident.lident)
  (ty : polymonadic_bind_t) : env=
  {
    solver = (env1.solver);
    range = (env1.range);
    curmodule = (env1.curmodule);
    gamma = (env1.gamma);
    gamma_sig = (env1.gamma_sig);
    gamma_cache = (env1.gamma_cache);
    modules = (env1.modules);
    expected_typ = (env1.expected_typ);
    sigtab = (env1.sigtab);
    attrtab = (env1.attrtab);
    instantiate_imp = (env1.instantiate_imp);
    effects =
      (let uu___ = env1.effects in
       {
         decls = (uu___.decls);
         order = (uu___.order);
         joins = (uu___.joins);
         polymonadic_binds = ((m, n, p, ty) ::
           ((env1.effects).polymonadic_binds));
         polymonadic_subcomps = (uu___.polymonadic_subcomps)
       });
    generalize = (env1.generalize);
    letrecs = (env1.letrecs);
    top_level = (env1.top_level);
    check_uvars = (env1.check_uvars);
    use_eq_strict = (env1.use_eq_strict);
    is_iface = (env1.is_iface);
    admit = (env1.admit);
    phase1 = (env1.phase1);
    failhard = (env1.failhard);
    flychecking = (env1.flychecking);
    uvar_subtyping = (env1.uvar_subtyping);
    intactics = (env1.intactics);
    nocoerce = (env1.nocoerce);
    tc_term = (env1.tc_term);
    typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
    universe_of = (env1.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env1.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env1.teq_nosmt_force);
    subtype_nosmt_force = (env1.subtype_nosmt_force);
    qtbl_name_and_index = (env1.qtbl_name_and_index);
    normalized_eff_names = (env1.normalized_eff_names);
    fv_delta_depths = (env1.fv_delta_depths);
    proof_ns = (env1.proof_ns);
    synth_hook = (env1.synth_hook);
    try_solve_implicits_hook = (env1.try_solve_implicits_hook);
    splice = (env1.splice);
    mpreprocess = (env1.mpreprocess);
    postprocess = (env1.postprocess);
    identifier_info = (env1.identifier_info);
    tc_hooks = (env1.tc_hooks);
    dsenv = (env1.dsenv);
    nbe = (env1.nbe);
    strict_args_tab = (env1.strict_args_tab);
    erasable_types_tab = (env1.erasable_types_tab);
    enable_defer_to_tac = (env1.enable_defer_to_tac);
    unif_allow_ref_guards = (env1.unif_allow_ref_guards);
    erase_erasable_args = (env1.erase_erasable_args);
    core_check = (env1.core_check);
    missing_decl = (env1.missing_decl)
  }
let add_polymonadic_subcomp (env1 : env) (m : FStarC_Ident.lident)
  (n : FStarC_Ident.lident)
  (uu___ :
    (FStarC_Syntax_Syntax.tscheme *
      FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  : env=
  match uu___ with
  | (ts, k) ->
      {
        solver = (env1.solver);
        range = (env1.range);
        curmodule = (env1.curmodule);
        gamma = (env1.gamma);
        gamma_sig = (env1.gamma_sig);
        gamma_cache = (env1.gamma_cache);
        modules = (env1.modules);
        expected_typ = (env1.expected_typ);
        sigtab = (env1.sigtab);
        attrtab = (env1.attrtab);
        instantiate_imp = (env1.instantiate_imp);
        effects =
          (let uu___1 = env1.effects in
           {
             decls = (uu___1.decls);
             order = (uu___1.order);
             joins = (uu___1.joins);
             polymonadic_binds = (uu___1.polymonadic_binds);
             polymonadic_subcomps = ((m, n, ts, k) ::
               ((env1.effects).polymonadic_subcomps))
           });
        generalize = (env1.generalize);
        letrecs = (env1.letrecs);
        top_level = (env1.top_level);
        check_uvars = (env1.check_uvars);
        use_eq_strict = (env1.use_eq_strict);
        is_iface = (env1.is_iface);
        admit = (env1.admit);
        phase1 = (env1.phase1);
        failhard = (env1.failhard);
        flychecking = (env1.flychecking);
        uvar_subtyping = (env1.uvar_subtyping);
        intactics = (env1.intactics);
        nocoerce = (env1.nocoerce);
        tc_term = (env1.tc_term);
        typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
        universe_of = (env1.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (env1.typeof_well_typed_tot_or_gtot_term);
        teq_nosmt_force = (env1.teq_nosmt_force);
        subtype_nosmt_force = (env1.subtype_nosmt_force);
        qtbl_name_and_index = (env1.qtbl_name_and_index);
        normalized_eff_names = (env1.normalized_eff_names);
        fv_delta_depths = (env1.fv_delta_depths);
        proof_ns = (env1.proof_ns);
        synth_hook = (env1.synth_hook);
        try_solve_implicits_hook = (env1.try_solve_implicits_hook);
        splice = (env1.splice);
        mpreprocess = (env1.mpreprocess);
        postprocess = (env1.postprocess);
        identifier_info = (env1.identifier_info);
        tc_hooks = (env1.tc_hooks);
        dsenv = (env1.dsenv);
        nbe = (env1.nbe);
        strict_args_tab = (env1.strict_args_tab);
        erasable_types_tab = (env1.erasable_types_tab);
        enable_defer_to_tac = (env1.enable_defer_to_tac);
        unif_allow_ref_guards = (env1.unif_allow_ref_guards);
        erase_erasable_args = (env1.erase_erasable_args);
        core_check = (env1.core_check);
        missing_decl = (env1.missing_decl)
      }
let push_local_binding (env1 : env) (b : FStarC_Syntax_Syntax.binding) : 
  env=
  {
    solver = (env1.solver);
    range = (env1.range);
    curmodule = (env1.curmodule);
    gamma = (b :: (env1.gamma));
    gamma_sig = (env1.gamma_sig);
    gamma_cache = (env1.gamma_cache);
    modules = (env1.modules);
    expected_typ = (env1.expected_typ);
    sigtab = (env1.sigtab);
    attrtab = (env1.attrtab);
    instantiate_imp = (env1.instantiate_imp);
    effects = (env1.effects);
    generalize = (env1.generalize);
    letrecs = (env1.letrecs);
    top_level = (env1.top_level);
    check_uvars = (env1.check_uvars);
    use_eq_strict = (env1.use_eq_strict);
    is_iface = (env1.is_iface);
    admit = (env1.admit);
    phase1 = (env1.phase1);
    failhard = (env1.failhard);
    flychecking = (env1.flychecking);
    uvar_subtyping = (env1.uvar_subtyping);
    intactics = (env1.intactics);
    nocoerce = (env1.nocoerce);
    tc_term = (env1.tc_term);
    typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
    universe_of = (env1.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env1.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env1.teq_nosmt_force);
    subtype_nosmt_force = (env1.subtype_nosmt_force);
    qtbl_name_and_index = (env1.qtbl_name_and_index);
    normalized_eff_names = (env1.normalized_eff_names);
    fv_delta_depths = (env1.fv_delta_depths);
    proof_ns = (env1.proof_ns);
    synth_hook = (env1.synth_hook);
    try_solve_implicits_hook = (env1.try_solve_implicits_hook);
    splice = (env1.splice);
    mpreprocess = (env1.mpreprocess);
    postprocess = (env1.postprocess);
    identifier_info = (env1.identifier_info);
    tc_hooks = (env1.tc_hooks);
    dsenv = (env1.dsenv);
    nbe = (env1.nbe);
    strict_args_tab = (env1.strict_args_tab);
    erasable_types_tab = (env1.erasable_types_tab);
    enable_defer_to_tac = (env1.enable_defer_to_tac);
    unif_allow_ref_guards = (env1.unif_allow_ref_guards);
    erase_erasable_args = (env1.erase_erasable_args);
    core_check = (env1.core_check);
    missing_decl = (env1.missing_decl)
  }
let push_bv (env1 : env) (x : FStarC_Syntax_Syntax.bv) : env=
  push_local_binding env1 (FStarC_Syntax_Syntax.Binding_var x)
let push_bvs (env1 : env) (bvs : FStarC_Syntax_Syntax.bv Prims.list) : 
  env= FStarC_List.fold_left (fun env2 bv -> push_bv env2 bv) env1 bvs
let pop_bv (env1 : env) :
  (FStarC_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option=
  match env1.gamma with
  | (FStarC_Syntax_Syntax.Binding_var x)::rest ->
      FStar_Pervasives_Native.Some
        (x,
          {
            solver = (env1.solver);
            range = (env1.range);
            curmodule = (env1.curmodule);
            gamma = rest;
            gamma_sig = (env1.gamma_sig);
            gamma_cache = (env1.gamma_cache);
            modules = (env1.modules);
            expected_typ = (env1.expected_typ);
            sigtab = (env1.sigtab);
            attrtab = (env1.attrtab);
            instantiate_imp = (env1.instantiate_imp);
            effects = (env1.effects);
            generalize = (env1.generalize);
            letrecs = (env1.letrecs);
            top_level = (env1.top_level);
            check_uvars = (env1.check_uvars);
            use_eq_strict = (env1.use_eq_strict);
            is_iface = (env1.is_iface);
            admit = (env1.admit);
            phase1 = (env1.phase1);
            failhard = (env1.failhard);
            flychecking = (env1.flychecking);
            uvar_subtyping = (env1.uvar_subtyping);
            intactics = (env1.intactics);
            nocoerce = (env1.nocoerce);
            tc_term = (env1.tc_term);
            typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
            universe_of = (env1.universe_of);
            typeof_well_typed_tot_or_gtot_term =
              (env1.typeof_well_typed_tot_or_gtot_term);
            teq_nosmt_force = (env1.teq_nosmt_force);
            subtype_nosmt_force = (env1.subtype_nosmt_force);
            qtbl_name_and_index = (env1.qtbl_name_and_index);
            normalized_eff_names = (env1.normalized_eff_names);
            fv_delta_depths = (env1.fv_delta_depths);
            proof_ns = (env1.proof_ns);
            synth_hook = (env1.synth_hook);
            try_solve_implicits_hook = (env1.try_solve_implicits_hook);
            splice = (env1.splice);
            mpreprocess = (env1.mpreprocess);
            postprocess = (env1.postprocess);
            identifier_info = (env1.identifier_info);
            tc_hooks = (env1.tc_hooks);
            dsenv = (env1.dsenv);
            nbe = (env1.nbe);
            strict_args_tab = (env1.strict_args_tab);
            erasable_types_tab = (env1.erasable_types_tab);
            enable_defer_to_tac = (env1.enable_defer_to_tac);
            unif_allow_ref_guards = (env1.unif_allow_ref_guards);
            erase_erasable_args = (env1.erase_erasable_args);
            core_check = (env1.core_check);
            missing_decl = (env1.missing_decl)
          })
  | uu___ -> FStar_Pervasives_Native.None
let push_binders (env1 : env) (bs : FStarC_Syntax_Syntax.binders) : env=
  FStarC_List.fold_left
    (fun env2 b -> push_bv env2 b.FStarC_Syntax_Syntax.binder_bv) env1 bs
let binding_of_lb (x : FStarC_Syntax_Syntax.lbname)
  (t :
    (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax))
  : FStarC_Syntax_Syntax.binding=
  match x with
  | FStar_Pervasives.Inl x1 ->
      let x2 =
        {
          FStarC_Syntax_Syntax.ppname = (x1.FStarC_Syntax_Syntax.ppname);
          FStarC_Syntax_Syntax.index = (x1.FStarC_Syntax_Syntax.index);
          FStarC_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
        } in
      FStarC_Syntax_Syntax.Binding_var x2
  | FStar_Pervasives.Inr fv ->
      FStarC_Syntax_Syntax.Binding_lid ((fv.FStarC_Syntax_Syntax.fv_name), t)
let push_let_binding (env1 : env) (lb : FStarC_Syntax_Syntax.lbname)
  (ts : FStarC_Syntax_Syntax.tscheme) : env=
  push_local_binding env1 (binding_of_lb lb ts)
let push_univ_vars (env1 : env_t) (xs : FStarC_Syntax_Syntax.univ_names) :
  env=
  FStarC_List.fold_left
    (fun env2 x ->
       push_local_binding env2 (FStarC_Syntax_Syntax.Binding_univ x)) env1 xs
let open_universes_in (env1 : env) (uvs : FStarC_Syntax_Syntax.univ_names)
  (terms : FStarC_Syntax_Syntax.term Prims.list) :
  (env * FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term
    Prims.list)=
  let uu___ = FStarC_Syntax_Subst.univ_var_opening uvs in
  match uu___ with
  | (univ_subst, univ_vars) ->
      let env' = push_univ_vars env1 univ_vars in
      let uu___1 =
        FStarC_List.map (FStarC_Syntax_Subst.subst univ_subst) terms in
      (env', univ_vars, uu___1)
let set_expected_typ (env1 : env) (t : FStarC_Syntax_Syntax.typ) : env=
  {
    solver = (env1.solver);
    range = (env1.range);
    curmodule = (env1.curmodule);
    gamma = (env1.gamma);
    gamma_sig = (env1.gamma_sig);
    gamma_cache = (env1.gamma_cache);
    modules = (env1.modules);
    expected_typ = (FStar_Pervasives_Native.Some (t, false));
    sigtab = (env1.sigtab);
    attrtab = (env1.attrtab);
    instantiate_imp = (env1.instantiate_imp);
    effects = (env1.effects);
    generalize = (env1.generalize);
    letrecs = (env1.letrecs);
    top_level = (env1.top_level);
    check_uvars = (env1.check_uvars);
    use_eq_strict = (env1.use_eq_strict);
    is_iface = (env1.is_iface);
    admit = (env1.admit);
    phase1 = (env1.phase1);
    failhard = (env1.failhard);
    flychecking = (env1.flychecking);
    uvar_subtyping = (env1.uvar_subtyping);
    intactics = (env1.intactics);
    nocoerce = (env1.nocoerce);
    tc_term = (env1.tc_term);
    typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
    universe_of = (env1.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env1.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env1.teq_nosmt_force);
    subtype_nosmt_force = (env1.subtype_nosmt_force);
    qtbl_name_and_index = (env1.qtbl_name_and_index);
    normalized_eff_names = (env1.normalized_eff_names);
    fv_delta_depths = (env1.fv_delta_depths);
    proof_ns = (env1.proof_ns);
    synth_hook = (env1.synth_hook);
    try_solve_implicits_hook = (env1.try_solve_implicits_hook);
    splice = (env1.splice);
    mpreprocess = (env1.mpreprocess);
    postprocess = (env1.postprocess);
    identifier_info = (env1.identifier_info);
    tc_hooks = (env1.tc_hooks);
    dsenv = (env1.dsenv);
    nbe = (env1.nbe);
    strict_args_tab = (env1.strict_args_tab);
    erasable_types_tab = (env1.erasable_types_tab);
    enable_defer_to_tac = (env1.enable_defer_to_tac);
    unif_allow_ref_guards = (env1.unif_allow_ref_guards);
    erase_erasable_args = (env1.erase_erasable_args);
    core_check = (env1.core_check);
    missing_decl = (env1.missing_decl)
  }
let set_expected_typ_maybe_eq (env1 : env) (t : FStarC_Syntax_Syntax.typ)
  (use_eq : Prims.bool) : env=
  {
    solver = (env1.solver);
    range = (env1.range);
    curmodule = (env1.curmodule);
    gamma = (env1.gamma);
    gamma_sig = (env1.gamma_sig);
    gamma_cache = (env1.gamma_cache);
    modules = (env1.modules);
    expected_typ = (FStar_Pervasives_Native.Some (t, use_eq));
    sigtab = (env1.sigtab);
    attrtab = (env1.attrtab);
    instantiate_imp = (env1.instantiate_imp);
    effects = (env1.effects);
    generalize = (env1.generalize);
    letrecs = (env1.letrecs);
    top_level = (env1.top_level);
    check_uvars = (env1.check_uvars);
    use_eq_strict = (env1.use_eq_strict);
    is_iface = (env1.is_iface);
    admit = (env1.admit);
    phase1 = (env1.phase1);
    failhard = (env1.failhard);
    flychecking = (env1.flychecking);
    uvar_subtyping = (env1.uvar_subtyping);
    intactics = (env1.intactics);
    nocoerce = (env1.nocoerce);
    tc_term = (env1.tc_term);
    typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
    universe_of = (env1.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (env1.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (env1.teq_nosmt_force);
    subtype_nosmt_force = (env1.subtype_nosmt_force);
    qtbl_name_and_index = (env1.qtbl_name_and_index);
    normalized_eff_names = (env1.normalized_eff_names);
    fv_delta_depths = (env1.fv_delta_depths);
    proof_ns = (env1.proof_ns);
    synth_hook = (env1.synth_hook);
    try_solve_implicits_hook = (env1.try_solve_implicits_hook);
    splice = (env1.splice);
    mpreprocess = (env1.mpreprocess);
    postprocess = (env1.postprocess);
    identifier_info = (env1.identifier_info);
    tc_hooks = (env1.tc_hooks);
    dsenv = (env1.dsenv);
    nbe = (env1.nbe);
    strict_args_tab = (env1.strict_args_tab);
    erasable_types_tab = (env1.erasable_types_tab);
    enable_defer_to_tac = (env1.enable_defer_to_tac);
    unif_allow_ref_guards = (env1.unif_allow_ref_guards);
    erase_erasable_args = (env1.erase_erasable_args);
    core_check = (env1.core_check);
    missing_decl = (env1.missing_decl)
  }
let expected_typ (env1 : env) :
  (FStarC_Syntax_Syntax.typ * Prims.bool) FStar_Pervasives_Native.option=
  match env1.expected_typ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let clear_expected_typ (env_ : env) :
  (env * (FStarC_Syntax_Syntax.typ * Prims.bool)
    FStar_Pervasives_Native.option)=
  let uu___ = expected_typ env_ in
  ({
     solver = (env_.solver);
     range = (env_.range);
     curmodule = (env_.curmodule);
     gamma = (env_.gamma);
     gamma_sig = (env_.gamma_sig);
     gamma_cache = (env_.gamma_cache);
     modules = (env_.modules);
     expected_typ = FStar_Pervasives_Native.None;
     sigtab = (env_.sigtab);
     attrtab = (env_.attrtab);
     instantiate_imp = (env_.instantiate_imp);
     effects = (env_.effects);
     generalize = (env_.generalize);
     letrecs = (env_.letrecs);
     top_level = (env_.top_level);
     check_uvars = (env_.check_uvars);
     use_eq_strict = (env_.use_eq_strict);
     is_iface = (env_.is_iface);
     admit = (env_.admit);
     phase1 = (env_.phase1);
     failhard = (env_.failhard);
     flychecking = (env_.flychecking);
     uvar_subtyping = (env_.uvar_subtyping);
     intactics = (env_.intactics);
     nocoerce = (env_.nocoerce);
     tc_term = (env_.tc_term);
     typeof_tot_or_gtot_term = (env_.typeof_tot_or_gtot_term);
     universe_of = (env_.universe_of);
     typeof_well_typed_tot_or_gtot_term =
       (env_.typeof_well_typed_tot_or_gtot_term);
     teq_nosmt_force = (env_.teq_nosmt_force);
     subtype_nosmt_force = (env_.subtype_nosmt_force);
     qtbl_name_and_index = (env_.qtbl_name_and_index);
     normalized_eff_names = (env_.normalized_eff_names);
     fv_delta_depths = (env_.fv_delta_depths);
     proof_ns = (env_.proof_ns);
     synth_hook = (env_.synth_hook);
     try_solve_implicits_hook = (env_.try_solve_implicits_hook);
     splice = (env_.splice);
     mpreprocess = (env_.mpreprocess);
     postprocess = (env_.postprocess);
     identifier_info = (env_.identifier_info);
     tc_hooks = (env_.tc_hooks);
     dsenv = (env_.dsenv);
     nbe = (env_.nbe);
     strict_args_tab = (env_.strict_args_tab);
     erasable_types_tab = (env_.erasable_types_tab);
     enable_defer_to_tac = (env_.enable_defer_to_tac);
     unif_allow_ref_guards = (env_.unif_allow_ref_guards);
     erase_erasable_args = (env_.erase_erasable_args);
     core_check = (env_.core_check);
     missing_decl = (env_.missing_decl)
   }, uu___)
let finish_module : env -> FStarC_Syntax_Syntax.modul -> env=
  let empty_lid =
    let uu___ = let uu___1 = FStarC_Ident.id_of_text "" in [uu___1] in
    FStarC_Ident.lid_of_ids uu___ in
  fun env1 m ->
    {
      solver = (env1.solver);
      range = (env1.range);
      curmodule = empty_lid;
      gamma = [];
      gamma_sig = [];
      gamma_cache = (env1.gamma_cache);
      modules = (m :: (env1.modules));
      expected_typ = (env1.expected_typ);
      sigtab = (env1.sigtab);
      attrtab = (env1.attrtab);
      instantiate_imp = (env1.instantiate_imp);
      effects = (env1.effects);
      generalize = (env1.generalize);
      letrecs = (env1.letrecs);
      top_level = (env1.top_level);
      check_uvars = (env1.check_uvars);
      use_eq_strict = (env1.use_eq_strict);
      is_iface = (env1.is_iface);
      admit = (env1.admit);
      phase1 = (env1.phase1);
      failhard = (env1.failhard);
      flychecking = (env1.flychecking);
      uvar_subtyping = (env1.uvar_subtyping);
      intactics = (env1.intactics);
      nocoerce = (env1.nocoerce);
      tc_term = (env1.tc_term);
      typeof_tot_or_gtot_term = (env1.typeof_tot_or_gtot_term);
      universe_of = (env1.universe_of);
      typeof_well_typed_tot_or_gtot_term =
        (env1.typeof_well_typed_tot_or_gtot_term);
      teq_nosmt_force = (env1.teq_nosmt_force);
      subtype_nosmt_force = (env1.subtype_nosmt_force);
      qtbl_name_and_index = (env1.qtbl_name_and_index);
      normalized_eff_names = (env1.normalized_eff_names);
      fv_delta_depths = (env1.fv_delta_depths);
      proof_ns = (env1.proof_ns);
      synth_hook = (env1.synth_hook);
      try_solve_implicits_hook = (env1.try_solve_implicits_hook);
      splice = (env1.splice);
      mpreprocess = (env1.mpreprocess);
      postprocess = (env1.postprocess);
      identifier_info = (env1.identifier_info);
      tc_hooks = (env1.tc_hooks);
      dsenv = (env1.dsenv);
      nbe = (env1.nbe);
      strict_args_tab = (env1.strict_args_tab);
      erasable_types_tab = (env1.erasable_types_tab);
      enable_defer_to_tac = (env1.enable_defer_to_tac);
      unif_allow_ref_guards = (env1.unif_allow_ref_guards);
      erase_erasable_args = (env1.erase_erasable_args);
      core_check = (env1.core_check);
      missing_decl = (env1.missing_decl)
    }
let uvars_in_env (env1 : env) : FStarC_Syntax_Syntax.uvars=
  let no_uvs =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic
            (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Free.ord_ctx_uvar))
         ()) in
  let rec aux out g =
    match g with
    | [] -> out
    | (FStarC_Syntax_Syntax.Binding_univ uu___)::tl -> aux out tl
    | (FStarC_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.uvars t in
          Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic out)
               (Obj.magic uu___3)) in
        aux uu___2 tl
    | (FStarC_Syntax_Syntax.Binding_var
        { FStarC_Syntax_Syntax.ppname = uu___;
          FStarC_Syntax_Syntax.index = uu___1;
          FStarC_Syntax_Syntax.sort = t;_})::tl
        ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.uvars t in
          Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic out)
               (Obj.magic uu___3)) in
        aux uu___2 tl in
  aux no_uvs env1.gamma
let univ_vars (env1 : env) :
  FStarC_Syntax_Syntax.universe_uvar FStarC_FlatSet.t=
  let no_univs =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic
            (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Free.ord_univ_uvar))
         ()) in
  let rec aux out g =
    match g with
    | [] -> out
    | (FStarC_Syntax_Syntax.Binding_univ uu___)::tl -> aux out tl
    | (FStarC_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.univs t in
          Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic out)
               (Obj.magic uu___3)) in
        aux uu___2 tl
    | (FStarC_Syntax_Syntax.Binding_var
        { FStarC_Syntax_Syntax.ppname = uu___;
          FStarC_Syntax_Syntax.index = uu___1;
          FStarC_Syntax_Syntax.sort = t;_})::tl
        ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.univs t in
          Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic out)
               (Obj.magic uu___3)) in
        aux uu___2 tl in
  aux no_univs env1.gamma
let univnames (env1 : env) : FStarC_Syntax_Syntax.univ_name FStarC_FlatSet.t=
  let no_univ_names =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic
            (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_ident))
         ()) in
  let rec aux out g =
    match g with
    | [] -> out
    | (FStarC_Syntax_Syntax.Binding_univ uname)::tl ->
        let uu___ =
          Obj.magic
            (FStarC_Class_Setlike.add ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_ident)) uname (Obj.magic out)) in
        aux uu___ tl
    | (FStarC_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.univnames t in
          Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_ident)) (Obj.magic out)
               (Obj.magic uu___3)) in
        aux uu___2 tl
    | (FStarC_Syntax_Syntax.Binding_var
        { FStarC_Syntax_Syntax.ppname = uu___;
          FStarC_Syntax_Syntax.index = uu___1;
          FStarC_Syntax_Syntax.sort = t;_})::tl
        ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.univnames t in
          Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_ident)) (Obj.magic out)
               (Obj.magic uu___3)) in
        aux uu___2 tl in
  aux no_univ_names env1.gamma
let lidents (env1 : env) : FStarC_Ident.lident Prims.list=
  let keys = FStarC_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
  FStarC_SMap.fold (sigtab env1)
    (fun uu___ v keys1 ->
       let uu___1 = FStarC_Syntax_Util.lids_of_sigelt v in
       FStarC_List.op_At uu___1 keys1) keys
let should_enc_path
  (proof_ns : (Prims.string Prims.list * Prims.bool) Prims.list)
  (path : Prims.string Prims.list) : Prims.bool=
  let rec str_i_prefix xs ys =
    match (xs, ys) with
    | ([], uu___) -> true
    | (x::xs1, y::ys1) ->
        ((FStarC_String.lowercase x) = (FStarC_String.lowercase y)) &&
          (str_i_prefix xs1 ys1)
    | (uu___, uu___1) -> false in
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (p, uu___2) -> str_i_prefix p path)
      proof_ns in
  match uu___ with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some (uu___1, b) -> b
let should_enc_lid (proof_ns : proof_namespace) (lid : FStarC_Ident.lident) :
  Prims.bool=
  let uu___ = FStarC_Ident.path_of_lid lid in should_enc_path proof_ns uu___
let cons_proof_ns (b : Prims.bool) (e : env) (path : name_prefix) : env=
  {
    solver = (e.solver);
    range = (e.range);
    curmodule = (e.curmodule);
    gamma = (e.gamma);
    gamma_sig = (e.gamma_sig);
    gamma_cache = (e.gamma_cache);
    modules = (e.modules);
    expected_typ = (e.expected_typ);
    sigtab = (e.sigtab);
    attrtab = (e.attrtab);
    instantiate_imp = (e.instantiate_imp);
    effects = (e.effects);
    generalize = (e.generalize);
    letrecs = (e.letrecs);
    top_level = (e.top_level);
    check_uvars = (e.check_uvars);
    use_eq_strict = (e.use_eq_strict);
    is_iface = (e.is_iface);
    admit = (e.admit);
    phase1 = (e.phase1);
    failhard = (e.failhard);
    flychecking = (e.flychecking);
    uvar_subtyping = (e.uvar_subtyping);
    intactics = (e.intactics);
    nocoerce = (e.nocoerce);
    tc_term = (e.tc_term);
    typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
    universe_of = (e.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (e.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (e.teq_nosmt_force);
    subtype_nosmt_force = (e.subtype_nosmt_force);
    qtbl_name_and_index = (e.qtbl_name_and_index);
    normalized_eff_names = (e.normalized_eff_names);
    fv_delta_depths = (e.fv_delta_depths);
    proof_ns = ((path, b) :: (e.proof_ns));
    synth_hook = (e.synth_hook);
    try_solve_implicits_hook = (e.try_solve_implicits_hook);
    splice = (e.splice);
    mpreprocess = (e.mpreprocess);
    postprocess = (e.postprocess);
    identifier_info = (e.identifier_info);
    tc_hooks = (e.tc_hooks);
    dsenv = (e.dsenv);
    nbe = (e.nbe);
    strict_args_tab = (e.strict_args_tab);
    erasable_types_tab = (e.erasable_types_tab);
    enable_defer_to_tac = (e.enable_defer_to_tac);
    unif_allow_ref_guards = (e.unif_allow_ref_guards);
    erase_erasable_args = (e.erase_erasable_args);
    core_check = (e.core_check);
    missing_decl = (e.missing_decl)
  }
let add_proof_ns (e : env) (path : name_prefix) : env=
  cons_proof_ns true e path
let rem_proof_ns (e : env) (path : name_prefix) : env=
  cons_proof_ns false e path
let get_proof_ns (e : env) : proof_namespace= e.proof_ns
let set_proof_ns (ns : proof_namespace) (e : env) : env=
  {
    solver = (e.solver);
    range = (e.range);
    curmodule = (e.curmodule);
    gamma = (e.gamma);
    gamma_sig = (e.gamma_sig);
    gamma_cache = (e.gamma_cache);
    modules = (e.modules);
    expected_typ = (e.expected_typ);
    sigtab = (e.sigtab);
    attrtab = (e.attrtab);
    instantiate_imp = (e.instantiate_imp);
    effects = (e.effects);
    generalize = (e.generalize);
    letrecs = (e.letrecs);
    top_level = (e.top_level);
    check_uvars = (e.check_uvars);
    use_eq_strict = (e.use_eq_strict);
    is_iface = (e.is_iface);
    admit = (e.admit);
    phase1 = (e.phase1);
    failhard = (e.failhard);
    flychecking = (e.flychecking);
    uvar_subtyping = (e.uvar_subtyping);
    intactics = (e.intactics);
    nocoerce = (e.nocoerce);
    tc_term = (e.tc_term);
    typeof_tot_or_gtot_term = (e.typeof_tot_or_gtot_term);
    universe_of = (e.universe_of);
    typeof_well_typed_tot_or_gtot_term =
      (e.typeof_well_typed_tot_or_gtot_term);
    teq_nosmt_force = (e.teq_nosmt_force);
    subtype_nosmt_force = (e.subtype_nosmt_force);
    qtbl_name_and_index = (e.qtbl_name_and_index);
    normalized_eff_names = (e.normalized_eff_names);
    fv_delta_depths = (e.fv_delta_depths);
    proof_ns = ns;
    synth_hook = (e.synth_hook);
    try_solve_implicits_hook = (e.try_solve_implicits_hook);
    splice = (e.splice);
    mpreprocess = (e.mpreprocess);
    postprocess = (e.postprocess);
    identifier_info = (e.identifier_info);
    tc_hooks = (e.tc_hooks);
    dsenv = (e.dsenv);
    nbe = (e.nbe);
    strict_args_tab = (e.strict_args_tab);
    erasable_types_tab = (e.erasable_types_tab);
    enable_defer_to_tac = (e.enable_defer_to_tac);
    unif_allow_ref_guards = (e.unif_allow_ref_guards);
    erase_erasable_args = (e.erase_erasable_args);
    core_check = (e.core_check);
    missing_decl = (e.missing_decl)
  }
let unbound_vars (e : env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.bv FStarC_FlatSet.t=
  let uu___ = FStarC_Syntax_Free.names t in
  let uu___1 = bound_vars e in
  FStarC_List.fold_left
    (fun uu___3 uu___2 ->
       (fun s bv ->
          Obj.magic
            (FStarC_Class_Setlike.remove ()
               (Obj.magic
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_bv)) bv (Obj.magic s))) uu___3
         uu___2) uu___ uu___1
let closed (e : env) (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = unbound_vars e t in
  FStarC_Class_Setlike.is_empty ()
    (Obj.magic (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv))
    (Obj.magic uu___)
let closed' (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = FStarC_Syntax_Free.names t in
  FStarC_Class_Setlike.is_empty ()
    (Obj.magic (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv))
    (Obj.magic uu___)
let string_of_proof_ns (env1 : env) : Prims.string=
  let aux uu___ =
    match uu___ with
    | (p, b) ->
        if (p = []) && b
        then "*"
        else
          (let uu___2 = FStarC_Ident.text_of_path p in
           Prims.strcat (if b then "+" else "-") uu___2) in
  let uu___ =
    let uu___1 = FStarC_List.map aux env1.proof_ns in FStarC_List.rev uu___1 in
  FStarC_String.concat " " uu___
let guard_of_guard_formula (g : FStarC_TypeChecker_Common.guard_formula) :
  guard_t=
  {
    FStarC_TypeChecker_Common.guard_f = g;
    FStarC_TypeChecker_Common.deferred_to_tac =
      (Obj.magic
         (FStarC_Class_Listlike.empty ()
            (Obj.magic (FStarC_CList.listlike_clist ()))));
    FStarC_TypeChecker_Common.deferred =
      (Obj.magic
         (FStarC_Class_Listlike.empty ()
            (Obj.magic (FStarC_CList.listlike_clist ()))));
    FStarC_TypeChecker_Common.univ_ineqs =
      ((Obj.magic
          (FStarC_Class_Listlike.empty ()
             (Obj.magic (FStarC_CList.listlike_clist ())))),
        (Obj.magic
           (FStarC_Class_Listlike.empty ()
              (Obj.magic (FStarC_CList.listlike_clist ())))));
    FStarC_TypeChecker_Common.implicits =
      (Obj.magic
         (FStarC_Class_Listlike.empty ()
            (Obj.magic (FStarC_CList.listlike_clist ()))))
  }
let guard_form (g : guard_t) : FStarC_TypeChecker_Common.guard_formula=
  g.FStarC_TypeChecker_Common.guard_f
let is_trivial (g : guard_t) : Prims.bool=
  let uu___ =
    (((FStarC_TypeChecker_Common.uu___is_Trivial
         g.FStarC_TypeChecker_Common.guard_f)
        &&
        (FStarC_Class_Listlike.is_empty (FStarC_CList.listlike_clist ())
           g.FStarC_TypeChecker_Common.deferred))
       &&
       (FStarC_Class_Listlike.is_empty (FStarC_CList.listlike_clist ())
          (FStar_Pervasives_Native.fst g.FStarC_TypeChecker_Common.univ_ineqs)))
      &&
      (FStarC_Class_Listlike.is_empty (FStarC_CList.listlike_clist ())
         (FStar_Pervasives_Native.snd g.FStarC_TypeChecker_Common.univ_ineqs)) in
  if uu___
  then
    FStarC_CList.for_all
      (fun imp ->
         (let uu___1 =
            FStarC_Syntax_Util.ctx_uvar_should_check
              imp.FStarC_TypeChecker_Common.imp_uvar in
          FStarC_Syntax_Syntax.uu___is_Allow_unresolved uu___1) ||
           (let uu___1 =
              FStarC_Syntax_Unionfind.find
                (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
            match uu___1 with
            | FStar_Pervasives_Native.Some uu___2 -> true
            | FStar_Pervasives_Native.None -> false))
      g.FStarC_TypeChecker_Common.implicits
  else false
let is_trivial_guard_formula (g : guard_t) : Prims.bool=
  match g with
  | { FStarC_TypeChecker_Common.guard_f = FStarC_TypeChecker_Common.Trivial;
      FStarC_TypeChecker_Common.deferred_to_tac = uu___;
      FStarC_TypeChecker_Common.deferred = uu___1;
      FStarC_TypeChecker_Common.univ_ineqs = uu___2;
      FStarC_TypeChecker_Common.implicits = uu___3;_} -> true
  | uu___ -> false
let trivial_guard : guard_t= FStarC_TypeChecker_Common.trivial_guard
let abstract_guard_n (bs : FStarC_Syntax_Syntax.binder Prims.list)
  (g : guard_t) : guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let f' =
        let uu___ =
          let uu___1 =
            FStarC_Syntax_Util.residual_tot FStarC_Syntax_Util.ktype0 in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Syntax_Util.abs bs f uu___ in
      {
        FStarC_TypeChecker_Common.guard_f =
          (FStarC_TypeChecker_Common.NonTrivial f');
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let abstract_guard (b : FStarC_Syntax_Syntax.binder) (g : guard_t) : 
  guard_t= abstract_guard_n [b] g
let too_early_in_prims (env1 : env) : Prims.bool=
  let uu___ = lid_exists env1 FStarC_Parser_Const.effect_GTot_lid in
  Prims.op_Negation uu___
let apply_guard (g : guard_t) (e : FStarC_Syntax_Syntax.term) : guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Syntax_Syntax.as_arg e in [uu___5] in
              {
                FStarC_Syntax_Syntax.hd = f;
                FStarC_Syntax_Syntax.args = uu___4
              } in
            FStarC_Syntax_Syntax.Tm_app uu___3 in
          FStarC_Syntax_Syntax.mk uu___2 f.FStarC_Syntax_Syntax.pos in
        FStarC_TypeChecker_Common.NonTrivial uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f = uu___;
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let map_guard (g : guard_t)
  (map : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) : guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let uu___ =
        let uu___1 = map f in FStarC_TypeChecker_Common.NonTrivial uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f = uu___;
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let always_map_guard (g : guard_t)
  (map : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) : guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial ->
      let uu___ =
        let uu___1 = map FStarC_Syntax_Util.t_true in
        FStarC_TypeChecker_Common.NonTrivial uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f = uu___;
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let uu___ =
        let uu___1 = map f in FStarC_TypeChecker_Common.NonTrivial uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f = uu___;
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let trivial (t : FStarC_TypeChecker_Common.guard_formula) : unit=
  match t with
  | FStarC_TypeChecker_Common.Trivial -> ()
  | FStarC_TypeChecker_Common.NonTrivial uu___ -> failwith "impossible"
let check_trivial (t : FStarC_Syntax_Syntax.term) :
  FStarC_TypeChecker_Common.guard_formula=
  FStarC_TypeChecker_Common.check_trivial t
let conj_guard (g1 : guard_t) (g2 : guard_t) : guard_t=
  FStarC_TypeChecker_Common.conj_guard g1 g2
let conj_guards (gs : guard_t Prims.list) : guard_t=
  FStarC_TypeChecker_Common.conj_guards gs
let imp_guard (g1 : guard_t) (g2 : guard_t) : guard_t=
  FStarC_TypeChecker_Common.imp_guard g1 g2
let close_guard_univs (us : FStarC_Syntax_Syntax.universes)
  (bs : FStarC_Syntax_Syntax.binders) (g : guard_t) : guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let f1 =
        FStarC_List.fold_right2
          (fun u b f2 ->
             let uu___ = FStarC_Syntax_Syntax.is_null_binder b in
             if uu___
             then f2
             else
               FStarC_Syntax_Util.mk_forall u
                 b.FStarC_Syntax_Syntax.binder_bv f2) us bs f in
      {
        FStarC_TypeChecker_Common.guard_f =
          (FStarC_TypeChecker_Common.NonTrivial f1);
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let close_forall (env1 : env) (bs : FStarC_Syntax_Syntax.binders)
  (f : FStarC_Syntax_Syntax.formula) : FStarC_Syntax_Syntax.term=
  FStarC_Errors.with_ctx "While closing a formula"
    (fun uu___ ->
       (let uu___2 =
          let uu___3 = FStarC_Syntax_Syntax.mk_Total f in
          FStarC_Syntax_Util.arrow bs uu___3 in
        FStarC_Defensive.def_check_scoped hasBinders_env
          FStarC_Class_Binders.hasNames_term FStarC_Syntax_Print.pretty_term
          f.FStarC_Syntax_Syntax.pos "close_forall" env1 uu___2);
       (let bvs =
          FStarC_List.map (fun b -> b.FStarC_Syntax_Syntax.binder_bv) bs in
        let env_full = push_bvs env1 bvs in
        let uu___2 =
          FStarC_List.fold_right
            (fun bv uu___3 ->
               match uu___3 with
               | (f1, e) ->
                   let e' =
                     let uu___4 =
                       let uu___5 = pop_bv e in FStarC_Option.must uu___5 in
                     FStar_Pervasives_Native.snd uu___4 in
                   (FStarC_Defensive.def_check_scoped hasBinders_env
                      FStarC_Class_Binders.hasNames_term
                      FStarC_Syntax_Print.pretty_term
                      FStarC_Range_Type.dummyRange "close_forall.sort" e'
                      bv.FStarC_Syntax_Syntax.sort;
                    (let f' =
                       let uu___5 = FStarC_Syntax_Syntax.is_null_bv bv in
                       if uu___5
                       then f1
                       else
                         (let u =
                            e'.universe_of e' bv.FStarC_Syntax_Syntax.sort in
                          FStarC_Syntax_Util.mk_forall u bv f1) in
                     (f', e')))) bvs (f, env_full) in
        match uu___2 with | (f', e) -> f'))
let close_guard (env1 : env) (binders : FStarC_Syntax_Syntax.binders)
  (g : guard_t) : guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let uu___ =
        let uu___1 = close_forall env1 binders f in
        FStarC_TypeChecker_Common.NonTrivial uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f = uu___;
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let new_tac_implicit_var (reason : Prims.string) (r : FStarC_Range_Type.t)
  (env1 : env) (uvar_typ : FStarC_Syntax_Syntax.typ)
  (should_check : FStarC_Syntax_Syntax.should_check_uvar)
  (uvar_typedness_deps : FStarC_Syntax_Syntax.ctx_uvar Prims.list)
  (meta :
    FStarC_Syntax_Syntax.ctx_uvar_meta_t FStar_Pervasives_Native.option)
  (unrefine : Prims.bool) :
  (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.ctx_uvar *
    FStarC_Range_Type.t) * guard_t)=
  let binders = all_binders env1 in
  let gamma = env1.gamma in
  let decoration =
    {
      FStarC_Syntax_Syntax.uvar_decoration_typ = uvar_typ;
      FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on =
        uvar_typedness_deps;
      FStarC_Syntax_Syntax.uvar_decoration_should_check = should_check;
      FStarC_Syntax_Syntax.uvar_decoration_should_unrefine = unrefine
    } in
  let ctx_uvar =
    let uu___ = FStarC_Syntax_Unionfind.fresh decoration r in
    {
      FStarC_Syntax_Syntax.ctx_uvar_head = uu___;
      FStarC_Syntax_Syntax.ctx_uvar_gamma = gamma;
      FStarC_Syntax_Syntax.ctx_uvar_binders = binders;
      FStarC_Syntax_Syntax.ctx_uvar_reason = reason;
      FStarC_Syntax_Syntax.ctx_uvar_range = r;
      FStarC_Syntax_Syntax.ctx_uvar_meta = meta
    } in
  FStarC_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma
    binders;
  (let t =
     FStarC_Syntax_Syntax.mk
       (FStarC_Syntax_Syntax.Tm_uvar
          (ctx_uvar, ([], FStarC_Syntax_Syntax.NoUseRange))) r in
   let imp =
     {
       FStarC_TypeChecker_Common.imp_reason = reason;
       FStarC_TypeChecker_Common.imp_uvar = ctx_uvar;
       FStarC_TypeChecker_Common.imp_tm = t;
       FStarC_TypeChecker_Common.imp_range = r
     } in
   (let uu___2 = FStarC_Effect.op_Bang dbg_ImplicitTrace in
    if uu___2
    then
      let uu___3 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_uvar
          ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_head in
      FStarC_Format.print1 "Just created uvar for implicit {%s}\n" uu___3
    else ());
   (let g =
      let uu___2 =
        Obj.magic
          (FStarC_Class_Listlike.cons ()
             (Obj.magic (FStarC_CList.listlike_clist ())) imp
             (FStarC_Class_Listlike.empty ()
                (Obj.magic (FStarC_CList.listlike_clist ())))) in
      {
        FStarC_TypeChecker_Common.guard_f =
          (trivial_guard.FStarC_TypeChecker_Common.guard_f);
        FStarC_TypeChecker_Common.deferred_to_tac =
          (trivial_guard.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (trivial_guard.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (trivial_guard.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits = uu___2
      } in
    (t, (ctx_uvar, r), g)))
let new_implicit_var_aux (reason : Prims.string) (r : FStarC_Range_Type.t)
  (env1 : env) (k : FStarC_Syntax_Syntax.typ)
  (should_check : FStarC_Syntax_Syntax.should_check_uvar)
  (meta :
    FStarC_Syntax_Syntax.ctx_uvar_meta_t FStar_Pervasives_Native.option)
  (unrefine : Prims.bool) :
  (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.ctx_uvar *
    FStarC_Range_Type.t) * guard_t)=
  new_tac_implicit_var reason r env1 k should_check [] meta unrefine
let uvar_meta_for_binder (b : FStarC_Syntax_Syntax.binder) :
  (FStarC_Syntax_Syntax.ctx_uvar_meta_t FStar_Pervasives_Native.option *
    Prims.bool)=
  let should_unrefine =
    FStarC_Syntax_Util.has_attribute b.FStarC_Syntax_Syntax.binder_attrs
      FStarC_Parser_Const.unrefine_binder_attr in
  let meta =
    match b.FStarC_Syntax_Syntax.binder_qual with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta tau) ->
        FStar_Pervasives_Native.Some
          (FStarC_Syntax_Syntax.Ctx_uvar_meta_tac tau)
    | uu___ ->
        let is_unification_tag t =
          let uu___1 = FStarC_Syntax_Util.head_and_args t in
          match uu___1 with
          | (hd, args) ->
              let hd1 = FStarC_Syntax_Util.un_uinst hd in
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Subst.compress hd1 in
                  uu___4.FStarC_Syntax_Syntax.n in
                (uu___3, args) in
              (match uu___2 with
               | (FStarC_Syntax_Syntax.Tm_fvar fv,
                  (uu___3, FStar_Pervasives_Native.Some
                   { FStarC_Syntax_Syntax.aqual_implicit = true;
                     FStarC_Syntax_Syntax.aqual_attributes = uu___4;_})::
                  (a, FStar_Pervasives_Native.None)::[]) when
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.unification_tag_lid
                   -> FStar_Pervasives_Native.Some a
               | uu___3 -> FStar_Pervasives_Native.None) in
        let uu___1 =
          FStarC_List.tryPick is_unification_tag
            b.FStarC_Syntax_Syntax.binder_attrs in
        (match uu___1 with
         | FStar_Pervasives_Native.Some tag ->
             FStar_Pervasives_Native.Some
               (FStarC_Syntax_Syntax.Ctx_uvar_meta_attr tag)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None) in
  (meta, should_unrefine)
let uvars_for_binders (env1 : env) (bs : FStarC_Syntax_Syntax.binders)
  (substs : FStarC_Syntax_Syntax.subst_t)
  (reason : FStarC_Syntax_Syntax.binder -> Prims.string)
  (r : FStarC_Range_Type.t) :
  (FStarC_Syntax_Syntax.term Prims.list * guard_t)=
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 b ->
         match uu___1 with
         | (substs1, uvars, g) ->
             let sort =
               FStarC_Syntax_Subst.subst substs1
                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
             let uu___2 = uvar_meta_for_binder b in
             (match uu___2 with
              | (ctx_uvar_meta, should_unrefine) ->
                  let uu___3 =
                    let uu___4 = reason b in
                    let uu___5 =
                      let uu___6 =
                        FStarC_Options.compat_pre_typed_indexed_effects () in
                      if uu___6
                      then
                        FStarC_Syntax_Syntax.Allow_untyped
                          "indexed effect uvar in compat mode"
                      else FStarC_Syntax_Syntax.Strict in
                    new_implicit_var_aux uu___4 r env1 sort uu___5
                      ctx_uvar_meta should_unrefine in
                  (match uu___3 with
                   | (t, l_ctx_uvars, g_t) ->
                       ((let uu___5 =
                           FStarC_Effect.op_Bang dbg_LayeredEffectsEqns in
                         if uu___5
                         then
                           let uu___6 =
                             FStarC_Class_Show.show
                               (FStarC_Class_Show.show_tuple2
                                  FStarC_Syntax_Print.showable_ctxu
                                  FStarC_Range_Ops.showable_range)
                               l_ctx_uvars in
                           FStarC_Format.print1 "Layered Effect uvar: %s\n"
                             uu___6
                         else ());
                        (let uu___5 = conj_guards [g; g_t] in
                         ((FStarC_List.op_At substs1
                             [FStarC_Syntax_Syntax.NT
                                ((b.FStarC_Syntax_Syntax.binder_bv), t)]),
                           (FStarC_List.op_At uvars [t]), uu___5))))))
      (substs, [], trivial_guard) bs in
  match uu___ with | (uu___1, uvars, g) -> (uvars, g)
let pure_precondition_for_trivial_post (env1 : env)
  (u : FStarC_Syntax_Syntax.universe) (t : FStarC_Syntax_Syntax.typ)
  (wp : FStarC_Syntax_Syntax.typ) (r : FStarC_Range_Type.t) :
  FStarC_Syntax_Syntax.typ=
  let trivial_post =
    let post_ts =
      let uu___ =
        lookup_definition [NoDelta] env1
          FStarC_Parser_Const.trivial_pure_post_lid in
      FStarC_Option.must uu___ in
    let uu___ = inst_tscheme_with post_ts [u] in
    match uu___ with
    | (uu___1, post) ->
        let uu___2 = let uu___3 = FStarC_Syntax_Syntax.as_arg t in [uu___3] in
        FStarC_Syntax_Syntax.mk_Tm_app post uu___2 r in
  let uu___ =
    let uu___1 = FStarC_Syntax_Syntax.as_arg trivial_post in [uu___1] in
  FStarC_Syntax_Syntax.mk_Tm_app wp uu___ r
let get_letrec_arity (env1 : env) (lbname : FStarC_Syntax_Syntax.lbname) :
  Prims.int FStar_Pervasives_Native.option=
  let compare_either f1 f2 e1 e2 =
    match (e1, e2) with
    | (FStar_Pervasives.Inl v1, FStar_Pervasives.Inl v2) -> f1 v1 v2
    | (FStar_Pervasives.Inr v1, FStar_Pervasives.Inr v2) -> f2 v1 v2
    | uu___ -> false in
  let uu___ =
    FStarC_Option.find
      (fun uu___1 ->
         match uu___1 with
         | (lbname', uu___2, uu___3, uu___4) ->
             compare_either FStarC_Syntax_Syntax.bv_eq
               FStarC_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, arity, uu___2, uu___3) ->
      FStar_Pervasives_Native.Some arity
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let fvar_of_nonqual_lid (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term=
  let qn = lookup_qname env1 lid in
  FStarC_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None
let split_smt_query (e : env) (q : FStarC_Syntax_Syntax.term) :
  (env * FStarC_Syntax_Syntax.term) Prims.list FStar_Pervasives_Native.option=
  match (e.solver).spinoff_strictly_positive_goals with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some p ->
      let uu___ = p e q in FStar_Pervasives_Native.Some uu___
let hashable_env : env FStarC_Class_Hashable.hashable=
  {
    FStarC_Class_Hashable.hash =
      (fun e ->
         let uu___ =
           let uu___1 =
             let uu___2 =
               FStarC_Class_Hashable.hash
                 (FStarC_Class_Hashable.hashable_list
                    FStarC_Syntax_Hash.hashable_binding) e.gamma in
             let uu___3 =
               FStarC_Class_Hashable.hash
                 (FStarC_Class_Hashable.hashable_list
                    (FStarC_Class_Hashable.hashable_tuple2
                       (FStarC_Class_Hashable.hashable_list
                          FStarC_Syntax_Hash.hashable_lident)
                       FStarC_Syntax_Hash.hashable_sigelt)) e.gamma_sig in
             FStarC_Hash.mix uu___2 uu___3 in
           let uu___2 =
             FStarC_Class_Hashable.hash
               (FStarC_Class_Hashable.hashable_list
                  (FStarC_Class_Hashable.hashable_tuple2
                     (FStarC_Class_Hashable.hashable_list
                        FStarC_Class_Hashable.hashable_string)
                     FStarC_Class_Hashable.hashable_bool)) e.proof_ns in
           FStarC_Hash.mix uu___1 uu___2 in
         let uu___1 =
           FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_bool
             e.admit in
         FStarC_Hash.mix uu___ uu___1)
  }
