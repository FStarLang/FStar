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
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldQual of Prims.string Prims.list 
  | UnfoldNamespace of Prims.string Prims.list 
  | UnfoldTac 
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
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee -> match projectee with | Beta -> true | uu___ -> false
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu___ -> false
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu___ -> false
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee -> match projectee with | ZetaFull -> true | uu___ -> false
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee -> match projectee with | Exclude _0 -> true | uu___ -> false
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee -> match projectee with | Exclude _0 -> _0
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu___ -> false
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu___ -> false
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee -> match projectee with | Primops -> true | uu___ -> false
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding -> true | uu___ -> false
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee -> match projectee with | Inlining -> true | uu___ -> false
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee ->
    match projectee with | DoNotUnfoldPureLets -> true | uu___ -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu___ -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu___ -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu___ -> false
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu___ -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldQual : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldQual _0 -> true | uu___ -> false
let (__proj__UnfoldQual__item___0 : step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldQual _0 -> _0
let (uu___is_UnfoldNamespace : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldNamespace _0 -> true | uu___ -> false
let (__proj__UnfoldNamespace__item___0 : step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldNamespace _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee -> match projectee with | UnfoldTac -> true | uu___ -> false
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PureSubtermsWithinComputations -> true
    | uu___ -> false
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee -> match projectee with | Simplify -> true | uu___ -> false
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | EraseUniverses -> true | uu___ -> false
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowUnboundUniverses -> true | uu___ -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu___ -> false
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CompressUvars -> true | uu___ -> false
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee -> match projectee with | NoFullNorm -> true | uu___ -> false
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckNoUvars -> true | uu___ -> false
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu___ -> false
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee -> match projectee with | Unascribe -> true | uu___ -> false
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu___ -> false
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ForExtraction -> true | uu___ -> false
let (uu___is_Unrefine : step -> Prims.bool) =
  fun projectee -> match projectee with | Unrefine -> true | uu___ -> false
let (uu___is_NormDebug : step -> Prims.bool) =
  fun projectee -> match projectee with | NormDebug -> true | uu___ -> false
let (uu___is_DefaultUnivsToZero : step -> Prims.bool) =
  fun projectee ->
    match projectee with | DefaultUnivsToZero -> true | uu___ -> false
type steps = step Prims.list
let (dbg_ImplicitTrace : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "ImplicitTrace"
let (dbg_LayeredEffectsEqns : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "LayeredEffectsEqns"
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      match (s1, s2) with
      | (Beta, Beta) -> true
      | (Iota, Iota) -> true
      | (Zeta, Zeta) -> true
      | (ZetaFull, ZetaFull) -> true
      | (Weak, Weak) -> true
      | (HNF, HNF) -> true
      | (Primops, Primops) -> true
      | (Eager_unfolding, Eager_unfolding) -> true
      | (Inlining, Inlining) -> true
      | (DoNotUnfoldPureLets, DoNotUnfoldPureLets) -> true
      | (UnfoldTac, UnfoldTac) -> true
      | (PureSubtermsWithinComputations, PureSubtermsWithinComputations) ->
          true
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
      | (Unrefine, Unrefine) -> true
      | (Exclude s11, Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11, UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1, UnfoldOnly lids2) ->
          FStar_Class_Deq.op_Equals_Question
            (FStar_Class_Ord.ord_eq
               (FStar_Class_Ord.ord_list FStar_Syntax_Syntax.ord_fv)) lids1
            lids2
      | (UnfoldFully lids1, UnfoldFully lids2) ->
          FStar_Class_Deq.op_Equals_Question
            (FStar_Class_Ord.ord_eq
               (FStar_Class_Ord.ord_list FStar_Syntax_Syntax.ord_fv)) lids1
            lids2
      | (UnfoldAttr lids1, UnfoldAttr lids2) ->
          FStar_Class_Deq.op_Equals_Question
            (FStar_Class_Ord.ord_eq
               (FStar_Class_Ord.ord_list FStar_Syntax_Syntax.ord_fv)) lids1
            lids2
      | (UnfoldQual strs1, UnfoldQual strs2) ->
          FStar_Class_Deq.op_Equals_Question
            (FStar_Class_Ord.ord_eq
               (FStar_Class_Ord.ord_list FStar_Class_Ord.ord_string)) strs1
            strs2
      | (UnfoldNamespace strs1, UnfoldNamespace strs2) ->
          FStar_Class_Deq.op_Equals_Question
            (FStar_Class_Ord.ord_eq
               (FStar_Class_Ord.ord_list FStar_Class_Ord.ord_string)) strs1
            strs2
      | uu___ -> false
let (deq_step : step FStar_Class_Deq.deq) =
  { FStar_Class_Deq.op_Equals_Question = eq_step }
let rec (step_to_string : step -> Prims.string) =
  fun s ->
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
          FStar_Class_Show.show FStar_Syntax_Syntax.showable_delta_depth s1 in
        Prims.strcat "UnfoldUntil " uu___
    | UnfoldOnly lids1 ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_list FStar_Ident.showable_lident) lids1 in
        Prims.strcat "UnfoldOnly " uu___
    | UnfoldFully lids1 ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_list FStar_Ident.showable_lident) lids1 in
        Prims.strcat "UnfoldFully " uu___
    | UnfoldAttr lids1 ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_list FStar_Ident.showable_lident) lids1 in
        Prims.strcat "UnfoldAttr " uu___
    | UnfoldQual strs1 ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_list
               (FStar_Class_Show.printableshow
                  FStar_Class_Printable.printable_string)) strs1 in
        Prims.strcat "UnfoldQual " uu___
    | UnfoldNamespace strs1 ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_list
               (FStar_Class_Show.printableshow
                  FStar_Class_Printable.printable_string)) strs1 in
        Prims.strcat "UnfoldNamespace " uu___
    | UnfoldTac -> "UnfoldTac"
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
let (showable_step : step FStar_Class_Show.showable) =
  { FStar_Class_Show.show = step_to_string }
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee -> match projectee with | NoDelta -> true | uu___ -> false
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | InliningDelta -> true | uu___ -> false
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding_only -> true | uu___ -> false
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee -> match projectee with | Unfold _0 -> true | uu___ -> false
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee -> match projectee with | Unfold _0 -> _0
let (deq_delta_level : delta_level FStar_Class_Deq.deq) =
  {
    FStar_Class_Deq.op_Equals_Question =
      (fun x ->
         fun y ->
           match (x, y) with
           | (NoDelta, NoDelta) -> true
           | (InliningDelta, InliningDelta) -> true
           | (Eager_unfolding_only, Eager_unfolding_only) -> true
           | (Unfold x1, Unfold y1) ->
               FStar_Class_Deq.op_Equals_Question
                 FStar_Syntax_Syntax.deq_delta_depth x1 y1
           | uu___ -> false)
  }
let (showable_delta_level : delta_level FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | NoDelta -> "NoDelta"
         | InliningDelta -> "Inlining"
         | Eager_unfolding_only -> "Eager_unfolding_only"
         | Unfold d ->
             let uu___1 =
               FStar_Class_Show.show FStar_Syntax_Syntax.showable_delta_depth
                 d in
             Prims.strcat "Unfold " uu___1)
  }
type name_prefix = FStar_Ident.path
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Pervasives.either * FStar_Compiler_Range_Type.range)
type goal = FStar_Syntax_Syntax.term
type must_tot = Prims.bool
type mlift =
  {
  mlift_wp:
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
and edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift ;
  mpath: FStar_Ident.lident Prims.list }
and effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
    ;
  polymonadic_binds:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env ->
         FStar_Syntax_Syntax.comp_typ ->
           FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStar_Syntax_Syntax.comp_typ ->
               FStar_Syntax_Syntax.cflag Prims.list ->
                 FStar_Compiler_Range_Type.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list
    ;
  polymonadic_subcomps:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Syntax_Syntax.tscheme *
      FStar_Syntax_Syntax.indexed_effect_combinator_kind) Prims.list
    }
and env =
  {
  solver: solver_t ;
  range: FStar_Compiler_Range_Type.range ;
  curmodule: FStar_Ident.lident ;
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
  gamma_cache: cached_elt FStar_Compiler_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ:
    (FStar_Syntax_Syntax.typ * Prims.bool) FStar_Pervasives_Native.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Compiler_Util.smap ;
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Compiler_Util.smap ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStar_Syntax_Syntax.lbname * Prims.int * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq_strict: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  flychecking: Prims.bool ;
  uvar_subtyping: Prims.bool ;
  intactics: Prims.bool ;
  nocoerce: Prims.bool ;
  tc_term:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t)
    ;
  typeof_tot_or_gtot_term:
    env ->
      FStar_Syntax_Syntax.term ->
        must_tot ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
            FStar_TypeChecker_Common.guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  typeof_well_typed_tot_or_gtot_term:
    env ->
      FStar_Syntax_Syntax.term ->
        must_tot ->
          (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Common.guard_t)
    ;
  teq_nosmt_force:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool ;
  subtype_nosmt_force:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool ;
  qtbl_name_and_index:
    ((FStar_Ident.lident * FStar_Syntax_Syntax.typ * Prims.int)
      FStar_Pervasives_Native.option * Prims.int FStar_Compiler_Util.smap)
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Compiler_Util.smap ;
  fv_delta_depths: FStar_Syntax_Syntax.delta_depth FStar_Compiler_Util.smap ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  try_solve_implicits_hook:
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit
    ;
  splice:
    env ->
      Prims.bool ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Compiler_Range_Type.range ->
              FStar_Syntax_Syntax.sigelt Prims.list
    ;
  mpreprocess:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  postprocess:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  identifier_info:
    FStar_TypeChecker_Common.id_info_table FStar_Compiler_Effect.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  strict_args_tab:
    Prims.int Prims.list FStar_Pervasives_Native.option
      FStar_Compiler_Util.smap
    ;
  erasable_types_tab: Prims.bool FStar_Compiler_Util.smap ;
  enable_defer_to_tac: Prims.bool ;
  unif_allow_ref_guards: Prims.bool ;
  erase_erasable_args: Prims.bool ;
  core_check:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          Prims.bool ->
            (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,
              Prims.bool -> Prims.string) FStar_Pervasives.either
    ;
  missing_decl: FStar_Ident.lident FStar_Compiler_RBSet.t }
and solver_t =
  {
  init: env -> unit ;
  push: Prims.string -> unit ;
  pop: Prims.string -> unit ;
  snapshot: Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit) ;
  rollback:
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit
    ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (Prims.bool * (env * goal * FStar_Options.optionstate) Prims.list)
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
  refresh: unit -> unit }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding, sig_binding) FStar_Pervasives.either ->
        unit
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun projectee ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_wp
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_term
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { msource; mtarget; mlift = mlift1; mpath;_} -> msource
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { msource; mtarget; mlift = mlift1; mpath;_} -> mtarget
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee ->
    match projectee with
    | { msource; mtarget; mlift = mlift1; mpath;_} -> mlift1
let (__proj__Mkedge__item__mpath : edge -> FStar_Ident.lident Prims.list) =
  fun projectee ->
    match projectee with
    | { msource; mtarget; mlift = mlift1; mpath;_} -> mpath
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        decls
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        order
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        joins
let (__proj__Mkeffects__item__polymonadic_binds :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env ->
         FStar_Syntax_Syntax.comp_typ ->
           FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStar_Syntax_Syntax.comp_typ ->
               FStar_Syntax_Syntax.cflag Prims.list ->
                 FStar_Compiler_Range_Type.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        polymonadic_binds
let (__proj__Mkeffects__item__polymonadic_subcomps :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Syntax_Syntax.tscheme *
      FStar_Syntax_Syntax.indexed_effect_combinator_kind) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        polymonadic_subcomps
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> solver
let (__proj__Mkenv__item__range : env -> FStar_Compiler_Range_Type.range) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> range
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> curmodule
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> gamma
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> gamma_sig
let (__proj__Mkenv__item__gamma_cache :
  env -> cached_elt FStar_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> gamma_cache
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> modules
let (__proj__Mkenv__item__expected_typ :
  env ->
    (FStar_Syntax_Syntax.typ * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> expected_typ
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> sigtab
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> attrtab
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> instantiate_imp
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> effects1
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> generalize
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * Prims.int * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> letrecs
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> top_level
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> check_uvars
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> use_eq_strict
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> is_iface
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> admit
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> lax
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> lax_universes
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> phase1
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> failhard
let (__proj__Mkenv__item__flychecking : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> flychecking
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> uvar_subtyping
let (__proj__Mkenv__item__intactics : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> intactics
let (__proj__Mkenv__item__nocoerce : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> nocoerce
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> tc_term
let (__proj__Mkenv__item__typeof_tot_or_gtot_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        must_tot ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
            FStar_TypeChecker_Common.guard_t))
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> typeof_tot_or_gtot_term
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> universe_of
let (__proj__Mkenv__item__typeof_well_typed_tot_or_gtot_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        must_tot ->
          (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Common.guard_t))
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> typeof_well_typed_tot_or_gtot_term
let (__proj__Mkenv__item__teq_nosmt_force :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> teq_nosmt_force
let (__proj__Mkenv__item__subtype_nosmt_force :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> subtype_nosmt_force
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    ((FStar_Ident.lident * FStar_Syntax_Syntax.typ * Prims.int)
      FStar_Pervasives_Native.option * Prims.int FStar_Compiler_Util.smap))
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> qtbl_name_and_index
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> normalized_eff_names
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> fv_delta_depths
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> proof_ns
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> synth_hook
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> try_solve_implicits_hook
let (__proj__Mkenv__item__splice :
  env ->
    env ->
      Prims.bool ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Compiler_Range_Type.range ->
              FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> splice
let (__proj__Mkenv__item__mpreprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> mpreprocess
let (__proj__Mkenv__item__postprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> postprocess
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> identifier_info
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> tc_hooks
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> dsenv
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> nbe
let (__proj__Mkenv__item__strict_args_tab :
  env ->
    Prims.int Prims.list FStar_Pervasives_Native.option
      FStar_Compiler_Util.smap)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> strict_args_tab
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> erasable_types_tab
let (__proj__Mkenv__item__enable_defer_to_tac : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> enable_defer_to_tac
let (__proj__Mkenv__item__unif_allow_ref_guards : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> unif_allow_ref_guards
let (__proj__Mkenv__item__erase_erasable_args : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> erase_erasable_args
let (__proj__Mkenv__item__core_check :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          Prims.bool ->
            (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,
              Prims.bool -> Prims.string) FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> core_check
let (__proj__Mkenv__item__missing_decl :
  env -> FStar_Ident.lident FStar_Compiler_RBSet.t) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq_strict; is_iface;
        admit; lax; lax_universes; phase1; failhard; flychecking;
        uvar_subtyping; intactics; nocoerce; tc_term;
        typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; teq_nosmt_force;
        subtype_nosmt_force; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab; enable_defer_to_tac;
        unif_allow_ref_guards; erase_erasable_args; core_check;
        missing_decl;_} -> missing_decl
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> init
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> push
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> pop
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> snapshot
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> rollback
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> encode_sig
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env ->
      goal ->
        (Prims.bool * (env * goal * FStar_Options.optionstate) Prims.list))
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> preprocess
let (__proj__Mksolver_t__item__spinoff_strictly_positive_goals :
  solver_t ->
    (env -> goal -> (env * goal) Prims.list) FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> spinoff_strictly_positive_goals
let (__proj__Mksolver_t__item__handle_smt_goal :
  solver_t -> env -> goal -> (env * goal) Prims.list) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> handle_smt_goal
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> goal -> unit)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> solve
let (__proj__Mksolver_t__item__solve_sync :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> goal -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> solve_sync
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> finish
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess;
        spinoff_strictly_positive_goals; handle_smt_goal; solve; solve_sync;
        finish; refresh;_} -> refresh
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding, sig_binding) FStar_Pervasives.either ->
        unit)
  =
  fun projectee ->
    match projectee with
    | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
type lift_comp_t =
  env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
type polymonadic_bind_t =
  env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.comp_typ ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            FStar_Compiler_Range_Type.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type core_check_t =
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,
            Prims.bool -> Prims.string) FStar_Pervasives.either
let (preprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun tau -> fun tm -> env1.mpreprocess env1 tau tm
let (postprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 -> fun tau -> fun ty -> fun tm -> env1.postprocess env1 tau ty tm
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst ->
    fun gamma ->
      FStar_Compiler_List.map
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.Binding_var x ->
               let y =
                 let uu___1 = FStar_Syntax_Syntax.bv_to_name x in
                 FStar_Syntax_Subst.subst subst uu___1 in
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress y in
                 uu___2.FStar_Syntax_Syntax.n in
               (match uu___1 with
                | FStar_Syntax_Syntax.Tm_name y1 ->
                    let uu___2 =
                      let uu___3 =
                        FStar_Syntax_Subst.subst subst
                          x.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (y1.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (y1.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu___3
                      } in
                    FStar_Syntax_Syntax.Binding_var uu___2
                | uu___2 -> FStar_Compiler_Effect.failwith "Not a renaming")
           | b -> b) gamma
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst ->
    fun env1 ->
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
        lax = (env1.lax);
        lax_universes = (env1.lax_universes);
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
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu___ -> fun uu___1 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env1 -> env1.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
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
        lax = (env1.lax);
        lax_universes = (env1.lax_universes);
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
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___ = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
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
        lax = (e.lax);
        lax_universes = (e.lax_universes);
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
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e -> FStar_Syntax_DsEnv.dep_graph e.dsenv
let (record_val_for : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___ =
        Obj.magic
          (FStar_Class_Setlike.add ()
             (Obj.magic
                (FStar_Compiler_RBSet.setlike_rbset
                   FStar_Syntax_Syntax.ord_fv)) l (Obj.magic e.missing_decl)) in
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
        lax = (e.lax);
        lax_universes = (e.lax_universes);
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
let (record_definition_for : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___ =
        Obj.magic
          (FStar_Class_Setlike.remove ()
             (Obj.magic
                (FStar_Compiler_RBSet.setlike_rbset
                   FStar_Syntax_Syntax.ord_fv)) l (Obj.magic e.missing_decl)) in
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
        lax = (e.lax);
        lax_universes = (e.lax_universes);
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
let (missing_definition_list : env -> FStar_Ident.lident Prims.list) =
  fun e ->
    FStar_Class_Setlike.elems ()
      (Obj.magic
         (FStar_Compiler_RBSet.setlike_rbset FStar_Syntax_Syntax.ord_fv))
      (Obj.magic e.missing_decl)
type implicit = FStar_TypeChecker_Common.implicit
type implicits = FStar_TypeChecker_Common.implicits
type guard_t = FStar_TypeChecker_Common.guard_t
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Pervasives.either * FStar_Compiler_Range_Type.range)
    FStar_Pervasives_Native.option
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Compiler_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1 ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu___ = FStar_Ident.string_of_lid env1.curmodule in
       FStar_Options.should_verify uu___)
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d ->
    fun q ->
      match (d, q) with
      | (NoDelta, uu___) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu___, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)
          -> true
      | (Unfold uu___, FStar_Syntax_Syntax.Visible_default) -> true
      | (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu___ -> false
let (default_table_size : Prims.int) = (Prims.of_int (200))
let new_sigtab : 'uuuuu . unit -> 'uuuuu FStar_Compiler_Util.smap =
  fun uu___ -> FStar_Compiler_Util.smap_create default_table_size
let new_gamma_cache : 'uuuuu . unit -> 'uuuuu FStar_Compiler_Util.smap =
  fun uu___ -> FStar_Compiler_Util.smap_create (Prims.of_int (100))
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
           guard_t))
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           must_tot ->
             (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
        ->
        (env ->
           FStar_Syntax_Syntax.term ->
             must_tot ->
               FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
          ->
          (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
            ->
            (env ->
               FStar_Syntax_Syntax.term ->
                 FStar_Syntax_Syntax.term -> Prims.bool)
              ->
              (env ->
                 FStar_Syntax_Syntax.term ->
                   FStar_Syntax_Syntax.term -> Prims.bool)
                ->
                solver_t ->
                  FStar_Ident.lident ->
                    (step Prims.list ->
                       env ->
                         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
                      -> core_check_t -> env)
  =
  fun deps ->
    fun tc_term ->
      fun typeof_tot_or_gtot_term ->
        fun typeof_tot_or_gtot_term_fastpath ->
          fun universe_of ->
            fun teq_nosmt_force ->
              fun subtype_nosmt_force ->
                fun solver ->
                  fun module_lid ->
                    fun nbe ->
                      fun core_check ->
                        let uu___ = new_gamma_cache () in
                        let uu___1 = new_sigtab () in
                        let uu___2 = new_sigtab () in
                        let uu___3 =
                          let uu___4 =
                            FStar_Compiler_Util.smap_create
                              (Prims.of_int (10)) in
                          (FStar_Pervasives_Native.None, uu___4) in
                        let uu___4 =
                          FStar_Compiler_Util.smap_create (Prims.of_int (20)) in
                        let uu___5 =
                          FStar_Compiler_Util.smap_create (Prims.of_int (50)) in
                        let uu___6 = FStar_Options.using_facts_from () in
                        let uu___7 =
                          FStar_Compiler_Util.mk_ref
                            FStar_TypeChecker_Common.id_info_table_empty in
                        let uu___8 = FStar_Syntax_DsEnv.empty_env deps in
                        let uu___9 =
                          FStar_Compiler_Util.smap_create (Prims.of_int (20)) in
                        let uu___10 =
                          FStar_Compiler_Util.smap_create (Prims.of_int (20)) in
                        let uu___11 =
                          Obj.magic
                            (FStar_Class_Setlike.empty ()
                               (Obj.magic
                                  (FStar_Compiler_RBSet.setlike_rbset
                                     FStar_Syntax_Syntax.ord_fv)) ()) in
                        {
                          solver;
                          range = FStar_Compiler_Range_Type.dummyRange;
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
                          lax = false;
                          lax_universes = false;
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
                            (fun env1 ->
                               fun t ->
                                 fun must_tot1 ->
                                   let uu___12 =
                                     typeof_tot_or_gtot_term_fastpath env1 t
                                       must_tot1 in
                                   match uu___12 with
                                   | FStar_Pervasives_Native.Some k ->
                                       (k,
                                         FStar_TypeChecker_Common.trivial_guard)
                                   | FStar_Pervasives_Native.None ->
                                       let uu___13 =
                                         typeof_tot_or_gtot_term env1 t
                                           must_tot1 in
                                       (match uu___13 with
                                        | (t', k, g) -> (k, g)));
                          teq_nosmt_force;
                          subtype_nosmt_force;
                          qtbl_name_and_index = uu___3;
                          normalized_eff_names = uu___4;
                          fv_delta_depths = uu___5;
                          proof_ns = uu___6;
                          synth_hook =
                            (fun e ->
                               fun g ->
                                 fun tau ->
                                   FStar_Compiler_Effect.failwith
                                     "no synthesizer available");
                          try_solve_implicits_hook =
                            (fun e ->
                               fun tau ->
                                 fun imps ->
                                   FStar_Compiler_Effect.failwith
                                     "no implicit hook available");
                          splice =
                            (fun e ->
                               fun is_typed ->
                                 fun lids ->
                                   fun tau ->
                                     fun range ->
                                       FStar_Compiler_Effect.failwith
                                         "no splicer available");
                          mpreprocess =
                            (fun e ->
                               fun tau ->
                                 fun tm ->
                                   FStar_Compiler_Effect.failwith
                                     "no preprocessor available");
                          postprocess =
                            (fun e ->
                               fun tau ->
                                 fun typ ->
                                   fun tm ->
                                     FStar_Compiler_Effect.failwith
                                       "no postprocessor available");
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
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env1 -> env1.dsenv
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Compiler_Util.smap) =
  fun env1 -> env1.sigtab
let (attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Compiler_Util.smap) =
  fun env1 -> env1.attrtab
let (gamma_cache : env -> cached_elt FStar_Compiler_Util.smap) =
  fun env1 -> env1.gamma_cache
let (query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref [[]]
let (push_query_indices : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang query_indices in
    match uu___1 with
    | [] -> FStar_Compiler_Effect.failwith "Empty query indices!"
    | uu___2 ->
        let uu___3 =
          let uu___4 =
            let uu___5 = FStar_Compiler_Effect.op_Bang query_indices in
            FStar_Compiler_List.hd uu___5 in
          let uu___5 = FStar_Compiler_Effect.op_Bang query_indices in uu___4
            :: uu___5 in
        FStar_Compiler_Effect.op_Colon_Equals query_indices uu___3
let (pop_query_indices : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang query_indices in
    match uu___1 with
    | [] -> FStar_Compiler_Effect.failwith "Empty query indices!"
    | hd::tl -> FStar_Compiler_Effect.op_Colon_Equals query_indices tl
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu___ -> FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu___ ->
    match uu___ with
    | (l, n) ->
        let uu___1 = FStar_Compiler_Effect.op_Bang query_indices in
        (match uu___1 with
         | hd::tl ->
             FStar_Compiler_Effect.op_Colon_Equals query_indices (((l, n) ::
               hd) :: tl)
         | uu___2 -> FStar_Compiler_Effect.failwith "Empty query indices")
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang query_indices in
    FStar_Compiler_List.hd uu___1
let (stack : env Prims.list FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref []
let (push_stack : env -> env) =
  fun env1 ->
    (let uu___1 =
       let uu___2 = FStar_Compiler_Effect.op_Bang stack in env1 :: uu___2 in
     FStar_Compiler_Effect.op_Colon_Equals stack uu___1);
    (let uu___1 = FStar_Compiler_Util.smap_copy (gamma_cache env1) in
     let uu___2 = FStar_Compiler_Util.smap_copy (sigtab env1) in
     let uu___3 = FStar_Compiler_Util.smap_copy (attrtab env1) in
     let uu___4 =
       let uu___5 =
         FStar_Compiler_Util.smap_copy
           (FStar_Pervasives_Native.snd env1.qtbl_name_and_index) in
       ((FStar_Pervasives_Native.fst env1.qtbl_name_and_index), uu___5) in
     let uu___5 = FStar_Compiler_Util.smap_copy env1.normalized_eff_names in
     let uu___6 = FStar_Compiler_Util.smap_copy env1.fv_delta_depths in
     let uu___7 =
       let uu___8 = FStar_Compiler_Effect.op_Bang env1.identifier_info in
       FStar_Compiler_Util.mk_ref uu___8 in
     let uu___8 = FStar_Compiler_Util.smap_copy env1.strict_args_tab in
     let uu___9 = FStar_Compiler_Util.smap_copy env1.erasable_types_tab in
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
       lax = (env1.lax);
       lax_universes = (env1.lax_universes);
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
let (pop_stack : unit -> env) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang stack in
    match uu___1 with
    | env1::tl -> (FStar_Compiler_Effect.op_Colon_Equals stack tl; env1)
    | uu___2 -> FStar_Compiler_Effect.failwith "Impossible: Too many pops"
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push_stack stack env1
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop_stack stack depth
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1 ->
    fun msg ->
      FStar_Compiler_Util.atomically
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
                         let uu___4 = FStar_Syntax_DsEnv.snapshot env2.dsenv in
                         (match uu___4 with
                          | (dsenv_depth, dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
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
                                  lax = (env2.lax);
                                  lax_universes = (env2.lax_universes);
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
                                  erasable_types_tab =
                                    (env2.erasable_types_tab);
                                  enable_defer_to_tac =
                                    (env2.enable_defer_to_tac);
                                  unif_allow_ref_guards =
                                    (env2.unif_allow_ref_guards);
                                  erase_erasable_args =
                                    (env2.erase_erasable_args);
                                  core_check = (env2.core_check);
                                  missing_decl = (env2.missing_decl)
                                })))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Compiler_Util.atomically
          (fun uu___ ->
             let uu___1 =
               match depth with
               | FStar_Pervasives_Native.Some (s1, s2, s3, s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None) in
             match uu___1 with
             | (stack_depth, query_indices_depth, solver_depth, dsenv_depth)
                 ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth in
                             ((let uu___5 =
                                 FStar_Compiler_Util.physical_equality
                                   tcenv.dsenv dsenv1 in
                               FStar_Common.runtime_assert uu___5
                                 "Inconsistent stack state");
                              tcenv))))))
let (push : env -> Prims.string -> env) =
  fun env1 ->
    fun msg ->
      let uu___ = snapshot env1 msg in FStar_Pervasives_Native.snd uu___
let (pop : env -> Prims.string -> env) =
  fun env1 ->
    fun msg -> rollback env1.solver msg FStar_Pervasives_Native.None
let (incr_query_index : env -> env) =
  fun env1 ->
    let qix = peek_query_indices () in
    match env1.qtbl_name_and_index with
    | (FStar_Pervasives_Native.None, uu___) -> env1
    | (FStar_Pervasives_Native.Some (l, typ, n), tbl) ->
        let uu___ =
          FStar_Compiler_List.tryFind
            (fun uu___1 ->
               match uu___1 with | (m, uu___2) -> FStar_Ident.lid_equals l m)
            qix in
        (match uu___ with
         | FStar_Pervasives_Native.None ->
             let next = n + Prims.int_one in
             (add_query_index (l, next);
              (let uu___3 = FStar_Ident.string_of_lid l in
               FStar_Compiler_Util.smap_add tbl uu___3 next);
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
                lax = (env1.lax);
                lax_universes = (env1.lax_universes);
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
              (let uu___4 = FStar_Ident.string_of_lid l in
               FStar_Compiler_Util.smap_add tbl uu___4 next);
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
                lax = (env1.lax);
                lax_universes = (env1.lax_universes);
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
let (set_range : env -> FStar_Compiler_Range_Type.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Compiler_Range_Type.dummyRange
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
          lax = (e.lax);
          lax_universes = (e.lax_universes);
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
let (get_range : env -> FStar_Compiler_Range_Type.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1 ->
    fun enabled ->
      let uu___ =
        let uu___1 = FStar_Compiler_Effect.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu___1 enabled in
      FStar_Compiler_Effect.op_Colon_Equals env1.identifier_info uu___
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun bv ->
      fun ty ->
        let uu___ =
          let uu___1 = FStar_Compiler_Effect.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu___1 bv ty in
        FStar_Compiler_Effect.op_Colon_Equals env1.identifier_info uu___
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun fv ->
      fun ty ->
        let uu___ =
          let uu___1 = FStar_Compiler_Effect.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu___1 fv ty in
        FStar_Compiler_Effect.op_Colon_Equals env1.identifier_info uu___
let (promote_id_info :
  env ->
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      -> unit)
  =
  fun env1 ->
    fun ty_map ->
      let uu___ =
        let uu___1 = FStar_Compiler_Effect.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu___1 ty_map in
      FStar_Compiler_Effect.op_Colon_Equals env1.identifier_info uu___
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1 -> env1.modules
let (current_module : env -> FStar_Ident.lident) = fun env1 -> env1.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun lid ->
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
        lax = (env1.lax);
        lax_universes = (env1.lax_universes);
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
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      FStar_Compiler_Util.for_some
        (fun m ->
           m.FStar_Syntax_Syntax.is_interface &&
             (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))
        env1.modules
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu___ = FStar_Ident.string_of_lid lid in
      FStar_Compiler_Util.smap_try_find (sigtab env1) uu___
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors_Codes.raw_error * Prims.string)) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Ident.string_of_lid l in
      FStar_Compiler_Util.format1 "Name \"%s\" not found" uu___1 in
    (FStar_Errors_Codes.Fatal_NameNotFound, uu___)
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors_Codes.raw_error * Prims.string)) =
  fun v ->
    let uu___ =
      let uu___1 = FStar_Syntax_Print.bv_to_string v in
      FStar_Compiler_Util.format1 "Variable \"%s\" not found" uu___1 in
    (FStar_Errors_Codes.Fatal_VariableNotFound, uu___)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu___ ->
    let uu___1 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Compiler_Range_Type.dummyRange in
    FStar_Syntax_Syntax.U_unif uu___1
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals ->
    fun us ->
      let n = (FStar_Compiler_List.length formals) - Prims.int_one in
      FStar_Compiler_List.mapi
        (fun i -> fun u -> FStar_Syntax_Syntax.UN ((n - i), u)) us
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun ts ->
    fun us ->
      match (ts, us) with
      | (([], t), []) -> ([], t)
      | ((formals, t), uu___) ->
          let vs = mk_univ_subst formals us in
          let uu___1 = FStar_Syntax_Subst.subst vs t in (us, uu___1)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___ ->
    match uu___ with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' = FStar_Compiler_List.map (fun uu___1 -> new_u_univ ()) us in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Compiler_Range_Type.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r ->
    fun t ->
      let uu___ = inst_tscheme t in
      match uu___ with
      | (us, t1) ->
          let uu___1 = FStar_Syntax_Subst.set_use_range r t1 in (us, uu___1)
let (check_effect_is_not_a_template :
  FStar_Syntax_Syntax.eff_decl -> FStar_Compiler_Range_Type.range -> unit) =
  fun ed ->
    fun rng ->
      if
        ((FStar_Compiler_List.length ed.FStar_Syntax_Syntax.univs) <>
           Prims.int_zero)
          ||
          ((FStar_Compiler_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        let msg =
          let uu___ =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu___1 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders in
          FStar_Compiler_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu___ uu___1 in
        FStar_Errors.raise_error
          (FStar_Errors_Codes.Fatal_NotEnoughArgumentsForEffect, msg) rng
      else ()
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts ->
    fun env1 ->
      fun ed ->
        fun uu___ ->
          match uu___ with
          | (us, t) ->
              (check_effect_is_not_a_template ed env1.range;
               if
                 (FStar_Compiler_List.length insts) <>
                   (FStar_Compiler_List.length us)
               then
                 (let uu___3 =
                    let uu___4 =
                      FStar_Compiler_Util.string_of_int
                        (FStar_Compiler_List.length us) in
                    let uu___5 =
                      FStar_Compiler_Util.string_of_int
                        (FStar_Compiler_List.length insts) in
                    let uu___6 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname in
                    let uu___7 = FStar_Syntax_Print.term_to_string t in
                    FStar_Compiler_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu___4 uu___5 uu___6 uu___7 in
                  FStar_Compiler_Effect.failwith uu___3)
               else ();
               (let uu___3 = inst_tscheme_with (us, t) insts in
                FStar_Pervasives_Native.snd uu___3))
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu___ -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu___ -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee -> match projectee with | Maybe -> true | uu___ -> false
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1 ->
    fun l ->
      let cur = current_module env1 in
      let uu___ =
        let uu___1 = FStar_Ident.nsstr l in
        let uu___2 = FStar_Ident.string_of_lid cur in uu___1 = uu___2 in
      if uu___
      then Yes
      else
        (let uu___2 =
           let uu___3 = FStar_Ident.nsstr l in
           let uu___4 = FStar_Ident.string_of_lid cur in
           FStar_Compiler_Util.starts_with uu___3 uu___4 in
         if uu___2
         then
           let lns =
             let uu___3 = FStar_Ident.ns_of_lid l in
             let uu___4 = let uu___5 = FStar_Ident.ident_of_lid l in [uu___5] in
             FStar_Compiler_List.op_At uu___3 uu___4 in
           let cur1 =
             let uu___3 = FStar_Ident.ns_of_lid cur in
             let uu___4 =
               let uu___5 = FStar_Ident.ident_of_lid cur in [uu___5] in
             FStar_Compiler_List.op_At uu___3 uu___4 in
           let rec aux c l1 =
             match (c, l1) with
             | ([], uu___3) -> Maybe
             | (uu___3, []) -> No
             | (hd::tl, hd'::tl') when
                 let uu___3 = FStar_Ident.string_of_id hd in
                 let uu___4 = FStar_Ident.string_of_id hd' in uu___3 = uu___4
                 -> aux tl tl'
             | uu___3 -> No in
           aux cur1 lns
         else No)
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env1 ->
    fun lid ->
      let cur_mod = in_cur_mod env1 lid in
      let cache t =
        (let uu___1 = FStar_Ident.string_of_lid lid in
         FStar_Compiler_Util.smap_add (gamma_cache env1) uu___1 t);
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu___ =
            let uu___1 = FStar_Ident.string_of_lid lid in
            FStar_Compiler_Util.smap_try_find (gamma_cache env1) uu___1 in
          match uu___ with
          | FStar_Pervasives_Native.None ->
              let uu___1 =
                FStar_Compiler_Util.find_map env1.gamma
                  (fun uu___2 ->
                     match uu___2 with
                     | FStar_Syntax_Syntax.Binding_lid (l, (us_names, t))
                         when FStar_Ident.lid_equals lid l ->
                         let us =
                           FStar_Compiler_List.map
                             (fun uu___3 -> FStar_Syntax_Syntax.U_name uu___3)
                             us_names in
                         let uu___3 =
                           let uu___4 = FStar_Ident.range_of_lid l in
                           ((FStar_Pervasives.Inl (us, t)), uu___4) in
                         FStar_Pervasives_Native.Some uu___3
                     | uu___3 -> FStar_Pervasives_Native.None) in
              FStar_Compiler_Util.catch_opt uu___1
                (fun uu___2 ->
                   FStar_Compiler_Util.find_map env1.gamma_sig
                     (fun uu___3 ->
                        match uu___3 with
                        | (uu___4,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               { FStar_Syntax_Syntax.ses = ses;
                                 FStar_Syntax_Syntax.lids = uu___5;_};
                             FStar_Syntax_Syntax.sigrng = uu___6;
                             FStar_Syntax_Syntax.sigquals = uu___7;
                             FStar_Syntax_Syntax.sigmeta = uu___8;
                             FStar_Syntax_Syntax.sigattrs = uu___9;
                             FStar_Syntax_Syntax.sigopens_and_abbrevs =
                               uu___10;
                             FStar_Syntax_Syntax.sigopts = uu___11;_})
                            ->
                            FStar_Compiler_Util.find_map ses
                              (fun se ->
                                 let uu___12 =
                                   FStar_Compiler_Util.for_some
                                     (FStar_Ident.lid_equals lid)
                                     (FStar_Syntax_Util.lids_of_sigelt se) in
                                 if uu___12
                                 then
                                   cache
                                     ((FStar_Pervasives.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids, s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ uu___4 ->
                                  FStar_Pervasives_Native.Some t
                              | uu___4 -> cache t in
                            let uu___4 =
                              FStar_Compiler_List.tryFind
                                (FStar_Ident.lid_equals lid) lids in
                            (match uu___4 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu___5 =
                                   let uu___6 = FStar_Ident.range_of_lid l in
                                   ((FStar_Pervasives.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu___6) in
                                 maybe_cache uu___5)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Compiler_Util.is_some found
      then found
      else
        (let uu___1 = find_in_sigtab env1 lid in
         match uu___1 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl uu___1, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1 ->
    fun attr ->
      let uu___ = FStar_Compiler_Util.smap_try_find (attrtab env1) attr in
      match uu___ with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      let add_one env2 se1 attr =
        let uu___ = let uu___1 = lookup_attr env2 attr in se1 :: uu___1 in
        FStar_Compiler_Util.smap_add (attrtab env2) attr uu___ in
      FStar_Compiler_List.iter
        (fun attr ->
           let uu___ = FStar_Syntax_Util.head_and_args attr in
           match uu___ with
           | (hd, uu___1) ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress hd in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Syntax.lid_of_fv fv in
                      FStar_Ident.string_of_lid uu___4 in
                    add_one env1 se uu___3
                | uu___3 -> ())) se.FStar_Syntax_Syntax.sigattrs
let (try_add_sigelt :
  Prims.bool ->
    env -> FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident -> unit)
  =
  fun force ->
    fun env1 ->
      fun se ->
        fun l ->
          let s = FStar_Ident.string_of_lid l in
          (let uu___1 =
             (Prims.op_Negation force) &&
               (let uu___2 =
                  FStar_Compiler_Util.smap_try_find (sigtab env1) s in
                FStar_Pervasives_Native.uu___is_Some uu___2) in
           if uu___1
           then
             let old_se =
               let uu___2 = FStar_Compiler_Util.smap_try_find (sigtab env1) s in
               FStar_Pervasives_Native.__proj__Some__item__v uu___2 in
             (if
                (FStar_Syntax_Syntax.uu___is_Sig_declare_typ
                   old_se.FStar_Syntax_Syntax.sigel)
                  &&
                  (((FStar_Syntax_Syntax.uu___is_Sig_let
                       se.FStar_Syntax_Syntax.sigel)
                      ||
                      (FStar_Syntax_Syntax.uu___is_Sig_inductive_typ
                         se.FStar_Syntax_Syntax.sigel))
                     ||
                     (FStar_Syntax_Syntax.uu___is_Sig_datacon
                        se.FStar_Syntax_Syntax.sigel))
              then ()
              else
                (let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Errors_Msg.text "Duplicate top-level names" in
                       let uu___7 = FStar_Pprint.arbitrary_string s in
                       FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_Errors_Msg.text "Previously declared at" in
                         let uu___9 =
                           let uu___10 =
                             let uu___11 = FStar_Ident.range_of_lid l in
                             FStar_Compiler_Range_Ops.string_of_range uu___11 in
                           FStar_Pprint.arbitrary_string uu___10 in
                         FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                       [uu___7] in
                     uu___5 :: uu___6 in
                   (FStar_Errors_Codes.Fatal_DuplicateTopLevelNames, uu___4) in
                 let uu___4 = FStar_Ident.range_of_lid l in
                 FStar_Errors.raise_error_doc uu___3 uu___4))
           else ());
          FStar_Compiler_Util.smap_add (sigtab env1) s se
let rec (add_sigelt :
  Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun force ->
    fun env1 ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle
            { FStar_Syntax_Syntax.ses = ses;
              FStar_Syntax_Syntax.lids = uu___;_}
            -> add_sigelts force env1 ses
        | uu___ ->
            let lids = FStar_Syntax_Util.lids_of_sigelt se in
            (FStar_Compiler_List.iter (try_add_sigelt force env1 se) lids;
             add_se_to_attrtab env1 se)
and (add_sigelts :
  Prims.bool -> env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun force ->
    fun env1 ->
      fun ses -> FStar_Compiler_List.iter (add_sigelt force env1) ses
let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Compiler_Range_Type.range)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun bv ->
      FStar_Compiler_Util.find_map env1.gamma
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu___1 =
                 let uu___2 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname in
                 ((id.FStar_Syntax_Syntax.sort), uu___2) in
               FStar_Pervasives_Native.Some uu___1
           | uu___1 -> FStar_Pervasives_Native.None)
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
          FStar_Compiler_Range_Type.range) FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let
            { FStar_Syntax_Syntax.lbs1 = (uu___, lb::[]);
              FStar_Syntax_Syntax.lids1 = uu___1;_}
            ->
            let uu___2 =
              let uu___3 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu___4 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu___3, uu___4) in
            FStar_Pervasives_Native.Some uu___2
        | FStar_Syntax_Syntax.Sig_let
            { FStar_Syntax_Syntax.lbs1 = (uu___, lbs);
              FStar_Syntax_Syntax.lids1 = uu___1;_}
            ->
            FStar_Compiler_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Pervasives.Inl uu___2 ->
                     FStar_Compiler_Effect.failwith "impossible"
                 | FStar_Pervasives.Inr fv ->
                     let uu___2 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu___2
                     then
                       let uu___3 =
                         let uu___4 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu___5 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu___4, uu___5) in
                       FStar_Pervasives_Native.Some uu___3
                     else FStar_Pervasives_Native.None)
        | uu___ -> FStar_Pervasives_Native.None
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Compiler_Range_Type.range ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
          FStar_Compiler_Range_Type.range) FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      fun rng ->
        let inst_ts us_opt1 ts =
          match us_opt1 with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_new_effect ne ->
            let sig_ts =
              FStar_Syntax_Util.effect_sig_ts
                ne.FStar_Syntax_Syntax.signature in
            (check_effect_is_not_a_template ne rng;
             (match us_opt with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some us ->
                  if
                    (FStar_Compiler_List.length us) <>
                      (FStar_Compiler_List.length
                         (FStar_Pervasives_Native.fst sig_ts))
                  then
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStar_Compiler_Util.string_of_int
                                (FStar_Compiler_List.length
                                   (FStar_Pervasives_Native.fst sig_ts)) in
                            let uu___8 =
                              let uu___9 =
                                FStar_Compiler_Util.string_of_int
                                  (FStar_Compiler_List.length us) in
                              Prims.strcat ", got " uu___9 in
                            Prims.strcat uu___7 uu___8 in
                          Prims.strcat ", expected " uu___6 in
                        Prims.strcat uu___4 uu___5 in
                      Prims.strcat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu___3 in
                    FStar_Compiler_Effect.failwith uu___2
                  else ());
             (let uu___2 =
                let uu___3 = inst_ts us_opt sig_ts in
                (uu___3, (se.FStar_Syntax_Syntax.sigrng)) in
              FStar_Pervasives_Native.Some uu___2))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            { FStar_Syntax_Syntax.lid4 = lid; FStar_Syntax_Syntax.us4 = us;
              FStar_Syntax_Syntax.bs2 = binders;
              FStar_Syntax_Syntax.comp1 = uu___;
              FStar_Syntax_Syntax.cflags = uu___1;_}
            ->
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                    FStar_Syntax_Util.arrow binders uu___6 in
                  (us, uu___5) in
                inst_ts us_opt uu___4 in
              (uu___3, (se.FStar_Syntax_Syntax.sigrng)) in
            FStar_Pervasives_Native.Some uu___2
        | uu___ -> FStar_Pervasives_Native.None
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) * FStar_Compiler_Range_Type.range)
          FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun env1 ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        let mapper uu___ =
          match uu___ with
          | (lr, rng) ->
              (match lr with
               | FStar_Pervasives.Inl t ->
                   FStar_Pervasives_Native.Some (t, rng)
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        { FStar_Syntax_Syntax.lid1 = uu___1;
                          FStar_Syntax_Syntax.us1 = uvs;
                          FStar_Syntax_Syntax.t1 = t;
                          FStar_Syntax_Syntax.ty_lid = uu___2;
                          FStar_Syntax_Syntax.num_ty_params = uu___3;
                          FStar_Syntax_Syntax.mutuals1 = uu___4;
                          FStar_Syntax_Syntax.injective_type_params1 = uu___5;_};
                      FStar_Syntax_Syntax.sigrng = uu___6;
                      FStar_Syntax_Syntax.sigquals = uu___7;
                      FStar_Syntax_Syntax.sigmeta = uu___8;
                      FStar_Syntax_Syntax.sigattrs = uu___9;
                      FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
                      FStar_Syntax_Syntax.sigopts = uu___11;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu___12 =
                     let uu___13 = inst_tscheme1 (uvs, t) in (uu___13, rng) in
                   FStar_Pervasives_Native.Some uu___12
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ
                        { FStar_Syntax_Syntax.lid2 = l;
                          FStar_Syntax_Syntax.us2 = uvs;
                          FStar_Syntax_Syntax.t2 = t;_};
                      FStar_Syntax_Syntax.sigrng = uu___1;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu___2;
                      FStar_Syntax_Syntax.sigattrs = uu___3;
                      FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
                      FStar_Syntax_Syntax.sigopts = uu___5;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu___6 =
                     let uu___7 = in_cur_mod env1 l in uu___7 = Yes in
                   if uu___6
                   then
                     (if
                        (FStar_Compiler_List.contains
                           FStar_Syntax_Syntax.Assumption qs)
                          || env1.is_iface
                      then
                        let uu___7 =
                          let uu___8 = inst_tscheme1 (uvs, t) in
                          (uu___8, rng) in
                        FStar_Pervasives_Native.Some uu___7
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu___8 =
                        let uu___9 = inst_tscheme1 (uvs, t) in (uu___9, rng) in
                      FStar_Pervasives_Native.Some uu___8)
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        { FStar_Syntax_Syntax.lid = lid1;
                          FStar_Syntax_Syntax.us = uvs;
                          FStar_Syntax_Syntax.params = tps;
                          FStar_Syntax_Syntax.num_uniform_params = uu___1;
                          FStar_Syntax_Syntax.t = k;
                          FStar_Syntax_Syntax.mutuals = uu___2;
                          FStar_Syntax_Syntax.ds = uu___3;
                          FStar_Syntax_Syntax.injective_type_params = uu___4;_};
                      FStar_Syntax_Syntax.sigrng = uu___5;
                      FStar_Syntax_Syntax.sigquals = uu___6;
                      FStar_Syntax_Syntax.sigmeta = uu___7;
                      FStar_Syntax_Syntax.sigattrs = uu___8;
                      FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
                      FStar_Syntax_Syntax.sigopts = uu___10;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu___11 =
                          let uu___12 = inst_tscheme1 (uvs, k) in
                          (uu___12, rng) in
                        FStar_Pervasives_Native.Some uu___11
                    | uu___11 ->
                        let uu___12 =
                          let uu___13 =
                            let uu___14 =
                              let uu___15 =
                                let uu___16 = FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu___16 in
                              (uvs, uu___15) in
                            inst_tscheme1 uu___14 in
                          (uu___13, rng) in
                        FStar_Pervasives_Native.Some uu___12)
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        { FStar_Syntax_Syntax.lid = lid1;
                          FStar_Syntax_Syntax.us = uvs;
                          FStar_Syntax_Syntax.params = tps;
                          FStar_Syntax_Syntax.num_uniform_params = uu___1;
                          FStar_Syntax_Syntax.t = k;
                          FStar_Syntax_Syntax.mutuals = uu___2;
                          FStar_Syntax_Syntax.ds = uu___3;
                          FStar_Syntax_Syntax.injective_type_params = uu___4;_};
                      FStar_Syntax_Syntax.sigrng = uu___5;
                      FStar_Syntax_Syntax.sigquals = uu___6;
                      FStar_Syntax_Syntax.sigmeta = uu___7;
                      FStar_Syntax_Syntax.sigattrs = uu___8;
                      FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
                      FStar_Syntax_Syntax.sigopts = uu___10;_},
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
                                let uu___16 = FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu___16 in
                              (uvs, uu___15) in
                            inst_tscheme_with uu___14 us in
                          (uu___13, rng) in
                        FStar_Pervasives_Native.Some uu___12)
               | FStar_Pervasives.Inr se ->
                   let uu___1 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu___2;
                          FStar_Syntax_Syntax.sigrng = uu___3;
                          FStar_Syntax_Syntax.sigquals = uu___4;
                          FStar_Syntax_Syntax.sigmeta = uu___5;
                          FStar_Syntax_Syntax.sigattrs = uu___6;
                          FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                          FStar_Syntax_Syntax.sigopts = uu___8;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu___2 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range in
                   FStar_Compiler_Util.map_option
                     (fun uu___2 ->
                        match uu___2 with | (us_t, rng1) -> (us_t, rng1))
                     uu___1) in
        let uu___ =
          let uu___1 = lookup_qname env1 lid in
          FStar_Compiler_Util.bind_opt uu___1 mapper in
        match uu___ with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n = (t.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu___4;
                    FStar_Syntax_Syntax.vars = (t.FStar_Syntax_Syntax.vars);
                    FStar_Syntax_Syntax.hash_code =
                      (t.FStar_Syntax_Syntax.hash_code)
                  } in
                (us, uu___3) in
              (uu___2, r) in
            FStar_Pervasives_Native.Some uu___1
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = lookup_qname env1 l in
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu___1 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Compiler_Range_Type.range))
  =
  fun env1 ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu___ = try_lookup_bv env1 bv in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 = variable_not_found bv in
          FStar_Errors.raise_error uu___1 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu___1 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu___2 =
            let uu___3 = FStar_Compiler_Range_Type.use_range bvr in
            FStar_Compiler_Range_Type.set_use_range r uu___3 in
          (uu___1, uu___2)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Compiler_Range_Type.range) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 =
            let uu___1 = FStar_Compiler_Range_Type.use_range use_range in
            FStar_Compiler_Range_Type.set_use_range r uu___1 in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu___3) in
            (uu___2, r1) in
          FStar_Pervasives_Native.Some uu___1
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ * FStar_Compiler_Range_Type.range)
          FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun us ->
      fun l ->
        let uu___ =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu___1, t), r) ->
            let use_range = FStar_Ident.range_of_lid l in
            let r1 =
              let uu___2 = FStar_Compiler_Range_Type.use_range use_range in
              FStar_Compiler_Range_Type.set_use_range r uu___2 in
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.set_use_range use_range t in
              (uu___3, r1) in
            FStar_Pervasives_Native.Some uu___2
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Compiler_Range_Type.range))
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid env1 l in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 = name_not_found l in
          let uu___2 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu___1 uu___2
      | FStar_Pervasives_Native.Some v -> v
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1 ->
    fun x ->
      let uu___ =
        FStar_Compiler_List.find
          (fun uu___1 ->
             match uu___1 with
             | FStar_Syntax_Syntax.Binding_univ y ->
                 let uu___2 = FStar_Ident.string_of_id x in
                 let uu___3 = FStar_Ident.string_of_id y in uu___2 = uu___3
             | uu___2 -> false) env1.gamma in
      FStar_Compiler_Option.isSome uu___
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                { FStar_Syntax_Syntax.lid2 = uu___1;
                  FStar_Syntax_Syntax.us2 = uvs;
                  FStar_Syntax_Syntax.t2 = t;_};
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu___3;
              FStar_Syntax_Syntax.sigattrs = uu___4;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
              FStar_Syntax_Syntax.sigopts = uu___6;_},
            FStar_Pervasives_Native.None),
           uu___7)
          ->
          let uu___8 =
            let uu___9 =
              let uu___10 =
                let uu___11 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu___11 t in
              (uvs, uu___10) in
            (uu___9, q) in
          FStar_Pervasives_Native.Some uu___8
      | uu___1 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                { FStar_Syntax_Syntax.lid2 = uu___1;
                  FStar_Syntax_Syntax.us2 = uvs;
                  FStar_Syntax_Syntax.t2 = t;_};
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = uu___3;
              FStar_Syntax_Syntax.sigmeta = uu___4;
              FStar_Syntax_Syntax.sigattrs = uu___5;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
              FStar_Syntax_Syntax.sigopts = uu___7;_},
            FStar_Pervasives_Native.None),
           uu___8)
          ->
          let uu___9 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu___9 (uvs, t)
      | uu___1 ->
          let uu___2 = name_not_found lid in
          let uu___3 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu___2 uu___3
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                { FStar_Syntax_Syntax.lid1 = uu___1;
                  FStar_Syntax_Syntax.us1 = uvs; FStar_Syntax_Syntax.t1 = t;
                  FStar_Syntax_Syntax.ty_lid = uu___2;
                  FStar_Syntax_Syntax.num_ty_params = uu___3;
                  FStar_Syntax_Syntax.mutuals1 = uu___4;
                  FStar_Syntax_Syntax.injective_type_params1 = uu___5;_};
              FStar_Syntax_Syntax.sigrng = uu___6;
              FStar_Syntax_Syntax.sigquals = uu___7;
              FStar_Syntax_Syntax.sigmeta = uu___8;
              FStar_Syntax_Syntax.sigattrs = uu___9;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
              FStar_Syntax_Syntax.sigopts = uu___11;_},
            FStar_Pervasives_Native.None),
           uu___12)
          ->
          let uu___13 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu___13 (uvs, t)
      | uu___1 ->
          let uu___2 = name_not_found lid in
          let uu___3 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu___2 uu___3
let (lookup_and_inst_datacon :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident -> FStar_Syntax_Syntax.typ)
  =
  fun env1 ->
    fun us ->
      fun lid ->
        let uu___ = lookup_qname env1 lid in
        match uu___ with
        | FStar_Pervasives_Native.Some
            (FStar_Pervasives.Inr
             ({
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  { FStar_Syntax_Syntax.lid1 = uu___1;
                    FStar_Syntax_Syntax.us1 = uvs;
                    FStar_Syntax_Syntax.t1 = t;
                    FStar_Syntax_Syntax.ty_lid = uu___2;
                    FStar_Syntax_Syntax.num_ty_params = uu___3;
                    FStar_Syntax_Syntax.mutuals1 = uu___4;
                    FStar_Syntax_Syntax.injective_type_params1 = uu___5;_};
                FStar_Syntax_Syntax.sigrng = uu___6;
                FStar_Syntax_Syntax.sigquals = uu___7;
                FStar_Syntax_Syntax.sigmeta = uu___8;
                FStar_Syntax_Syntax.sigattrs = uu___9;
                FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
                FStar_Syntax_Syntax.sigopts = uu___11;_},
              FStar_Pervasives_Native.None),
             uu___12)
            ->
            let uu___13 = inst_tscheme_with (uvs, t) us in
            FStar_Pervasives_Native.snd uu___13
        | uu___1 ->
            let uu___2 = name_not_found lid in
            let uu___3 = FStar_Ident.range_of_lid lid in
            FStar_Errors.raise_error uu___2 uu___3
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                { FStar_Syntax_Syntax.lid = uu___1;
                  FStar_Syntax_Syntax.us = uu___2;
                  FStar_Syntax_Syntax.params = uu___3;
                  FStar_Syntax_Syntax.num_uniform_params = uu___4;
                  FStar_Syntax_Syntax.t = uu___5;
                  FStar_Syntax_Syntax.mutuals = uu___6;
                  FStar_Syntax_Syntax.ds = dcs;
                  FStar_Syntax_Syntax.injective_type_params = uu___7;_};
              FStar_Syntax_Syntax.sigrng = uu___8;
              FStar_Syntax_Syntax.sigquals = uu___9;
              FStar_Syntax_Syntax.sigmeta = uu___10;
              FStar_Syntax_Syntax.sigattrs = uu___11;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
              FStar_Syntax_Syntax.sigopts = uu___13;_},
            uu___14),
           uu___15)
          -> (true, dcs)
      | uu___1 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                { FStar_Syntax_Syntax.lid1 = uu___1;
                  FStar_Syntax_Syntax.us1 = uu___2;
                  FStar_Syntax_Syntax.t1 = uu___3;
                  FStar_Syntax_Syntax.ty_lid = l;
                  FStar_Syntax_Syntax.num_ty_params = uu___4;
                  FStar_Syntax_Syntax.mutuals1 = uu___5;
                  FStar_Syntax_Syntax.injective_type_params1 = uu___6;_};
              FStar_Syntax_Syntax.sigrng = uu___7;
              FStar_Syntax_Syntax.sigquals = uu___8;
              FStar_Syntax_Syntax.sigmeta = uu___9;
              FStar_Syntax_Syntax.sigattrs = uu___10;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
              FStar_Syntax_Syntax.sigopts = uu___12;_},
            uu___13),
           uu___14)
          -> l
      | uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Compiler_Util.format1 "Not a datacon: %s" uu___3 in
          FStar_Compiler_Effect.failwith uu___2
let (num_datacon_non_injective_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                { FStar_Syntax_Syntax.lid1 = uu___1;
                  FStar_Syntax_Syntax.us1 = uu___2;
                  FStar_Syntax_Syntax.t1 = uu___3;
                  FStar_Syntax_Syntax.ty_lid = uu___4;
                  FStar_Syntax_Syntax.num_ty_params = num_ty_params;
                  FStar_Syntax_Syntax.mutuals1 = uu___5;
                  FStar_Syntax_Syntax.injective_type_params1 =
                    injective_type_params;_};
              FStar_Syntax_Syntax.sigrng = uu___6;
              FStar_Syntax_Syntax.sigquals = uu___7;
              FStar_Syntax_Syntax.sigmeta = uu___8;
              FStar_Syntax_Syntax.sigattrs = uu___9;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
              FStar_Syntax_Syntax.sigopts = uu___11;_},
            uu___12),
           uu___13)
          ->
          if injective_type_params
          then FStar_Pervasives_Native.Some Prims.int_zero
          else FStar_Pervasives_Native.Some num_ty_params
      | uu___1 -> FStar_Pervasives_Native.None
let (lookup_definition_qninfo_aux :
  Prims.bool ->
    delta_level Prims.list ->
      FStar_Ident.lident ->
        qninfo ->
          (FStar_Syntax_Syntax.univ_name Prims.list *
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.option)
  =
  fun rec_ok ->
    fun delta_levels ->
      fun lid ->
        fun qninfo1 ->
          let visible quals =
            FStar_Compiler_Util.for_some
              (fun dl -> FStar_Compiler_Util.for_some (visible_at dl) quals)
              delta_levels in
          match qninfo1 with
          | FStar_Pervasives_Native.Some
              (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None),
               uu___)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let
                   { FStar_Syntax_Syntax.lbs1 = (is_rec, lbs);
                     FStar_Syntax_Syntax.lids1 = uu___1;_}
                   when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Compiler_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Compiler_Util.right
                            lb.FStar_Syntax_Syntax.lbname in
                        let uu___2 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                        if uu___2
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu___1 -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun lid ->
      fun qninfo1 ->
        lookup_definition_qninfo_aux true delta_levels lid qninfo1
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun env1 ->
      fun lid ->
        let uu___ = lookup_qname env1 lid in
        lookup_definition_qninfo delta_levels lid uu___
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun env1 ->
      fun lid ->
        let uu___ = lookup_qname env1 lid in
        lookup_definition_qninfo_aux false delta_levels lid uu___
let rec (delta_depth_of_qninfo_lid :
  env -> FStar_Ident.lident -> qninfo -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun lid ->
      fun qn ->
        match qn with
        | FStar_Pervasives_Native.None -> FStar_Syntax_Syntax.delta_constant
        | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl uu___, uu___1)
            -> FStar_Syntax_Syntax.delta_constant
        | FStar_Pervasives_Native.Some
            (FStar_Pervasives.Inr (se, uu___), uu___1) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_inductive_typ uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_bundle uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_datacon uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_declare_typ uu___2 ->
                 let d0 =
                   let uu___3 = FStar_Syntax_Util.is_primop_lid lid in
                   if uu___3
                   then FStar_Syntax_Syntax.delta_equational
                   else FStar_Syntax_Syntax.delta_constant in
                 let uu___3 =
                   (FStar_Compiler_Util.for_some
                      FStar_Syntax_Syntax.uu___is_Assumption
                      se.FStar_Syntax_Syntax.sigquals)
                     &&
                     (let uu___4 =
                        FStar_Compiler_Util.for_some
                          FStar_Syntax_Syntax.uu___is_New
                          se.FStar_Syntax_Syntax.sigquals in
                      Prims.op_Negation uu___4) in
                 if uu___3 then FStar_Syntax_Syntax.Delta_abstract d0 else d0
             | FStar_Syntax_Syntax.Sig_let
                 { FStar_Syntax_Syntax.lbs1 = (uu___2, lbs);
                   FStar_Syntax_Syntax.lids1 = uu___3;_}
                 ->
                 let uu___4 =
                   FStar_Compiler_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Compiler_Util.right
                            lb.FStar_Syntax_Syntax.lbname in
                        let uu___5 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                        if uu___5
                        then
                          let uu___6 =
                            let uu___7 =
                              delta_depth_of_term env1
                                lb.FStar_Syntax_Syntax.lbdef in
                            FStar_Syntax_Util.incr_delta_depth uu___7 in
                          FStar_Pervasives_Native.Some uu___6
                        else FStar_Pervasives_Native.None) in
                 FStar_Compiler_Util.must uu___4
             | FStar_Syntax_Syntax.Sig_fail uu___2 ->
                 FStar_Compiler_Effect.failwith
                   "impossible: delta_depth_of_qninfo"
             | FStar_Syntax_Syntax.Sig_splice uu___2 ->
                 FStar_Compiler_Effect.failwith
                   "impossible: delta_depth_of_qninfo"
             | FStar_Syntax_Syntax.Sig_assume uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_new_effect uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_sub_effect uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_effect_abbrev uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_pragma uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___2 ->
                 FStar_Syntax_Syntax.delta_constant
             | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___2 ->
                 FStar_Syntax_Syntax.delta_constant)
and (delta_depth_of_qninfo :
  env -> FStar_Syntax_Syntax.fv -> qninfo -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env1 ->
    fun fv ->
      fun qn ->
        delta_depth_of_qninfo_lid env1
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v qn
and (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid lid in
        FStar_Compiler_Util.smap_try_find env1.fv_delta_depths uu___1 in
      match uu___ with
      | FStar_Pervasives_Native.Some dd -> dd
      | FStar_Pervasives_Native.None ->
          ((let uu___2 = FStar_Ident.string_of_lid lid in
            FStar_Compiler_Util.smap_add env1.fv_delta_depths uu___2
              FStar_Syntax_Syntax.delta_equational);
           (let d =
              let uu___2 =
                lookup_qname env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              delta_depth_of_qninfo env1 fv uu___2 in
            (let uu___3 = FStar_Ident.string_of_lid lid in
             FStar_Compiler_Util.smap_add env1.fv_delta_depths uu___3 d);
            d))
and (fv_delta_depth :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let d = delta_depth_of_fv env1 fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract
          (FStar_Syntax_Syntax.Delta_constant_at_level l) ->
          let uu___ =
            (let uu___1 = FStar_Ident.string_of_lid env1.curmodule in
             let uu___2 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu___1 = uu___2) && (Prims.op_Negation env1.is_iface) in
          if uu___
          then FStar_Syntax_Syntax.Delta_constant_at_level l
          else FStar_Syntax_Syntax.delta_constant
      | d1 -> d1
and (delta_depth_of_term :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu___ ->
          FStar_Compiler_Effect.failwith "Impossible (delta depth of term)"
      | FStar_Syntax_Syntax.Tm_delayed uu___ ->
          FStar_Compiler_Effect.failwith "Impossible (delta depth of term)"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu___ = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env1 uu___
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_delta_depth env1 fv
      | FStar_Syntax_Syntax.Tm_bvar uu___ ->
          FStar_Syntax_Syntax.delta_equational
      | FStar_Syntax_Syntax.Tm_name uu___ ->
          FStar_Syntax_Syntax.delta_equational
      | FStar_Syntax_Syntax.Tm_match uu___ ->
          FStar_Syntax_Syntax.delta_equational
      | FStar_Syntax_Syntax.Tm_uvar uu___ ->
          FStar_Syntax_Syntax.delta_equational
      | FStar_Syntax_Syntax.Tm_unknown ->
          FStar_Syntax_Syntax.delta_equational
      | FStar_Syntax_Syntax.Tm_type uu___ ->
          FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu___ ->
          FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_constant uu___ ->
          FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu___ ->
          FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu___) ->
          delta_depth_of_term env1 t2
      | FStar_Syntax_Syntax.Tm_refine
          {
            FStar_Syntax_Syntax.b =
              { FStar_Syntax_Syntax.ppname = uu___;
                FStar_Syntax_Syntax.index = uu___1;
                FStar_Syntax_Syntax.sort = t2;_};
            FStar_Syntax_Syntax.phi = uu___2;_}
          -> delta_depth_of_term env1 t2
      | FStar_Syntax_Syntax.Tm_ascribed
          { FStar_Syntax_Syntax.tm = t2; FStar_Syntax_Syntax.asc = uu___;
            FStar_Syntax_Syntax.eff_opt = uu___1;_}
          -> delta_depth_of_term env1 t2
      | FStar_Syntax_Syntax.Tm_app
          { FStar_Syntax_Syntax.hd = t2; FStar_Syntax_Syntax.args = uu___;_}
          -> delta_depth_of_term env1 t2
      | FStar_Syntax_Syntax.Tm_abs
          { FStar_Syntax_Syntax.bs = uu___; FStar_Syntax_Syntax.body = t2;
            FStar_Syntax_Syntax.rc_opt = uu___1;_}
          -> delta_depth_of_term env1 t2
      | FStar_Syntax_Syntax.Tm_let
          { FStar_Syntax_Syntax.lbs = uu___;
            FStar_Syntax_Syntax.body1 = t2;_}
          -> delta_depth_of_term env1 t2
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, uu___), uu___1)
        -> FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu___ -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr (se, uu___), uu___1)
        -> FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu___ -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid -> let uu___ = lookup_qname env1 lid in attrs_of_qninfo uu___
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu___ = lookup_attrs_of_lid env1 fv_lid in
        match uu___ with
        | FStar_Pervasives_Native.None -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu___1 =
              FStar_Compiler_Util.for_some
                (fun tm ->
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Util.un_uinst tm in
                     uu___3.FStar_Syntax_Syntax.n in
                   match uu___2 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                   | uu___3 -> false) attrs in
            (true, uu___1)
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu___ = fv_exists_and_has_attr env1 fv_lid attr_lid in
        FStar_Pervasives_Native.snd uu___
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env1 ->
    fun fv ->
      fun attr_lid ->
        fv_with_lid_has_attr env1
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
let cache_in_fv_tab :
  'a .
    'a FStar_Compiler_Util.smap ->
      FStar_Syntax_Syntax.fv -> (unit -> (Prims.bool * 'a)) -> 'a
  =
  fun tab ->
    fun fv ->
      fun f ->
        let s =
          let uu___ = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu___ in
        let uu___ = FStar_Compiler_Util.smap_try_find tab s in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 = f () in
            (match uu___1 with
             | (should_cache, res) ->
                 (if should_cache
                  then FStar_Compiler_Util.smap_add tab s res
                  else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
let (fv_has_erasable_attr : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1 ->
    fun fv ->
      let f uu___ =
        let uu___1 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr in
        match uu___1 with | (ex, erasable) -> (ex, erasable) in
      cache_in_fv_tab env1.erasable_types_tab fv f
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fv ->
      let f uu___ =
        let attrs =
          let uu___1 = FStar_Syntax_Syntax.lid_of_fv fv in
          lookup_attrs_of_lid env1 uu___1 in
        match attrs with
        | FStar_Pervasives_Native.None ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Compiler_Util.find_map attrs1
                (fun x ->
                   let uu___1 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr in
                   FStar_Pervasives_Native.fst uu___1) in
            (true, res) in
      cache_in_fv_tab env1.strict_args_tab fv f
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ftv ->
      let uu___ = lookup_qname env1 ftv in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None), uu___1)
          ->
          let uu___2 =
            effect_signature FStar_Pervasives_Native.None se env1.range in
          (match uu___2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu___3, t), r) ->
               let uu___4 =
                 let uu___5 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu___5 t in
               FStar_Pervasives_Native.Some uu___4)
      | uu___1 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun ftv ->
      let uu___ = try_lookup_effect_lid env1 ftv in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 = name_not_found ftv in
          let uu___2 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu___1 uu___2
      | FStar_Pervasives_Native.Some k -> k
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun univ_insts ->
      fun lid0 ->
        let uu___ = lookup_qname env1 lid0 in
        match uu___ with
        | FStar_Pervasives_Native.Some
            (FStar_Pervasives.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  { FStar_Syntax_Syntax.lid4 = lid;
                    FStar_Syntax_Syntax.us4 = univs;
                    FStar_Syntax_Syntax.bs2 = binders;
                    FStar_Syntax_Syntax.comp1 = c;
                    FStar_Syntax_Syntax.cflags = uu___1;_};
                FStar_Syntax_Syntax.sigrng = uu___2;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu___3;
                FStar_Syntax_Syntax.sigattrs = uu___4;
                FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
                FStar_Syntax_Syntax.sigopts = uu___6;_},
              FStar_Pervasives_Native.None),
             uu___7)
            ->
            let lid1 =
              let uu___8 =
                let uu___9 = FStar_Ident.range_of_lid lid in
                let uu___10 =
                  let uu___11 = FStar_Ident.range_of_lid lid0 in
                  FStar_Compiler_Range_Type.use_range uu___11 in
                FStar_Compiler_Range_Type.set_use_range uu___9 uu___10 in
              FStar_Ident.set_lid_range lid uu___8 in
            let uu___8 =
              FStar_Compiler_Util.for_some
                (fun uu___9 ->
                   match uu___9 with
                   | FStar_Syntax_Syntax.Irreducible -> true
                   | uu___10 -> false) quals in
            if uu___8
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_Compiler_List.length univ_insts) =
                     (FStar_Compiler_List.length univs)
                 then univ_insts
                 else
                   (let uu___11 =
                      let uu___12 =
                        let uu___13 = get_range env1 in
                        FStar_Compiler_Range_Ops.string_of_range uu___13 in
                      let uu___13 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu___14 =
                        FStar_Compiler_Util.string_of_int
                          (FStar_Compiler_List.length univ_insts) in
                      FStar_Compiler_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu___12 uu___13 uu___14 in
                    FStar_Compiler_Effect.failwith uu___11) in
               match (binders, univs) with
               | ([], uu___10) ->
                   FStar_Compiler_Effect.failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu___10, uu___11::uu___12::uu___13) ->
                   let uu___14 =
                     let uu___15 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu___16 =
                       FStar_Compiler_Util.string_of_int
                         (FStar_Compiler_List.length univs) in
                     FStar_Compiler_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu___15 uu___16 in
                   FStar_Compiler_Effect.failwith uu___14
               | uu___10 ->
                   let uu___11 =
                     let uu___12 =
                       let uu___13 = FStar_Syntax_Util.arrow binders c in
                       (univs, uu___13) in
                     inst_tscheme_with uu___12 insts in
                   (match uu___11 with
                    | (uu___12, t) ->
                        let t1 =
                          let uu___13 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu___13 t in
                        let uu___13 =
                          let uu___14 = FStar_Syntax_Subst.compress t1 in
                          uu___14.FStar_Syntax_Syntax.n in
                        (match uu___13 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             { FStar_Syntax_Syntax.bs1 = binders1;
                               FStar_Syntax_Syntax.comp = c1;_}
                             -> FStar_Pervasives_Native.Some (binders1, c1)
                         | uu___14 ->
                             FStar_Compiler_Effect.failwith "Impossible")))
        | uu___1 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun l ->
      let rec find l1 =
        let uu___ =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu___1, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu___2 = find l2 in
            (match uu___2 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid l in
          FStar_Compiler_Util.smap_try_find env1.normalized_eff_names uu___1 in
        match uu___ with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu___1 = find l in
            (match uu___1 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu___3 = FStar_Ident.string_of_lid l in
                   FStar_Compiler_Util.smap_add env1.normalized_eff_names
                     uu___3 m);
                  m)) in
      let uu___ = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu___
let (is_erasable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = norm_eff_name env1 l in
      (FStar_Ident.lid_equals uu___ FStar_Parser_Const.effect_GHOST_lid) ||
        (let uu___1 =
           FStar_Syntax_Syntax.lid_as_fv uu___ FStar_Pervasives_Native.None in
         fv_has_erasable_attr env1 uu___1)
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Util.unrefine t in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_type uu___1 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (fv_has_erasable_attr env1 fv)
      | FStar_Syntax_Syntax.Tm_app
          { FStar_Syntax_Syntax.hd = head;
            FStar_Syntax_Syntax.args = uu___1;_}
          -> non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) -> non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow
          { FStar_Syntax_Syntax.bs1 = uu___1; FStar_Syntax_Syntax.comp = c;_}
          ->
          ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
             (non_informative env1 (FStar_Syntax_Util.comp_result c)))
            ||
            (is_erasable_effect env1 (FStar_Syntax_Util.comp_effect_name c))
      | uu___1 -> false
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Compiler_Range_Type.range -> Prims.int)
  =
  fun env1 ->
    fun name ->
      fun r ->
        let sig_t =
          let uu___ = lookup_effect_lid env1 name in
          FStar_Syntax_Subst.compress uu___ in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow
            { FStar_Syntax_Syntax.bs1 = _a::bs;
              FStar_Syntax_Syntax.comp = uu___;_}
            -> FStar_Compiler_List.length bs
        | uu___ ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Ident.string_of_lid name in
                let uu___4 = FStar_Syntax_Print.term_to_string sig_t in
                FStar_Compiler_Util.format2
                  "Signature for %s not an arrow (%s)" uu___3 uu___4 in
              (FStar_Errors_Codes.Fatal_UnexpectedSignatureForMonad, uu___2) in
            FStar_Errors.raise_error uu___1 r
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1 ->
    fun l ->
      let l1 = norm_eff_name env1 l in
      let uu___ = lookup_qname env1 l1 in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu___1;
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu___3;
              FStar_Syntax_Syntax.sigattrs = uu___4;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
              FStar_Syntax_Syntax.sigopts = uu___6;_},
            uu___7),
           uu___8)
          -> q
      | uu___1 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      fun i ->
        let fail uu___ =
          let uu___1 =
            let uu___2 = FStar_Compiler_Util.string_of_int i in
            let uu___3 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Compiler_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu___2 uu___3 in
          FStar_Compiler_Effect.failwith uu___1 in
        let uu___ = lookup_datacon env1 lid in
        match uu___ with
        | (uu___1, t) ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.compress t in
              uu___3.FStar_Syntax_Syntax.n in
            (match uu___2 with
             | FStar_Syntax_Syntax.Tm_arrow
                 { FStar_Syntax_Syntax.bs1 = binders;
                   FStar_Syntax_Syntax.comp = uu___3;_}
                 ->
                 if
                   (i < Prims.int_zero) ||
                     (i >= (FStar_Compiler_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_Compiler_List.nth binders i in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      b.FStar_Syntax_Syntax.binder_bv i)
             | uu___3 -> fail ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = lookup_qname env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                uu___1;
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu___3;
              FStar_Syntax_Syntax.sigattrs = uu___4;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
              FStar_Syntax_Syntax.sigopts = uu___6;_},
            uu___7),
           uu___8)
          ->
          FStar_Compiler_Util.for_some
            (fun uu___9 ->
               match uu___9 with
               | FStar_Syntax_Syntax.Projector uu___10 -> true
               | uu___10 -> false) quals
      | uu___1 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                uu___1;
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = uu___3;
              FStar_Syntax_Syntax.sigmeta = uu___4;
              FStar_Syntax_Syntax.sigattrs = uu___5;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
              FStar_Syntax_Syntax.sigopts = uu___7;_},
            uu___8),
           uu___9)
          -> true
      | uu___1 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ uu___1;
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu___3;
              FStar_Syntax_Syntax.sigattrs = uu___4;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
              FStar_Syntax_Syntax.sigopts = uu___6;_},
            uu___7),
           uu___8)
          ->
          FStar_Compiler_Util.for_some
            (fun uu___9 ->
               match uu___9 with
               | FStar_Syntax_Syntax.RecordType uu___10 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu___10 -> true
               | uu___10 -> false) quals
      | uu___1 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Pervasives.Inr
         ({ FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let uu___;
            FStar_Syntax_Syntax.sigrng = uu___1;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu___2;
            FStar_Syntax_Syntax.sigattrs = uu___3;
            FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
            FStar_Syntax_Syntax.sigopts = uu___5;_},
          uu___6),
         uu___7)
        ->
        FStar_Compiler_Util.for_some
          (fun uu___8 ->
             match uu___8 with
             | FStar_Syntax_Syntax.Action uu___9 -> true
             | uu___9 -> false) quals
    | uu___ -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid -> let uu___ = lookup_qname env1 lid in qninfo_is_action uu___
let (is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation] in
  fun env1 ->
    fun head ->
      let uu___ =
        let uu___1 = FStar_Syntax_Util.un_uinst head in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (FStar_Compiler_Util.for_some
             (FStar_Ident.lid_equals
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
             interpreted_symbols)
            ||
            (let uu___1 = delta_depth_of_fv env1 fv in
             (match uu___1 with
              | FStar_Syntax_Syntax.Delta_equational_at_level uu___2 -> true
              | uu___2 -> false))
      | uu___1 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = lookup_qname env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr (se, uu___1), uu___2) ->
          FStar_Compiler_Util.for_some
            (fun uu___3 ->
               match uu___3 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu___4 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu___1 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Pervasives.Inl uu___ -> FStar_Pervasives_Native.Some false
        | FStar_Pervasives.Inr (se, uu___) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu___1 ->
                 FStar_Pervasives_Native.Some
                   (FStar_Compiler_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu___1 ->
                 FStar_Pervasives_Native.Some true
             | uu___1 -> FStar_Pervasives_Native.Some false) in
      let uu___ =
        let uu___1 = lookup_qname env1 lid in
        FStar_Compiler_Util.bind_opt uu___1 mapper in
      match uu___ with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                { FStar_Syntax_Syntax.lid = uu___1;
                  FStar_Syntax_Syntax.us = uu___2;
                  FStar_Syntax_Syntax.params = tps;
                  FStar_Syntax_Syntax.num_uniform_params = uu___3;
                  FStar_Syntax_Syntax.t = uu___4;
                  FStar_Syntax_Syntax.mutuals = uu___5;
                  FStar_Syntax_Syntax.ds = uu___6;
                  FStar_Syntax_Syntax.injective_type_params = uu___7;_};
              FStar_Syntax_Syntax.sigrng = uu___8;
              FStar_Syntax_Syntax.sigquals = uu___9;
              FStar_Syntax_Syntax.sigmeta = uu___10;
              FStar_Syntax_Syntax.sigattrs = uu___11;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
              FStar_Syntax_Syntax.sigopts = uu___13;_},
            uu___14),
           uu___15)
          -> FStar_Pervasives_Native.Some (FStar_Compiler_List.length tps)
      | uu___1 -> FStar_Pervasives_Native.None
let (num_inductive_uniform_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                { FStar_Syntax_Syntax.lid = uu___1;
                  FStar_Syntax_Syntax.us = uu___2;
                  FStar_Syntax_Syntax.params = uu___3;
                  FStar_Syntax_Syntax.num_uniform_params = num_uniform;
                  FStar_Syntax_Syntax.t = uu___4;
                  FStar_Syntax_Syntax.mutuals = uu___5;
                  FStar_Syntax_Syntax.ds = uu___6;
                  FStar_Syntax_Syntax.injective_type_params = uu___7;_};
              FStar_Syntax_Syntax.sigrng = uu___8;
              FStar_Syntax_Syntax.sigquals = uu___9;
              FStar_Syntax_Syntax.sigmeta = uu___10;
              FStar_Syntax_Syntax.sigattrs = uu___11;
              FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
              FStar_Syntax_Syntax.sigopts = uu___13;_},
            uu___14),
           uu___15)
          ->
          (match num_uniform with
           | FStar_Pervasives_Native.None ->
               let uu___16 =
                 let uu___17 =
                   let uu___18 = FStar_Ident.string_of_lid lid in
                   FStar_Compiler_Util.format1
                     "Internal error: Inductive %s is not decorated with its uniform type parameters"
                     uu___18 in
                 (FStar_Errors_Codes.Fatal_UnexpectedInductivetype, uu___17) in
               let uu___17 = FStar_Ident.range_of_lid lid in
               FStar_Errors.raise_error uu___16 uu___17
           | FStar_Pervasives_Native.Some n -> FStar_Pervasives_Native.Some n)
      | uu___1 -> FStar_Pervasives_Native.None
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      FStar_Compiler_Util.find_opt
        (fun uu___ ->
           match uu___ with
           | (d, uu___1) ->
               FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
        (env1.effects).decls
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1 ->
    fun l ->
      let uu___ = effect_decl_opt env1 l in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 = name_not_found l in
          let uu___2 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu___1 uu___2
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (get_lid_valued_effect_attr :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident FStar_Pervasives_Native.option ->
          FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun eff_lid ->
      fun attr_name_lid ->
        fun default_if_attr_has_no_arg ->
          let attr_args =
            let uu___ =
              let uu___1 =
                let uu___2 = norm_eff_name env1 eff_lid in
                lookup_attrs_of_lid env1 uu___2 in
              FStar_Compiler_Util.dflt [] uu___1 in
            FStar_Syntax_Util.get_attribute attr_name_lid uu___ in
          match attr_args with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some args ->
              if (FStar_Compiler_List.length args) = Prims.int_zero
              then default_if_attr_has_no_arg
              else
                (let uu___1 = FStar_Compiler_List.hd args in
                 match uu___1 with
                 | (t, uu___2) ->
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Subst.compress t in
                       uu___4.FStar_Syntax_Syntax.n in
                     (match uu___3 with
                      | FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_string (s, uu___4)) ->
                          let uu___5 = FStar_Ident.lid_of_str s in
                          FStar_Pervasives_Native.Some uu___5
                      | uu___4 ->
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = FStar_Ident.string_of_lid eff_lid in
                              let uu___8 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Compiler_Util.format2
                                "The argument for the effect attribute for %s is not a constant string, it is %s\n"
                                uu___7 uu___8 in
                            (FStar_Errors_Codes.Fatal_UnexpectedEffect,
                              uu___6) in
                          FStar_Errors.raise_error uu___5
                            t.FStar_Syntax_Syntax.pos))
let (get_default_effect :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      get_lid_valued_effect_attr env1 lid
        FStar_Parser_Const.default_effect_attr FStar_Pervasives_Native.None
let (get_top_level_effect :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      get_lid_valued_effect_attr env1 lid
        FStar_Parser_Const.top_level_effect_attr
        (FStar_Pervasives_Native.Some lid)
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = get_effect_decl env1 l in
      FStar_Syntax_Util.is_layered uu___
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu___ -> fun c -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu___ ->
            fun uu___1 -> fun e -> FStar_Compiler_Util.return_all e))
  }
let (join_opt :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu___ = FStar_Ident.lid_equals l1 l2 in
        if uu___
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu___2 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu___2
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu___4 =
                FStar_Compiler_Util.find_opt
                  (fun uu___5 ->
                     match uu___5 with
                     | (m1, m2, uu___6, uu___7, uu___8) ->
                         (FStar_Ident.lid_equals l1 m1) &&
                           (FStar_Ident.lid_equals l2 m2))
                  (env1.effects).joins in
              match uu___4 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (uu___5, uu___6, m3, j1, j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu___ = join_opt env1 l1 l2 in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Print.lid_to_string l1 in
                let uu___4 = FStar_Syntax_Print.lid_to_string l2 in
                FStar_Compiler_Util.format2
                  "Effects %s and %s cannot be composed" uu___3 uu___4 in
              (FStar_Errors_Codes.Fatal_EffectsCannotBeComposed, uu___2) in
            FStar_Errors.raise_error uu___1 env1.range
        | FStar_Pervasives_Native.Some t -> t
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu___ =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu___
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift; mpath = []
            }
        else
          FStar_Compiler_Util.find_opt
            (fun e ->
               (FStar_Ident.lid_equals l1 e.msource) &&
                 (FStar_Ident.lid_equals l2 e.mtarget)) (env1.effects).order
let wp_sig_aux :
  'uuuuu .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuu) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls ->
    fun m ->
      let uu___ =
        FStar_Compiler_Util.find_opt
          (fun uu___1 ->
             match uu___1 with
             | (d, uu___2) ->
                 FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m) decls in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid m in
            FStar_Compiler_Util.format1
              "Impossible: declaration for monad %s not found" uu___2 in
          FStar_Compiler_Effect.failwith uu___1
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu___1 =
            let uu___2 =
              FStar_Syntax_Util.effect_sig_ts
                md.FStar_Syntax_Syntax.signature in
            inst_tscheme uu___2 in
          (match uu___1 with
           | (uu___2, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   { FStar_Syntax_Syntax.bs1 = b::wp_b::[];
                     FStar_Syntax_Syntax.comp = c;_})
                    when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    ->
                    ((b.FStar_Syntax_Syntax.binder_bv),
                      ((wp_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort))
                | uu___3 -> FStar_Compiler_Effect.failwith "Impossible"))
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env1 -> fun m -> wp_sig_aux (env1.effects).decls m
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_Compiler_List.collect
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Binding_var x -> [x]
         | FStar_Syntax_Syntax.Binding_lid uu___1 -> []
         | FStar_Syntax_Syntax.Binding_univ uu___1 -> []) bs
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu___ =
      let uu___1 = bound_vars_of_bindings bs in
      FStar_Compiler_List.map FStar_Syntax_Syntax.mk_binder uu___1 in
    FStar_Compiler_List.rev uu___
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1 -> binders_of_bindings env1.gamma
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1 -> bound_vars_of_bindings env1.gamma
let (hasBinders_env : env FStar_Class_Binders.hasBinders) =
  {
    FStar_Class_Binders.boundNames =
      (fun uu___ ->
         (fun e ->
            let uu___ = bound_vars e in
            Obj.magic
              (FStar_Class_Setlike.from_list ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Syntax.ord_bv)) uu___)) uu___)
  }
let (hasNames_lcomp :
  FStar_TypeChecker_Common.lcomp FStar_Class_Binders.hasNames) =
  {
    FStar_Class_Binders.freeNames =
      (fun lc ->
         let uu___ =
           let uu___1 = FStar_TypeChecker_Common.lcomp_comp lc in
           FStar_Pervasives_Native.fst uu___1 in
         FStar_Class_Binders.freeNames FStar_Class_Binders.hasNames_comp
           uu___)
  }
let (pretty_lcomp : FStar_TypeChecker_Common.lcomp FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = (fun lc -> FStar_Pprint.empty) }
let (hasNames_guard : guard_t FStar_Class_Binders.hasNames) =
  {
    FStar_Class_Binders.freeNames =
      (fun uu___ ->
         (fun g ->
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial ->
                Obj.magic
                  (Obj.repr
                     (FStar_Class_Setlike.empty ()
                        (Obj.magic
                           (FStar_Compiler_FlatSet.setlike_flat_set
                              FStar_Syntax_Syntax.ord_bv)) ()))
            | FStar_TypeChecker_Common.NonTrivial f ->
                Obj.magic
                  (Obj.repr
                     (FStar_Class_Binders.freeNames
                        FStar_Class_Binders.hasNames_term f))) uu___)
  }
let (pretty_guard : guard_t FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun g ->
         match g.FStar_TypeChecker_Common.guard_f with
         | FStar_TypeChecker_Common.Trivial ->
             FStar_Pprint.doc_of_string "Trivial"
         | FStar_TypeChecker_Common.NonTrivial f ->
             let uu___ = FStar_Pprint.doc_of_string "NonTrivial" in
             let uu___1 = FStar_Class_PP.pp FStar_Syntax_Print.pretty_term f in
             FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1)
  }
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun c ->
      FStar_Defensive.def_check_scoped hasBinders_env
        FStar_Class_Binders.hasNames_comp FStar_Syntax_Print.pretty_comp
        c.FStar_Syntax_Syntax.pos "comp_to_comp_typ" env1 c;
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Comp ct -> ct
       | uu___1 ->
           let uu___2 =
             match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total t ->
                 (FStar_Parser_Const.effect_Tot_lid, t)
             | FStar_Syntax_Syntax.GTotal t ->
                 (FStar_Parser_Const.effect_GTot_lid, t) in
           (match uu___2 with
            | (effect_name, result_typ) ->
                let uu___3 =
                  let uu___4 = env1.universe_of env1 result_typ in [uu___4] in
                {
                  FStar_Syntax_Syntax.comp_univs = uu___3;
                  FStar_Syntax_Syntax.effect_name = effect_name;
                  FStar_Syntax_Syntax.result_typ = result_typ;
                  FStar_Syntax_Syntax.effect_args = [];
                  FStar_Syntax_Syntax.flags =
                    (FStar_Syntax_Util.comp_flags c)
                }))
let (comp_set_flags :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun c ->
      fun f ->
        FStar_Defensive.def_check_scoped hasBinders_env
          FStar_Class_Binders.hasNames_comp FStar_Syntax_Print.pretty_comp
          c.FStar_Syntax_Syntax.pos "comp_set_flags.IN" env1 c;
        (let r =
           let uu___1 =
             let uu___2 =
               let uu___3 = comp_to_comp_typ env1 c in
               {
                 FStar_Syntax_Syntax.comp_univs =
                   (uu___3.FStar_Syntax_Syntax.comp_univs);
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags = f
               } in
             FStar_Syntax_Syntax.Comp uu___2 in
           {
             FStar_Syntax_Syntax.n = uu___1;
             FStar_Syntax_Syntax.pos = (c.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars = (c.FStar_Syntax_Syntax.vars);
             FStar_Syntax_Syntax.hash_code =
               (c.FStar_Syntax_Syntax.hash_code)
           } in
         FStar_Defensive.def_check_scoped hasBinders_env
           FStar_Class_Binders.hasNames_comp FStar_Syntax_Print.pretty_comp
           c.FStar_Syntax_Syntax.pos "comp_set_flags.OUT" env1 r;
         r)
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun comp ->
      FStar_Defensive.def_check_scoped hasBinders_env
        FStar_Class_Binders.hasNames_comp FStar_Syntax_Print.pretty_comp
        comp.FStar_Syntax_Syntax.pos "unfold_effect_abbrev" env1 comp;
      (let c = comp_to_comp_typ env1 comp in
       let uu___1 =
         lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
           c.FStar_Syntax_Syntax.effect_name in
       match uu___1 with
       | FStar_Pervasives_Native.None -> c
       | FStar_Pervasives_Native.Some (binders, cdef) ->
           let uu___2 = FStar_Syntax_Subst.open_comp binders cdef in
           (match uu___2 with
            | (binders1, cdef1) ->
                (if
                   (FStar_Compiler_List.length binders1) <>
                     ((FStar_Compiler_List.length
                         c.FStar_Syntax_Syntax.effect_args)
                        + Prims.int_one)
                 then
                   (let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStar_Compiler_Util.string_of_int
                            (FStar_Compiler_List.length binders1) in
                        let uu___7 =
                          FStar_Compiler_Util.string_of_int
                            ((FStar_Compiler_List.length
                                c.FStar_Syntax_Syntax.effect_args)
                               + Prims.int_one) in
                        let uu___8 =
                          let uu___9 = FStar_Syntax_Syntax.mk_Comp c in
                          FStar_Syntax_Print.comp_to_string uu___9 in
                        FStar_Compiler_Util.format3
                          "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                          uu___6 uu___7 uu___8 in
                      (FStar_Errors_Codes.Fatal_ConstructorArgLengthMismatch,
                        uu___5) in
                    FStar_Errors.raise_error uu___4
                      comp.FStar_Syntax_Syntax.pos)
                 else ();
                 (let inst =
                    let uu___4 =
                      let uu___5 =
                        FStar_Syntax_Syntax.as_arg
                          c.FStar_Syntax_Syntax.result_typ in
                      uu___5 :: (c.FStar_Syntax_Syntax.effect_args) in
                    FStar_Compiler_List.map2
                      (fun b ->
                         fun uu___5 ->
                           match uu___5 with
                           | (t, uu___6) ->
                               FStar_Syntax_Syntax.NT
                                 ((b.FStar_Syntax_Syntax.binder_bv), t))
                      binders1 uu___4 in
                  let c1 = FStar_Syntax_Subst.subst_comp inst cdef1 in
                  let c2 =
                    let uu___4 =
                      let uu___5 = comp_to_comp_typ env1 c1 in
                      {
                        FStar_Syntax_Syntax.comp_univs =
                          (uu___5.FStar_Syntax_Syntax.comp_univs);
                        FStar_Syntax_Syntax.effect_name =
                          (uu___5.FStar_Syntax_Syntax.effect_name);
                        FStar_Syntax_Syntax.result_typ =
                          (uu___5.FStar_Syntax_Syntax.result_typ);
                        FStar_Syntax_Syntax.effect_args =
                          (uu___5.FStar_Syntax_Syntax.effect_args);
                        FStar_Syntax_Syntax.flags =
                          (c.FStar_Syntax_Syntax.flags)
                      } in
                    FStar_Syntax_Syntax.mk_Comp uu___4 in
                  unfold_effect_abbrev env1 c2))))
let effect_repr_aux :
  'uuuuu .
    'uuuuu ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable ->
    fun env1 ->
      fun c ->
        fun u_res ->
          let check_partial_application eff_name args =
            let r = get_range env1 in
            let uu___ =
              let uu___1 = num_effect_indices env1 eff_name r in
              ((FStar_Compiler_List.length args), uu___1) in
            match uu___ with
            | (given, expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu___2 = FStar_Ident.string_of_lid eff_name in
                     let uu___3 = FStar_Compiler_Util.string_of_int given in
                     let uu___4 = FStar_Compiler_Util.string_of_int expected in
                     FStar_Compiler_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu___2 uu___3 uu___4 in
                   FStar_Errors.raise_error
                     (FStar_Errors_Codes.Fatal_NotEnoughArgumentsForEffect,
                       message) r) in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c) in
          let uu___ = effect_decl_opt env1 effect_name in
          match uu___ with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, uu___1) ->
              let uu___2 = FStar_Syntax_Util.get_eff_repr ed in
              (match uu___2 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             let uu___8 = FStar_Syntax_Syntax.as_arg res_typ in
                             uu___8 :: (c1.FStar_Syntax_Syntax.effect_args) in
                           {
                             FStar_Syntax_Syntax.hd = repr;
                             FStar_Syntax_Syntax.args = uu___7
                           } in
                         FStar_Syntax_Syntax.Tm_app uu___6 in
                       let uu___6 = get_range env1 in
                       FStar_Syntax_Syntax.mk uu___5 uu___6 in
                     FStar_Pervasives_Native.Some uu___4)))
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env1 -> fun c -> fun u_res -> effect_repr_aux false env1 c u_res
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env1 effect_lid in
      let quals = lookup_effect_quals env1 effect_lid1 in
      FStar_Compiler_List.contains FStar_Syntax_Syntax.Reifiable quals
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env1 effect_lid in
      let quals = lookup_effect_quals env1 effect_lid1 in
      FStar_Compiler_List.existsb
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.Reflectable uu___1 -> true
           | uu___1 -> false) quals
let (is_total_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env1 effect_lid in
      let quals = lookup_effect_quals env1 effect_lid1 in
      FStar_Compiler_List.contains FStar_Syntax_Syntax.TotalEffect quals
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env1 effect_lid in
      (is_user_reifiable_effect env1 effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env1 ->
    fun c -> is_reifiable_effect env1 c.FStar_Syntax_Syntax.residual_effect
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env1 ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env1 ct.FStar_Syntax_Syntax.effect_name
      | uu___ -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_arrow
          { FStar_Syntax_Syntax.bs1 = uu___1; FStar_Syntax_Syntax.comp = c;_}
          -> is_reifiable_comp env1 c
      | uu___1 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu___1 =
           let uu___2 = is_reifiable_effect env1 l in
           Prims.op_Negation uu___2 in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Ident.string_of_lid l in
               FStar_Compiler_Util.format1 "Effect %s cannot be reified"
                 uu___4 in
             (FStar_Errors_Codes.Fatal_EffectCannotBeReified, uu___3) in
           let uu___3 = get_range env1 in
           FStar_Errors.raise_error uu___2 uu___3
         else ());
        (let uu___1 = effect_repr_aux true env1 c u_c in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStar_Compiler_Effect.failwith
               "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let rec (record_vals_and_defns : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun g ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_declare_typ uu___ when
          FStar_Compiler_Util.for_some
            (fun uu___1 ->
               match uu___1 with
               | FStar_Syntax_Syntax.OnlyName -> true
               | uu___2 -> false) se.FStar_Syntax_Syntax.sigquals
          -> g
      | FStar_Syntax_Syntax.Sig_let uu___ when
          FStar_Compiler_Util.for_some
            (fun uu___1 ->
               match uu___1 with
               | FStar_Syntax_Syntax.OnlyName -> true
               | uu___2 -> false) se.FStar_Syntax_Syntax.sigquals
          -> g
      | FStar_Syntax_Syntax.Sig_declare_typ
          { FStar_Syntax_Syntax.lid2 = lid; FStar_Syntax_Syntax.us2 = uu___;
            FStar_Syntax_Syntax.t2 = uu___1;_}
          ->
          if
            (FStar_Compiler_List.contains FStar_Syntax_Syntax.Assumption
               se.FStar_Syntax_Syntax.sigquals)
              || g.is_iface
          then g
          else record_val_for g lid
      | FStar_Syntax_Syntax.Sig_let
          { FStar_Syntax_Syntax.lbs1 = uu___;
            FStar_Syntax_Syntax.lids1 = lids;_}
          -> FStar_Compiler_List.fold_left record_definition_for g lids
      | FStar_Syntax_Syntax.Sig_datacon
          { FStar_Syntax_Syntax.lid1 = lid; FStar_Syntax_Syntax.us1 = uu___;
            FStar_Syntax_Syntax.t1 = uu___1;
            FStar_Syntax_Syntax.ty_lid = uu___2;
            FStar_Syntax_Syntax.num_ty_params = uu___3;
            FStar_Syntax_Syntax.mutuals1 = uu___4;
            FStar_Syntax_Syntax.injective_type_params1 = uu___5;_}
          -> record_definition_for g lid
      | FStar_Syntax_Syntax.Sig_inductive_typ
          { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = uu___;
            FStar_Syntax_Syntax.params = uu___1;
            FStar_Syntax_Syntax.num_uniform_params = uu___2;
            FStar_Syntax_Syntax.t = uu___3;
            FStar_Syntax_Syntax.mutuals = uu___4;
            FStar_Syntax_Syntax.ds = uu___5;
            FStar_Syntax_Syntax.injective_type_params = uu___6;_}
          -> record_definition_for g lid
      | FStar_Syntax_Syntax.Sig_bundle
          { FStar_Syntax_Syntax.ses = ses;
            FStar_Syntax_Syntax.lids = uu___;_}
          -> FStar_Compiler_List.fold_left record_vals_and_defns g ses
      | uu___ -> g
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun force ->
    fun env1 ->
      fun s ->
        let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
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
            lax = (env1.lax);
            lax_universes = (env1.lax_universes);
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
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  push_sigelt' false
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  push_sigelt' true
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env1 ->
    fun uu___ ->
      match uu___ with
      | (ed, quals) ->
          let effects1 =
            let uu___1 = env1.effects in
            {
              decls =
                (FStar_Compiler_List.op_At (env1.effects).decls [(ed, quals)]);
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
            lax = (env1.lax);
            lax_universes = (env1.lax_universes);
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
let (exists_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * polymonadic_bind_t)
          FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun m ->
      fun n ->
        let uu___ =
          FStar_Compiler_Util.find_opt
            (fun uu___1 ->
               match uu___1 with
               | (m1, n1, uu___2, uu___3) ->
                   (FStar_Ident.lid_equals m m1) &&
                     (FStar_Ident.lid_equals n n1))
            (env1.effects).polymonadic_binds in
        match uu___ with
        | FStar_Pervasives_Native.Some (uu___1, uu___2, p, t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu___1 -> FStar_Pervasives_Native.None
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.tscheme *
          FStar_Syntax_Syntax.indexed_effect_combinator_kind)
          FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun m ->
      fun n ->
        let uu___ =
          FStar_Compiler_Util.find_opt
            (fun uu___1 ->
               match uu___1 with
               | (m1, n1, uu___2, uu___3) ->
                   (FStar_Ident.lid_equals m m1) &&
                     (FStar_Ident.lid_equals n n1))
            (env1.effects).polymonadic_subcomps in
        match uu___ with
        | FStar_Pervasives_Native.Some (uu___1, uu___2, ts, k) ->
            FStar_Pervasives_Native.Some (ts, k)
        | uu___1 -> FStar_Pervasives_Native.None
let (print_effects_graph : env -> Prims.string) =
  fun env1 ->
    let eff_name lid =
      let uu___ = FStar_Ident.ident_of_lid lid in
      FStar_Ident.string_of_id uu___ in
    let path_str path =
      let uu___ = FStar_Compiler_List.map eff_name path in
      FStar_Compiler_String.concat ";" uu___ in
    let pbinds = FStar_Compiler_Util.smap_create (Prims.of_int (10)) in
    let lifts = FStar_Compiler_Util.smap_create (Prims.of_int (20)) in
    let psubcomps = FStar_Compiler_Util.smap_create (Prims.of_int (10)) in
    FStar_Compiler_List.iter
      (fun uu___1 ->
         match uu___1 with
         | { msource = src; mtarget = tgt; mlift = uu___2; mpath = path;_} ->
             let key = eff_name src in
             let m =
               let uu___3 = FStar_Compiler_Util.smap_try_find lifts key in
               match uu___3 with
               | FStar_Pervasives_Native.None ->
                   let m1 =
                     FStar_Compiler_Util.smap_create (Prims.of_int (10)) in
                   (FStar_Compiler_Util.smap_add lifts key m1; m1)
               | FStar_Pervasives_Native.Some m1 -> m1 in
             let uu___3 =
               let uu___4 = eff_name tgt in
               FStar_Compiler_Util.smap_try_find m uu___4 in
             (match uu___3 with
              | FStar_Pervasives_Native.Some uu___4 -> ()
              | FStar_Pervasives_Native.None ->
                  let uu___4 = eff_name tgt in
                  let uu___5 = path_str path in
                  FStar_Compiler_Util.smap_add m uu___4 uu___5))
      (env1.effects).order;
    FStar_Compiler_List.iter
      (fun uu___2 ->
         match uu___2 with
         | (m, n, p, uu___3) ->
             let key =
               let uu___4 = eff_name m in
               let uu___5 = eff_name n in
               let uu___6 = eff_name p in
               FStar_Compiler_Util.format3 "%s, %s |> %s" uu___4 uu___5
                 uu___6 in
             FStar_Compiler_Util.smap_add pbinds key "")
      (env1.effects).polymonadic_binds;
    FStar_Compiler_List.iter
      (fun uu___3 ->
         match uu___3 with
         | (m, n, uu___4, uu___5) ->
             let key =
               let uu___6 = eff_name m in
               let uu___7 = eff_name n in
               FStar_Compiler_Util.format2 "%s <: %s" uu___6 uu___7 in
             FStar_Compiler_Util.smap_add psubcomps key "")
      (env1.effects).polymonadic_subcomps;
    (let uu___3 =
       let uu___4 =
         FStar_Compiler_Util.smap_fold lifts
           (fun src ->
              fun m ->
                fun s ->
                  FStar_Compiler_Util.smap_fold m
                    (fun tgt ->
                       fun path ->
                         fun s1 ->
                           let uu___5 =
                             FStar_Compiler_Util.format3
                               "%s -> %s [label=\"%s\"]" src tgt path in
                           uu___5 :: s1) s) [] in
       FStar_Compiler_String.concat "\n" uu___4 in
     let uu___4 =
       let uu___5 =
         FStar_Compiler_Util.smap_fold pbinds
           (fun k ->
              fun uu___6 ->
                fun s ->
                  let uu___7 =
                    FStar_Compiler_Util.format1
                      "\"%s\" [shape=\"plaintext\"]" k in
                  uu___7 :: s) [] in
       FStar_Compiler_String.concat "\n" uu___5 in
     let uu___5 =
       let uu___6 =
         FStar_Compiler_Util.smap_fold psubcomps
           (fun k ->
              fun uu___7 ->
                fun s ->
                  let uu___8 =
                    FStar_Compiler_Util.format1
                      "\"%s\" [shape=\"plaintext\"]" k in
                  uu___8 :: s) [] in
       FStar_Compiler_String.concat "\n" uu___6 in
     FStar_Compiler_Util.format3
       "digraph {\nlabel=\"Effects ordering\"\nsubgraph cluster_lifts {\nlabel = \"Lifts\"\n\n      %s\n}\nsubgraph cluster_polymonadic_binds {\nlabel = \"Polymonadic binds\"\n%s\n}\nsubgraph cluster_polymonadic_subcomps {\nlabel = \"Polymonadic subcomps\"\n%s\n}}\n"
       uu___3 uu___4 uu___5)
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1 ->
    fun src ->
      fun tgt ->
        fun st_mlift ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu___ = (e1.mlift).mlift_wp env2 c in
                match uu___ with
                | (c1, g1) ->
                    let uu___1 = (e2.mlift).mlift_wp env2 c1 in
                    (match uu___1 with
                     | (c2, g2) ->
                         let uu___2 =
                           FStar_TypeChecker_Common.conj_guard g1 g2 in
                         (c2, uu___2)) in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun e -> let uu___ = l1 u t e in l2 u t uu___))
                | uu___ -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift;
              mpath =
                (FStar_Compiler_List.op_At e1.mpath
                   (FStar_Compiler_List.op_At [e1.mtarget] e2.mpath))
            } in
          let edge1 =
            { msource = src; mtarget = tgt; mlift = st_mlift; mpath = [] } in
          let id_edge l =
            {
              msource = src;
              mtarget = tgt;
              mlift = identity_mlift;
              mpath = []
            } in
          let find_edge order uu___ =
            match uu___ with
            | (i, j) ->
                let uu___1 = FStar_Ident.lid_equals i j in
                if uu___1
                then FStar_Pervasives_Native.Some (id_edge i)
                else
                  FStar_Compiler_Util.find_opt
                    (fun e ->
                       (FStar_Ident.lid_equals e.msource i) &&
                         (FStar_Ident.lid_equals e.mtarget j)) order in
          let ms =
            FStar_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (e, uu___1) -> e.FStar_Syntax_Syntax.mname)
              (env1.effects).decls in
          let all_i_src =
            FStar_Compiler_List.fold_left
              (fun edges ->
                 fun i ->
                   let uu___ = FStar_Ident.lid_equals i edge1.msource in
                   if uu___
                   then edges
                   else
                     (let uu___2 =
                        find_edge (env1.effects).order (i, (edge1.msource)) in
                      match uu___2 with
                      | FStar_Pervasives_Native.Some e -> e :: edges
                      | FStar_Pervasives_Native.None -> edges)) [] ms in
          let all_tgt_j =
            FStar_Compiler_List.fold_left
              (fun edges ->
                 fun j ->
                   let uu___ = FStar_Ident.lid_equals edge1.mtarget j in
                   if uu___
                   then edges
                   else
                     (let uu___2 =
                        find_edge (env1.effects).order ((edge1.mtarget), j) in
                      match uu___2 with
                      | FStar_Pervasives_Native.Some e -> e :: edges
                      | FStar_Pervasives_Native.None -> edges)) [] ms in
          let check_cycle src1 tgt1 =
            let uu___ = FStar_Ident.lid_equals src1 tgt1 in
            if uu___
            then
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Ident.string_of_lid edge1.msource in
                  let uu___4 = FStar_Ident.string_of_lid edge1.mtarget in
                  let uu___5 = FStar_Ident.string_of_lid src1 in
                  FStar_Compiler_Util.format3
                    "Adding an edge %s~>%s induces a cycle %s" uu___3 uu___4
                    uu___5 in
                (FStar_Errors_Codes.Fatal_Effects_Ordering_Coherence, uu___2) in
              FStar_Errors.raise_error uu___1 env1.range
            else () in
          let new_i_edge_target =
            FStar_Compiler_List.fold_left
              (fun edges ->
                 fun i_src ->
                   check_cycle i_src.msource edge1.mtarget;
                   (let uu___1 = compose_edges i_src edge1 in uu___1 :: edges))
              [] all_i_src in
          let new_edge_source_j =
            FStar_Compiler_List.fold_left
              (fun edges ->
                 fun tgt_j ->
                   check_cycle edge1.msource tgt_j.mtarget;
                   (let uu___1 = compose_edges edge1 tgt_j in uu___1 :: edges))
              [] all_tgt_j in
          let new_i_j =
            FStar_Compiler_List.fold_left
              (fun edges ->
                 fun i_src ->
                   FStar_Compiler_List.fold_left
                     (fun edges1 ->
                        fun tgt_j ->
                          check_cycle i_src.msource tgt_j.mtarget;
                          (let uu___1 =
                             let uu___2 = compose_edges i_src edge1 in
                             compose_edges uu___2 tgt_j in
                           uu___1 :: edges1)) edges all_tgt_j) [] all_i_src in
          let new_edges = edge1 ::
            (FStar_Compiler_List.op_At new_i_edge_target
               (FStar_Compiler_List.op_At new_edge_source_j new_i_j)) in
          let order =
            FStar_Compiler_List.op_At new_edges (env1.effects).order in
          FStar_Compiler_List.iter
            (fun edge2 ->
               let uu___1 =
                 (FStar_Ident.lid_equals edge2.msource
                    FStar_Parser_Const.effect_DIV_lid)
                   &&
                   (let uu___2 = lookup_effect_quals env1 edge2.mtarget in
                    FStar_Compiler_List.contains
                      FStar_Syntax_Syntax.TotalEffect uu___2) in
               if uu___1
               then
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Ident.string_of_lid edge2.mtarget in
                     FStar_Compiler_Util.format1
                       "Divergent computations cannot be included in an effect %s marked 'total'"
                       uu___4 in
                   (FStar_Errors_Codes.Fatal_DivergentComputationCannotBeIncludedInTotal,
                     uu___3) in
                 let uu___3 = get_range env1 in
                 FStar_Errors.raise_error uu___2 uu___3
               else ()) order;
          (let joins =
             let ubs = FStar_Compiler_Util.smap_create (Prims.of_int (10)) in
             let add_ub i j k ik jk =
               let key =
                 let uu___1 = FStar_Ident.string_of_lid i in
                 let uu___2 =
                   let uu___3 = FStar_Ident.string_of_lid j in
                   Prims.strcat ":" uu___3 in
                 Prims.strcat uu___1 uu___2 in
               let v =
                 let uu___1 = FStar_Compiler_Util.smap_try_find ubs key in
                 match uu___1 with
                 | FStar_Pervasives_Native.Some ubs1 -> (i, j, k, ik, jk) ::
                     ubs1
                 | FStar_Pervasives_Native.None -> [(i, j, k, ik, jk)] in
               FStar_Compiler_Util.smap_add ubs key v in
             FStar_Compiler_List.iter
               (fun i ->
                  FStar_Compiler_List.iter
                    (fun j ->
                       let uu___2 = FStar_Ident.lid_equals i j in
                       if uu___2
                       then ()
                       else
                         FStar_Compiler_List.iter
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
             FStar_Compiler_Util.smap_fold ubs
               (fun s ->
                  fun l ->
                    fun joins1 ->
                      let lubs =
                        FStar_Compiler_List.filter
                          (fun uu___2 ->
                             match uu___2 with
                             | (i, j, k, ik, jk) ->
                                 FStar_Compiler_List.for_all
                                   (fun uu___3 ->
                                      match uu___3 with
                                      | (uu___4, uu___5, k', uu___6, uu___7)
                                          ->
                                          let uu___8 =
                                            find_edge order (k, k') in
                                          FStar_Compiler_Util.is_some uu___8)
                                   l) l in
                      if (FStar_Compiler_List.length lubs) <> Prims.int_one
                      then
                        let uu___2 =
                          let uu___3 =
                            FStar_Compiler_Util.format1
                              "Effects %s have incomparable upper bounds" s in
                          (FStar_Errors_Codes.Fatal_Effects_Ordering_Coherence,
                            uu___3) in
                        FStar_Errors.raise_error uu___2 env1.range
                      else FStar_Compiler_List.op_At lubs joins1) [] in
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
             lax = (env1.lax);
             lax_universes = (env1.lax_universes);
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
let (add_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Ident.lident -> polymonadic_bind_t -> env)
  =
  fun env1 ->
    fun m ->
      fun n ->
        fun p ->
          fun ty ->
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
              lax = (env1.lax);
              lax_universes = (env1.lax_universes);
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
let (add_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.tscheme *
          FStar_Syntax_Syntax.indexed_effect_combinator_kind) -> env)
  =
  fun env1 ->
    fun m ->
      fun n ->
        fun uu___ ->
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
                lax = (env1.lax);
                lax_universes = (env1.lax_universes);
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
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1 ->
    fun b ->
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
        lax = (env1.lax);
        lax_universes = (env1.lax_universes);
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
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env1 ->
    fun x -> push_local_binding env1 (FStar_Syntax_Syntax.Binding_var x)
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env1 ->
    fun bvs ->
      FStar_Compiler_List.fold_left (fun env2 -> fun bv -> push_bv env2 bv)
        env1 bvs
let (pop_bv :
  env -> (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option) =
  fun env1 ->
    match env1.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
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
              lax = (env1.lax);
              lax_universes = (env1.lax_universes);
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
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1 ->
    fun bs ->
      FStar_Compiler_List.fold_left
        (fun env2 -> fun b -> push_bv env2 b.FStar_Syntax_Syntax.binder_bv)
        env1 bs
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.binding)
  =
  fun x ->
    fun t ->
      match x with
      | FStar_Pervasives.Inl x1 ->
          let x2 =
            {
              FStar_Syntax_Syntax.ppname = (x1.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (x1.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Pervasives.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env1 ->
    fun lb -> fun ts -> push_local_binding env1 (binding_of_lb lb ts)
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env1 ->
    fun xs ->
      FStar_Compiler_List.fold_left
        (fun env2 ->
           fun x ->
             push_local_binding env2 (FStar_Syntax_Syntax.Binding_univ x))
        env1 xs
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list))
  =
  fun env1 ->
    fun uvs ->
      fun terms ->
        let uu___ = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu___ with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env1 univ_vars in
            let uu___1 =
              FStar_Compiler_List.map (FStar_Syntax_Subst.subst univ_subst)
                terms in
            (env', univ_vars, uu___1)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1 ->
    fun t ->
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
        lax = (env1.lax);
        lax_universes = (env1.lax_universes);
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
let (set_expected_typ_maybe_eq :
  env -> FStar_Syntax_Syntax.typ -> Prims.bool -> env) =
  fun env1 ->
    fun t ->
      fun use_eq ->
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
          lax = (env1.lax);
          lax_universes = (env1.lax_universes);
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
let (expected_typ :
  env ->
    (FStar_Syntax_Syntax.typ * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    match env1.expected_typ with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let (clear_expected_typ :
  env ->
    (env * (FStar_Syntax_Syntax.typ * Prims.bool)
      FStar_Pervasives_Native.option))
  =
  fun env_ ->
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
       lax = (env_.lax);
       lax_universes = (env_.lax_universes);
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
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu___ = let uu___1 = FStar_Ident.id_of_text "" in [uu___1] in
    FStar_Ident.lid_of_ids uu___ in
  fun env1 ->
    fun m ->
      let sigs =
        let uu___ =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu___
        then
          let uu___1 =
            FStar_Compiler_List.map FStar_Pervasives_Native.snd
              env1.gamma_sig in
          FStar_Compiler_List.rev uu___1
        else m.FStar_Syntax_Syntax.declarations in
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
        lax = (env1.lax);
        lax_universes = (env1.lax_universes);
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
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1 ->
    let no_uvs =
      Obj.magic
        (FStar_Class_Setlike.empty ()
           (Obj.magic
              (FStar_Compiler_FlatSet.setlike_flat_set
                 FStar_Syntax_Free.ord_ctx_uvar)) ()) in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu___)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.uvars t in
            Obj.magic
              (FStar_Class_Setlike.union ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Free.ord_ctx_uvar)) (Obj.magic out)
                 (Obj.magic uu___3)) in
          aux uu___2 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.uvars t in
            Obj.magic
              (FStar_Class_Setlike.union ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Free.ord_ctx_uvar)) (Obj.magic out)
                 (Obj.magic uu___3)) in
          aux uu___2 tl in
    aux no_uvs env1.gamma
let (univ_vars :
  env -> FStar_Syntax_Syntax.universe_uvar FStar_Compiler_FlatSet.t) =
  fun env1 ->
    let no_univs =
      Obj.magic
        (FStar_Class_Setlike.empty ()
           (Obj.magic
              (FStar_Compiler_FlatSet.setlike_flat_set
                 FStar_Syntax_Free.ord_univ_uvar)) ()) in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu___)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univs t in
            Obj.magic
              (FStar_Class_Setlike.union ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Free.ord_univ_uvar)) (Obj.magic out)
                 (Obj.magic uu___3)) in
          aux uu___2 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univs t in
            Obj.magic
              (FStar_Class_Setlike.union ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Free.ord_univ_uvar)) (Obj.magic out)
                 (Obj.magic uu___3)) in
          aux uu___2 tl in
    aux no_univs env1.gamma
let (univnames :
  env -> FStar_Syntax_Syntax.univ_name FStar_Compiler_FlatSet.t) =
  fun env1 ->
    let no_univ_names =
      Obj.magic
        (FStar_Class_Setlike.empty ()
           (Obj.magic
              (FStar_Compiler_FlatSet.setlike_flat_set
                 FStar_Syntax_Syntax.ord_ident)) ()) in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu___ =
            Obj.magic
              (FStar_Class_Setlike.add ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Syntax.ord_ident)) uname (Obj.magic out)) in
          aux uu___ tl
      | (FStar_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univnames t in
            Obj.magic
              (FStar_Class_Setlike.union ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Syntax.ord_ident)) (Obj.magic out)
                 (Obj.magic uu___3)) in
          aux uu___2 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univnames t in
            Obj.magic
              (FStar_Class_Setlike.union ()
                 (Obj.magic
                    (FStar_Compiler_FlatSet.setlike_flat_set
                       FStar_Syntax_Syntax.ord_ident)) (Obj.magic out)
                 (Obj.magic uu___3)) in
          aux uu___2 tl in
    aux no_univ_names env1.gamma
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    let keys =
      FStar_Compiler_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
    FStar_Compiler_Util.smap_fold (sigtab env1)
      (fun uu___ ->
         fun v ->
           fun keys1 ->
             FStar_Compiler_List.op_At (FStar_Syntax_Util.lids_of_sigelt v)
               keys1) keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1 ->
    fun path ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([], uu___) -> true
        | (x::xs1, y::ys1) ->
            ((FStar_Compiler_String.lowercase x) =
               (FStar_Compiler_String.lowercase y))
              && (str_i_prefix xs1 ys1)
        | (uu___, uu___1) -> false in
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with | (p, uu___2) -> str_i_prefix p path)
          env1.proof_ns in
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu___1, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu___ = FStar_Ident.path_of_lid lid in should_enc_path env1 uu___
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
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
          lax = (e.lax);
          lax_universes = (e.lax_universes);
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
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
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
        lax = (e.lax);
        lax_universes = (e.lax_universes);
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
let (unbound_vars :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.t)
  =
  fun e ->
    fun t ->
      let uu___ = FStar_Syntax_Free.names t in
      let uu___1 = bound_vars e in
      FStar_Compiler_List.fold_left
        (fun uu___3 ->
           fun uu___2 ->
             (fun s ->
                fun bv ->
                  Obj.magic
                    (FStar_Class_Setlike.remove ()
                       (Obj.magic
                          (FStar_Compiler_FlatSet.setlike_flat_set
                             FStar_Syntax_Syntax.ord_bv)) bv (Obj.magic s)))
               uu___3 uu___2) uu___ uu___1
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu___ = unbound_vars e t in
      FStar_Class_Setlike.is_empty ()
        (Obj.magic
           (FStar_Compiler_FlatSet.setlike_flat_set
              FStar_Syntax_Syntax.ord_bv)) (Obj.magic uu___)
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Free.names t in
    FStar_Class_Setlike.is_empty ()
      (Obj.magic
         (FStar_Compiler_FlatSet.setlike_flat_set FStar_Syntax_Syntax.ord_bv))
      (Obj.magic uu___)
let (string_of_proof_ns : env -> Prims.string) =
  fun env1 ->
    let aux uu___ =
      match uu___ with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu___2 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu___2) in
    let uu___ =
      let uu___1 = FStar_Compiler_List.map aux env1.proof_ns in
      FStar_Compiler_List.rev uu___1 in
    FStar_Compiler_String.concat " " uu___
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g ->
    {
      FStar_TypeChecker_Common.guard_f = g;
      FStar_TypeChecker_Common.deferred_to_tac = [];
      FStar_TypeChecker_Common.deferred = [];
      FStar_TypeChecker_Common.univ_ineqs = ([], []);
      FStar_TypeChecker_Common.implicits = []
    }
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g -> g.FStar_TypeChecker_Common.guard_f
let (is_trivial : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial;
        FStar_TypeChecker_Common.deferred_to_tac = uu___;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([], []);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_Compiler_Util.for_all
          (fun imp ->
             (let uu___1 =
                FStar_Syntax_Util.ctx_uvar_should_check
                  imp.FStar_TypeChecker_Common.imp_uvar in
              FStar_Syntax_Syntax.uu___is_Allow_unresolved uu___1) ||
               (let uu___1 =
                  FStar_Syntax_Unionfind.find
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                match uu___1 with
                | FStar_Pervasives_Native.Some uu___2 -> true
                | FStar_Pervasives_Native.None -> false)) i
    | uu___ -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial;
        FStar_TypeChecker_Common.deferred_to_tac = uu___;
        FStar_TypeChecker_Common.deferred = uu___1;
        FStar_TypeChecker_Common.univ_ineqs = uu___2;
        FStar_TypeChecker_Common.implicits = uu___3;_} -> true
    | uu___ -> false
let (trivial_guard : guard_t) = FStar_TypeChecker_Common.trivial_guard
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs ->
    fun g ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (g.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (g.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (g.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (g.FStar_TypeChecker_Common.implicits)
          }
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b -> fun g -> abstract_guard_n [b] g
let (too_early_in_prims : env -> Prims.bool) =
  fun env1 ->
    let uu___ = lid_exists env1 FStar_Parser_Const.effect_GTot_lid in
    Prims.op_Negation uu___
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g ->
    fun e ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Syntax_Syntax.as_arg e in [uu___5] in
                  {
                    FStar_Syntax_Syntax.hd = f;
                    FStar_Syntax_Syntax.args = uu___4
                  } in
                FStar_Syntax_Syntax.Tm_app uu___3 in
              FStar_Syntax_Syntax.mk uu___2 f.FStar_Syntax_Syntax.pos in
            FStar_TypeChecker_Common.NonTrivial uu___1 in
          {
            FStar_TypeChecker_Common.guard_f = uu___;
            FStar_TypeChecker_Common.deferred_to_tac =
              (g.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (g.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (g.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (g.FStar_TypeChecker_Common.implicits)
          }
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___ =
            let uu___1 = map f in FStar_TypeChecker_Common.NonTrivial uu___1 in
          {
            FStar_TypeChecker_Common.guard_f = uu___;
            FStar_TypeChecker_Common.deferred_to_tac =
              (g.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (g.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (g.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (g.FStar_TypeChecker_Common.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___ =
            let uu___1 = map FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu___1 in
          {
            FStar_TypeChecker_Common.guard_f = uu___;
            FStar_TypeChecker_Common.deferred_to_tac =
              (g.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (g.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (g.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (g.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___ =
            let uu___1 = map f in FStar_TypeChecker_Common.NonTrivial uu___1 in
          {
            FStar_TypeChecker_Common.guard_f = uu___;
            FStar_TypeChecker_Common.deferred_to_tac =
              (g.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (g.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (g.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (g.FStar_TypeChecker_Common.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu___ ->
        FStar_Compiler_Effect.failwith "impossible"
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t -> FStar_TypeChecker_Common.check_trivial t
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> FStar_TypeChecker_Common.conj_guard g1 g2
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs -> FStar_TypeChecker_Common.conj_guards gs
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> FStar_TypeChecker_Common.imp_guard g1 g2
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us ->
    fun bs ->
      fun g ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_Compiler_List.fold_right2
                (fun u ->
                   fun b ->
                     fun f2 ->
                       let uu___ = FStar_Syntax_Syntax.is_null_binder b in
                       if uu___
                       then f2
                       else
                         FStar_Syntax_Util.mk_forall u
                           b.FStar_Syntax_Syntax.binder_bv f2) us bs f in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (g.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (g.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (g.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (g.FStar_TypeChecker_Common.implicits)
            }
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun bs ->
      fun f ->
        FStar_Errors.with_ctx "While closing a formula"
          (fun uu___ ->
             (let uu___2 =
                let uu___3 = FStar_Syntax_Syntax.mk_Total f in
                FStar_Syntax_Util.arrow bs uu___3 in
              FStar_Defensive.def_check_scoped hasBinders_env
                FStar_Class_Binders.hasNames_term
                FStar_Syntax_Print.pretty_term f.FStar_Syntax_Syntax.pos
                "close_forall" env1 uu___2);
             (let bvs =
                FStar_Compiler_List.map
                  (fun b -> b.FStar_Syntax_Syntax.binder_bv) bs in
              let env_full = push_bvs env1 bvs in
              let uu___2 =
                FStar_Compiler_List.fold_right
                  (fun bv ->
                     fun uu___3 ->
                       match uu___3 with
                       | (f1, e) ->
                           let e' =
                             let uu___4 =
                               let uu___5 = pop_bv e in
                               FStar_Compiler_Util.must uu___5 in
                             FStar_Pervasives_Native.snd uu___4 in
                           (FStar_Defensive.def_check_scoped hasBinders_env
                              FStar_Class_Binders.hasNames_term
                              FStar_Syntax_Print.pretty_term
                              FStar_Compiler_Range_Type.dummyRange
                              "close_forall.sort" e'
                              bv.FStar_Syntax_Syntax.sort;
                            (let f' =
                               let uu___5 = FStar_Syntax_Syntax.is_null_bv bv in
                               if uu___5
                               then f1
                               else
                                 (let u =
                                    e'.universe_of e'
                                      bv.FStar_Syntax_Syntax.sort in
                                  FStar_Syntax_Util.mk_forall u bv f1) in
                             (f', e')))) bvs (f, env_full) in
              match uu___2 with | (f', e) -> f'))
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env1 ->
    fun binders ->
      fun g ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___ =
              let uu___1 = close_forall env1 binders f in
              FStar_TypeChecker_Common.NonTrivial uu___1 in
            {
              FStar_TypeChecker_Common.guard_f = uu___;
              FStar_TypeChecker_Common.deferred_to_tac =
                (g.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (g.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (g.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (g.FStar_TypeChecker_Common.implicits)
            }
let (new_tac_implicit_var :
  Prims.string ->
    FStar_Compiler_Range_Type.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            FStar_Syntax_Syntax.ctx_uvar Prims.list ->
              FStar_Syntax_Syntax.ctx_uvar_meta_t
                FStar_Pervasives_Native.option ->
                (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
                  FStar_Compiler_Range_Type.range) Prims.list * guard_t))
  =
  fun reason ->
    fun r ->
      fun env1 ->
        fun k ->
          fun should_check ->
            fun uvar_typedness_deps ->
              fun meta ->
                let binders = all_binders env1 in
                let gamma = env1.gamma in
                let decoration =
                  {
                    FStar_Syntax_Syntax.uvar_decoration_typ = k;
                    FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on
                      = uvar_typedness_deps;
                    FStar_Syntax_Syntax.uvar_decoration_should_check =
                      should_check
                  } in
                let ctx_uvar =
                  let uu___ = FStar_Syntax_Unionfind.fresh decoration r in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu___;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_range = r;
                    FStar_Syntax_Syntax.ctx_uvar_meta = meta
                  } in
                FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                  true gamma binders;
                (let t =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uvar
                        (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange))) r in
                 let imp =
                   {
                     FStar_TypeChecker_Common.imp_reason = reason;
                     FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                     FStar_TypeChecker_Common.imp_tm = t;
                     FStar_TypeChecker_Common.imp_range = r
                   } in
                 (let uu___2 =
                    FStar_Compiler_Effect.op_Bang dbg_ImplicitTrace in
                  if uu___2
                  then
                    let uu___3 =
                      FStar_Syntax_Print.uvar_to_string
                        ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                    FStar_Compiler_Util.print1
                      "Just created uvar for implicit {%s}\n" uu___3
                  else ());
                 (let g =
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (trivial_guard.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac =
                        (trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                      FStar_TypeChecker_Common.deferred =
                        (trivial_guard.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = [imp]
                    } in
                  (t, [(ctx_uvar, r)], g)))
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Compiler_Range_Type.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            FStar_Syntax_Syntax.ctx_uvar_meta_t
              FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
                FStar_Compiler_Range_Type.range) Prims.list * guard_t))
  =
  fun reason ->
    fun r ->
      fun env1 ->
        fun k ->
          fun should_check ->
            fun meta ->
              new_tac_implicit_var reason r env1 k should_check [] meta
let (uvars_for_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.subst_t ->
        (FStar_Syntax_Syntax.binder -> Prims.string) ->
          FStar_Compiler_Range_Type.range ->
            (FStar_Syntax_Syntax.term Prims.list * guard_t))
  =
  fun env1 ->
    fun bs ->
      fun substs ->
        fun reason ->
          fun r ->
            let uu___ =
              FStar_Compiler_List.fold_left
                (fun uu___1 ->
                   fun b ->
                     match uu___1 with
                     | (substs1, uvars, g) ->
                         let sort =
                           FStar_Syntax_Subst.subst substs1
                             (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                         let ctx_uvar_meta_t =
                           match ((b.FStar_Syntax_Syntax.binder_qual),
                                   (b.FStar_Syntax_Syntax.binder_attrs))
                           with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta t), []) ->
                               FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Ctx_uvar_meta_tac t)
                           | (uu___2, t::uu___3) ->
                               FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Ctx_uvar_meta_attr t)
                           | uu___2 -> FStar_Pervasives_Native.None in
                         let uu___2 =
                           let uu___3 = reason b in
                           let uu___4 =
                             let uu___5 =
                               FStar_Options.compat_pre_typed_indexed_effects
                                 () in
                             if uu___5
                             then
                               FStar_Syntax_Syntax.Allow_untyped
                                 "indexed effect uvar in compat mode"
                             else FStar_Syntax_Syntax.Strict in
                           new_implicit_var_aux uu___3 r env1 sort uu___4
                             ctx_uvar_meta_t in
                         (match uu___2 with
                          | (t, l_ctx_uvars, g_t) ->
                              ((let uu___4 =
                                  FStar_Compiler_Effect.op_Bang
                                    dbg_LayeredEffectsEqns in
                                if uu___4
                                then
                                  FStar_Compiler_List.iter
                                    (fun uu___5 ->
                                       match uu___5 with
                                       | (ctx_uvar, uu___6) ->
                                           let uu___7 =
                                             FStar_Syntax_Print.ctx_uvar_to_string
                                               ctx_uvar in
                                           FStar_Compiler_Util.print1
                                             "Layered Effect uvar : %s\n"
                                             uu___7) l_ctx_uvars
                                else ());
                               (let uu___4 = conj_guards [g; g_t] in
                                ((FStar_Compiler_List.op_At substs1
                                    [FStar_Syntax_Syntax.NT
                                       ((b.FStar_Syntax_Syntax.binder_bv), t)]),
                                  (FStar_Compiler_List.op_At uvars [t]),
                                  uu___4))))) (substs, [], trivial_guard) bs in
            match uu___ with | (uu___1, uvars, g) -> (uvars, g)
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Compiler_Range_Type.range -> FStar_Syntax_Syntax.typ)
  =
  fun env1 ->
    fun u ->
      fun t ->
        fun wp ->
          fun r ->
            let trivial_post =
              let post_ts =
                let uu___ =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid in
                FStar_Compiler_Util.must uu___ in
              let uu___ = inst_tscheme_with post_ts [u] in
              match uu___ with
              | (uu___1, post) ->
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Syntax.as_arg t in [uu___3] in
                  FStar_Syntax_Syntax.mk_Tm_app post uu___2 r in
            let uu___ =
              let uu___1 = FStar_Syntax_Syntax.as_arg trivial_post in
              [uu___1] in
            FStar_Syntax_Syntax.mk_Tm_app wp uu___ r
let (get_letrec_arity :
  env ->
    FStar_Syntax_Syntax.lbname -> Prims.int FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lbname ->
      let compare_either f1 f2 e1 e2 =
        match (e1, e2) with
        | (FStar_Pervasives.Inl v1, FStar_Pervasives.Inl v2) -> f1 v1 v2
        | (FStar_Pervasives.Inr v1, FStar_Pervasives.Inr v2) -> f2 v1 v2
        | uu___ -> false in
      let uu___ =
        FStar_Compiler_Util.find_opt
          (fun uu___1 ->
             match uu___1 with
             | (lbname', uu___2, uu___3, uu___4) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
      match uu___ with
      | FStar_Pervasives_Native.Some (uu___1, arity, uu___2, uu___3) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (fvar_of_nonqual_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun lid ->
      let qn = lookup_qname env1 lid in
      FStar_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None
let (split_smt_query :
  env ->
    FStar_Syntax_Syntax.term ->
      (env * FStar_Syntax_Syntax.term) Prims.list
        FStar_Pervasives_Native.option)
  =
  fun e ->
    fun q ->
      match (e.solver).spinoff_strictly_positive_goals with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some p ->
          let uu___ = p e q in FStar_Pervasives_Native.Some uu___