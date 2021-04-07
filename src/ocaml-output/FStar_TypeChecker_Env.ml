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
type steps = step Prims.list
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
      | (Exclude s11, Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11, UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1, UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1, UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr lids1, UnfoldAttr lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | uu___ -> false
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
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Pervasives.either * FStar_Range.range)
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
  mlift: mlift }
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
                 FStar_Range.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list
    ;
  polymonadic_subcomps:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
      Prims.list
    }
and env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStar_Syntax_Syntax.lbname * Prims.int * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  use_eq_strict: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  nosynth: Prims.bool ;
  uvar_subtyping: Prims.bool ;
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
  use_bv_sorts: Prims.bool ;
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option)
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Util.smap ;
  fv_delta_depths: FStar_Syntax_Syntax.delta_depth FStar_Util.smap ;
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
      FStar_Range.range ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list
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
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  strict_args_tab:
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap ;
  erasable_types_tab: Prims.bool FStar_Util.smap ;
  enable_defer_to_tac: Prims.bool ;
  unif_allow_ref_guards: Prims.bool }
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
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list ;
  solve:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit
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
    match projectee with | { msource; mtarget; mlift = mlift1;_} -> msource
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with | { msource; mtarget; mlift = mlift1;_} -> mtarget
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee ->
    match projectee with | { msource; mtarget; mlift = mlift1;_} -> mlift1
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
                 FStar_Range.range ->
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
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
      Prims.list)
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        solver
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        range
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        curmodule
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        gamma
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        gamma_sig
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        gamma_cache
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        modules
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        expected_typ
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        sigtab
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        attrtab
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        instantiate_imp
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        effects1
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        generalize
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * Prims.int * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        letrecs
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        top_level
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        check_uvars
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        use_eq
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        use_eq_strict
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        is_iface
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        admit
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        lax
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        lax_universes
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        phase1
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        failhard
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        nosynth
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        uvar_subtyping
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        tc_term
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        typeof_tot_or_gtot_term
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        universe_of
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        typeof_well_typed_tot_or_gtot_term
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        use_bv_sorts
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        qtbl_name_and_index
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        normalized_eff_names
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        fv_delta_depths
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        proof_ns
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        synth_hook
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        try_solve_implicits_hook
let (__proj__Mkenv__item__splice :
  env ->
    env ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        splice
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        mpreprocess
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
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        postprocess
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        identifier_info
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        tc_hooks
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        dsenv
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        nbe
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        strict_args_tab
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        erasable_types_tab
let (__proj__Mkenv__item__enable_defer_to_tac : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        enable_defer_to_tac
let (__proj__Mkenv__item__unif_allow_ref_guards : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; typeof_tot_or_gtot_term; universe_of;
        typeof_well_typed_tot_or_gtot_term; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice; mpreprocess;
        postprocess; identifier_info; tc_hooks; dsenv; nbe; strict_args_tab;
        erasable_types_tab; enable_defer_to_tac; unif_allow_ref_guards;_} ->
        unif_allow_ref_guards
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> init
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> push
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> pop
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> snapshot
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> rollback
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> encode_sig
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> preprocess
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> solve
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> finish
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> refresh
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
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicit = FStar_TypeChecker_Common.implicit
type implicits = FStar_TypeChecker_Common.implicits
type guard_t = FStar_TypeChecker_Common.guard_t
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
      FStar_All.pipe_right gamma
        (FStar_List.map
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
                         let uu___3 = y1 in
                         let uu___4 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___3.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___3.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu___4
                         } in
                       FStar_Syntax_Syntax.Binding_var uu___2
                   | uu___2 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst ->
    fun env1 ->
      let uu___ = env1 in
      let uu___1 = rename_gamma subst env1.gamma in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = (uu___.curmodule);
        gamma = uu___1;
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (uu___.expected_typ);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = (uu___.use_eq);
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = (uu___.proof_ns);
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = (uu___.tc_hooks);
        dsenv = (uu___.dsenv);
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu___ -> fun uu___1 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env1 -> env1.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___ = env1 in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = (uu___.curmodule);
        gamma = (uu___.gamma);
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (uu___.expected_typ);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = (uu___.use_eq);
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = (uu___.proof_ns);
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___.dsenv);
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___ = e in
      let uu___1 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = (uu___.curmodule);
        gamma = (uu___.gamma);
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (uu___.expected_typ);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = (uu___.use_eq);
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = (uu___.proof_ns);
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = (uu___.tc_hooks);
        dsenv = uu___1;
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e -> FStar_Syntax_DsEnv.dep_graph e.dsenv
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
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
let new_sigtab : 'uuuuu . unit -> 'uuuuu FStar_Util.smap =
  fun uu___ -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'uuuuu . unit -> 'uuuuu FStar_Util.smap =
  fun uu___ -> FStar_Util.smap_create (Prims.of_int (100))
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
            solver_t ->
              FStar_Ident.lident ->
                (step Prims.list ->
                   env ->
                     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
                  -> env)
  =
  fun deps ->
    fun tc_term ->
      fun typeof_tot_or_gtot_term ->
        fun typeof_tot_or_gtot_term_fastpath ->
          fun universe_of ->
            fun solver ->
              fun module_lid ->
                fun nbe ->
                  let uu___ = new_gamma_cache () in
                  let uu___1 = new_sigtab () in
                  let uu___2 = new_sigtab () in
                  let uu___3 =
                    let uu___4 = FStar_Util.smap_create (Prims.of_int (10)) in
                    (uu___4, FStar_Pervasives_Native.None) in
                  let uu___4 = FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu___5 = FStar_Util.smap_create (Prims.of_int (50)) in
                  let uu___6 = FStar_Options.using_facts_from () in
                  let uu___7 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty in
                  let uu___8 = FStar_Syntax_DsEnv.empty_env deps in
                  let uu___9 = FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu___10 = FStar_Util.smap_create (Prims.of_int (20)) in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
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
                    use_eq = false;
                    use_eq_strict = false;
                    is_iface = false;
                    admit = false;
                    lax = false;
                    lax_universes = false;
                    phase1 = false;
                    failhard = false;
                    nosynth = false;
                    uvar_subtyping = true;
                    tc_term;
                    typeof_tot_or_gtot_term;
                    universe_of;
                    typeof_well_typed_tot_or_gtot_term =
                      (fun env1 ->
                         fun t ->
                           fun must_tot1 ->
                             let uu___11 =
                               typeof_tot_or_gtot_term_fastpath env1 t
                                 must_tot1 in
                             match uu___11 with
                             | FStar_Pervasives_Native.Some k ->
                                 (k, FStar_TypeChecker_Common.trivial_guard)
                             | FStar_Pervasives_Native.None ->
                                 let uu___12 =
                                   typeof_tot_or_gtot_term env1 t must_tot1 in
                                 (match uu___12 with
                                  | (uu___13, k, g) -> (k, g)));
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu___3;
                    normalized_eff_names = uu___4;
                    fv_delta_depths = uu___5;
                    proof_ns = uu___6;
                    synth_hook =
                      (fun e ->
                         fun g ->
                           fun tau -> failwith "no synthesizer available");
                    try_solve_implicits_hook =
                      (fun e ->
                         fun tau ->
                           fun imps -> failwith "no implicit hook available");
                    splice =
                      (fun e ->
                         fun rng ->
                           fun tau -> failwith "no splicer available");
                    mpreprocess =
                      (fun e ->
                         fun tau ->
                           fun tm -> failwith "no preprocessor available");
                    postprocess =
                      (fun e ->
                         fun tau ->
                           fun typ ->
                             fun tm -> failwith "no postprocessor available");
                    identifier_info = uu___7;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu___8;
                    nbe;
                    strict_args_tab = uu___9;
                    erasable_types_tab = uu___10;
                    enable_defer_to_tac = true;
                    unif_allow_ref_guards = false
                  }
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env1 -> env1.dsenv
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env1 -> env1.sigtab
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env1 -> env1.attrtab
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env1 -> env1.gamma_cache
let (query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]]
let (push_query_indices : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang query_indices in
    match uu___1 with
    | [] -> failwith "Empty query indices!"
    | uu___2 ->
        let uu___3 =
          let uu___4 =
            let uu___5 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu___5 in
          let uu___5 = FStar_ST.op_Bang query_indices in uu___4 :: uu___5 in
        FStar_ST.op_Colon_Equals query_indices uu___3
let (pop_query_indices : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang query_indices in
    match uu___1 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu___ -> FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu___ ->
    match uu___ with
    | (l, n) ->
        let uu___1 = FStar_ST.op_Bang query_indices in
        (match uu___1 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu___2 -> failwith "Empty query indices")
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang query_indices in FStar_List.hd uu___1
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env1 ->
    (let uu___1 = let uu___2 = FStar_ST.op_Bang stack in env1 :: uu___2 in
     FStar_ST.op_Colon_Equals stack uu___1);
    (let uu___1 = env1 in
     let uu___2 = FStar_Util.smap_copy (gamma_cache env1) in
     let uu___3 = FStar_Util.smap_copy (sigtab env1) in
     let uu___4 = FStar_Util.smap_copy (attrtab env1) in
     let uu___5 =
       let uu___6 =
         let uu___7 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu___7 in
       let uu___7 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu___6, uu___7) in
     let uu___6 = FStar_Util.smap_copy env1.normalized_eff_names in
     let uu___7 = FStar_Util.smap_copy env1.fv_delta_depths in
     let uu___8 =
       let uu___9 = FStar_ST.op_Bang env1.identifier_info in
       FStar_Util.mk_ref uu___9 in
     let uu___9 = FStar_Util.smap_copy env1.strict_args_tab in
     let uu___10 = FStar_Util.smap_copy env1.erasable_types_tab in
     {
       solver = (uu___1.solver);
       range = (uu___1.range);
       curmodule = (uu___1.curmodule);
       gamma = (uu___1.gamma);
       gamma_sig = (uu___1.gamma_sig);
       gamma_cache = uu___2;
       modules = (uu___1.modules);
       expected_typ = (uu___1.expected_typ);
       sigtab = uu___3;
       attrtab = uu___4;
       instantiate_imp = (uu___1.instantiate_imp);
       effects = (uu___1.effects);
       generalize = (uu___1.generalize);
       letrecs = (uu___1.letrecs);
       top_level = (uu___1.top_level);
       check_uvars = (uu___1.check_uvars);
       use_eq = (uu___1.use_eq);
       use_eq_strict = (uu___1.use_eq_strict);
       is_iface = (uu___1.is_iface);
       admit = (uu___1.admit);
       lax = (uu___1.lax);
       lax_universes = (uu___1.lax_universes);
       phase1 = (uu___1.phase1);
       failhard = (uu___1.failhard);
       nosynth = (uu___1.nosynth);
       uvar_subtyping = (uu___1.uvar_subtyping);
       tc_term = (uu___1.tc_term);
       typeof_tot_or_gtot_term = (uu___1.typeof_tot_or_gtot_term);
       universe_of = (uu___1.universe_of);
       typeof_well_typed_tot_or_gtot_term =
         (uu___1.typeof_well_typed_tot_or_gtot_term);
       use_bv_sorts = (uu___1.use_bv_sorts);
       qtbl_name_and_index = uu___5;
       normalized_eff_names = uu___6;
       fv_delta_depths = uu___7;
       proof_ns = (uu___1.proof_ns);
       synth_hook = (uu___1.synth_hook);
       try_solve_implicits_hook = (uu___1.try_solve_implicits_hook);
       splice = (uu___1.splice);
       mpreprocess = (uu___1.mpreprocess);
       postprocess = (uu___1.postprocess);
       identifier_info = uu___8;
       tc_hooks = (uu___1.tc_hooks);
       dsenv = (uu___1.dsenv);
       nbe = (uu___1.nbe);
       strict_args_tab = uu___9;
       erasable_types_tab = uu___10;
       enable_defer_to_tac = (uu___1.enable_defer_to_tac);
       unif_allow_ref_guards = (uu___1.unif_allow_ref_guards)
     })
let (pop_stack : unit -> env) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang stack in
    match uu___1 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu___2 -> failwith "Impossible: Too many pops"
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push_stack stack env1
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop_stack stack depth
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1 ->
    fun msg ->
      FStar_Util.atomically
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
                                (let uu___5 = env2 in
                                 {
                                   solver = (uu___5.solver);
                                   range = (uu___5.range);
                                   curmodule = (uu___5.curmodule);
                                   gamma = (uu___5.gamma);
                                   gamma_sig = (uu___5.gamma_sig);
                                   gamma_cache = (uu___5.gamma_cache);
                                   modules = (uu___5.modules);
                                   expected_typ = (uu___5.expected_typ);
                                   sigtab = (uu___5.sigtab);
                                   attrtab = (uu___5.attrtab);
                                   instantiate_imp = (uu___5.instantiate_imp);
                                   effects = (uu___5.effects);
                                   generalize = (uu___5.generalize);
                                   letrecs = (uu___5.letrecs);
                                   top_level = (uu___5.top_level);
                                   check_uvars = (uu___5.check_uvars);
                                   use_eq = (uu___5.use_eq);
                                   use_eq_strict = (uu___5.use_eq_strict);
                                   is_iface = (uu___5.is_iface);
                                   admit = (uu___5.admit);
                                   lax = (uu___5.lax);
                                   lax_universes = (uu___5.lax_universes);
                                   phase1 = (uu___5.phase1);
                                   failhard = (uu___5.failhard);
                                   nosynth = (uu___5.nosynth);
                                   uvar_subtyping = (uu___5.uvar_subtyping);
                                   tc_term = (uu___5.tc_term);
                                   typeof_tot_or_gtot_term =
                                     (uu___5.typeof_tot_or_gtot_term);
                                   universe_of = (uu___5.universe_of);
                                   typeof_well_typed_tot_or_gtot_term =
                                     (uu___5.typeof_well_typed_tot_or_gtot_term);
                                   use_bv_sorts = (uu___5.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___5.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___5.normalized_eff_names);
                                   fv_delta_depths = (uu___5.fv_delta_depths);
                                   proof_ns = (uu___5.proof_ns);
                                   synth_hook = (uu___5.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___5.try_solve_implicits_hook);
                                   splice = (uu___5.splice);
                                   mpreprocess = (uu___5.mpreprocess);
                                   postprocess = (uu___5.postprocess);
                                   identifier_info = (uu___5.identifier_info);
                                   tc_hooks = (uu___5.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___5.nbe);
                                   strict_args_tab = (uu___5.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___5.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___5.enable_defer_to_tac);
                                   unif_allow_ref_guards =
                                     (uu___5.unif_allow_ref_guards)
                                 }))))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
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
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1 in
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
    | (uu___, FStar_Pervasives_Native.None) -> env1
    | (tbl, FStar_Pervasives_Native.Some (l, n)) ->
        let uu___ =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu___1 ->
                  match uu___1 with
                  | (m, uu___2) -> FStar_Ident.lid_equals l m)) in
        (match uu___ with
         | FStar_Pervasives_Native.None ->
             let next = n + Prims.int_one in
             (add_query_index (l, next);
              (let uu___3 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu___3 next);
              (let uu___3 = env1 in
               {
                 solver = (uu___3.solver);
                 range = (uu___3.range);
                 curmodule = (uu___3.curmodule);
                 gamma = (uu___3.gamma);
                 gamma_sig = (uu___3.gamma_sig);
                 gamma_cache = (uu___3.gamma_cache);
                 modules = (uu___3.modules);
                 expected_typ = (uu___3.expected_typ);
                 sigtab = (uu___3.sigtab);
                 attrtab = (uu___3.attrtab);
                 instantiate_imp = (uu___3.instantiate_imp);
                 effects = (uu___3.effects);
                 generalize = (uu___3.generalize);
                 letrecs = (uu___3.letrecs);
                 top_level = (uu___3.top_level);
                 check_uvars = (uu___3.check_uvars);
                 use_eq = (uu___3.use_eq);
                 use_eq_strict = (uu___3.use_eq_strict);
                 is_iface = (uu___3.is_iface);
                 admit = (uu___3.admit);
                 lax = (uu___3.lax);
                 lax_universes = (uu___3.lax_universes);
                 phase1 = (uu___3.phase1);
                 failhard = (uu___3.failhard);
                 nosynth = (uu___3.nosynth);
                 uvar_subtyping = (uu___3.uvar_subtyping);
                 tc_term = (uu___3.tc_term);
                 typeof_tot_or_gtot_term = (uu___3.typeof_tot_or_gtot_term);
                 universe_of = (uu___3.universe_of);
                 typeof_well_typed_tot_or_gtot_term =
                   (uu___3.typeof_well_typed_tot_or_gtot_term);
                 use_bv_sorts = (uu___3.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___3.normalized_eff_names);
                 fv_delta_depths = (uu___3.fv_delta_depths);
                 proof_ns = (uu___3.proof_ns);
                 synth_hook = (uu___3.synth_hook);
                 try_solve_implicits_hook = (uu___3.try_solve_implicits_hook);
                 splice = (uu___3.splice);
                 mpreprocess = (uu___3.mpreprocess);
                 postprocess = (uu___3.postprocess);
                 identifier_info = (uu___3.identifier_info);
                 tc_hooks = (uu___3.tc_hooks);
                 dsenv = (uu___3.dsenv);
                 nbe = (uu___3.nbe);
                 strict_args_tab = (uu___3.strict_args_tab);
                 erasable_types_tab = (uu___3.erasable_types_tab);
                 enable_defer_to_tac = (uu___3.enable_defer_to_tac);
                 unif_allow_ref_guards = (uu___3.unif_allow_ref_guards)
               }))
         | FStar_Pervasives_Native.Some (uu___1, m) ->
             let next = m + Prims.int_one in
             (add_query_index (l, next);
              (let uu___4 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu___4 next);
              (let uu___4 = env1 in
               {
                 solver = (uu___4.solver);
                 range = (uu___4.range);
                 curmodule = (uu___4.curmodule);
                 gamma = (uu___4.gamma);
                 gamma_sig = (uu___4.gamma_sig);
                 gamma_cache = (uu___4.gamma_cache);
                 modules = (uu___4.modules);
                 expected_typ = (uu___4.expected_typ);
                 sigtab = (uu___4.sigtab);
                 attrtab = (uu___4.attrtab);
                 instantiate_imp = (uu___4.instantiate_imp);
                 effects = (uu___4.effects);
                 generalize = (uu___4.generalize);
                 letrecs = (uu___4.letrecs);
                 top_level = (uu___4.top_level);
                 check_uvars = (uu___4.check_uvars);
                 use_eq = (uu___4.use_eq);
                 use_eq_strict = (uu___4.use_eq_strict);
                 is_iface = (uu___4.is_iface);
                 admit = (uu___4.admit);
                 lax = (uu___4.lax);
                 lax_universes = (uu___4.lax_universes);
                 phase1 = (uu___4.phase1);
                 failhard = (uu___4.failhard);
                 nosynth = (uu___4.nosynth);
                 uvar_subtyping = (uu___4.uvar_subtyping);
                 tc_term = (uu___4.tc_term);
                 typeof_tot_or_gtot_term = (uu___4.typeof_tot_or_gtot_term);
                 universe_of = (uu___4.universe_of);
                 typeof_well_typed_tot_or_gtot_term =
                   (uu___4.typeof_well_typed_tot_or_gtot_term);
                 use_bv_sorts = (uu___4.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___4.normalized_eff_names);
                 fv_delta_depths = (uu___4.fv_delta_depths);
                 proof_ns = (uu___4.proof_ns);
                 synth_hook = (uu___4.synth_hook);
                 try_solve_implicits_hook = (uu___4.try_solve_implicits_hook);
                 splice = (uu___4.splice);
                 mpreprocess = (uu___4.mpreprocess);
                 postprocess = (uu___4.postprocess);
                 identifier_info = (uu___4.identifier_info);
                 tc_hooks = (uu___4.tc_hooks);
                 dsenv = (uu___4.dsenv);
                 nbe = (uu___4.nbe);
                 strict_args_tab = (uu___4.strict_args_tab);
                 erasable_types_tab = (uu___4.erasable_types_tab);
                 enable_defer_to_tac = (uu___4.enable_defer_to_tac);
                 unif_allow_ref_guards = (uu___4.unif_allow_ref_guards)
               })))
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = FStar_Ident.string_of_lid env1.curmodule in
      FStar_Options.debug_at_level uu___ l
let (set_range : env -> FStar_Range.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___1 = e in
         {
           solver = (uu___1.solver);
           range = r;
           curmodule = (uu___1.curmodule);
           gamma = (uu___1.gamma);
           gamma_sig = (uu___1.gamma_sig);
           gamma_cache = (uu___1.gamma_cache);
           modules = (uu___1.modules);
           expected_typ = (uu___1.expected_typ);
           sigtab = (uu___1.sigtab);
           attrtab = (uu___1.attrtab);
           instantiate_imp = (uu___1.instantiate_imp);
           effects = (uu___1.effects);
           generalize = (uu___1.generalize);
           letrecs = (uu___1.letrecs);
           top_level = (uu___1.top_level);
           check_uvars = (uu___1.check_uvars);
           use_eq = (uu___1.use_eq);
           use_eq_strict = (uu___1.use_eq_strict);
           is_iface = (uu___1.is_iface);
           admit = (uu___1.admit);
           lax = (uu___1.lax);
           lax_universes = (uu___1.lax_universes);
           phase1 = (uu___1.phase1);
           failhard = (uu___1.failhard);
           nosynth = (uu___1.nosynth);
           uvar_subtyping = (uu___1.uvar_subtyping);
           tc_term = (uu___1.tc_term);
           typeof_tot_or_gtot_term = (uu___1.typeof_tot_or_gtot_term);
           universe_of = (uu___1.universe_of);
           typeof_well_typed_tot_or_gtot_term =
             (uu___1.typeof_well_typed_tot_or_gtot_term);
           use_bv_sorts = (uu___1.use_bv_sorts);
           qtbl_name_and_index = (uu___1.qtbl_name_and_index);
           normalized_eff_names = (uu___1.normalized_eff_names);
           fv_delta_depths = (uu___1.fv_delta_depths);
           proof_ns = (uu___1.proof_ns);
           synth_hook = (uu___1.synth_hook);
           try_solve_implicits_hook = (uu___1.try_solve_implicits_hook);
           splice = (uu___1.splice);
           mpreprocess = (uu___1.mpreprocess);
           postprocess = (uu___1.postprocess);
           identifier_info = (uu___1.identifier_info);
           tc_hooks = (uu___1.tc_hooks);
           dsenv = (uu___1.dsenv);
           nbe = (uu___1.nbe);
           strict_args_tab = (uu___1.strict_args_tab);
           erasable_types_tab = (uu___1.erasable_types_tab);
           enable_defer_to_tac = (uu___1.enable_defer_to_tac);
           unif_allow_ref_guards = (uu___1.unif_allow_ref_guards)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1 ->
    fun enabled ->
      let uu___ =
        let uu___1 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu___1 enabled in
      FStar_ST.op_Colon_Equals env1.identifier_info uu___
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun bv ->
      fun ty ->
        let uu___ =
          let uu___1 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu___1 bv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu___
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun fv ->
      fun ty ->
        let uu___ =
          let uu___1 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu___1 fv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu___
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1 ->
    fun ty_map ->
      let uu___ =
        let uu___1 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu___1 ty_map in
      FStar_ST.op_Colon_Equals env1.identifier_info uu___
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1 -> env1.modules
let (current_module : env -> FStar_Ident.lident) = fun env1 -> env1.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun lid ->
      let uu___ = env1 in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = lid;
        gamma = (uu___.gamma);
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (uu___.expected_typ);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = (uu___.use_eq);
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = (uu___.proof_ns);
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = (uu___.tc_hooks);
        dsenv = (uu___.dsenv);
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      FStar_All.pipe_right env1.modules
        (FStar_Util.for_some
           (fun m ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu___ = FStar_Ident.string_of_lid lid in
      FStar_Util.smap_try_find (sigtab env1) uu___
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Ident.string_of_lid l in
      FStar_Util.format1 "Name \"%s\" not found" uu___1 in
    (FStar_Errors.Fatal_NameNotFound, uu___)
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v ->
    let uu___ =
      let uu___1 = FStar_Syntax_Print.bv_to_string v in
      FStar_Util.format1 "Variable \"%s\" not found" uu___1 in
    (FStar_Errors.Fatal_VariableNotFound, uu___)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu___ ->
    let uu___1 = FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
    FStar_Syntax_Syntax.U_unif uu___1
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals ->
    fun us ->
      let n = (FStar_List.length formals) - Prims.int_one in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i -> fun u -> FStar_Syntax_Syntax.UN ((n - i), u)))
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
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu___1 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
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
  FStar_Syntax_Syntax.eff_decl -> FStar_Range.range -> unit) =
  fun ed ->
    fun rng ->
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        let msg =
          let uu___ =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu___1 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu___ uu___1 in
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect, msg) rng
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
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu___3 =
                    let uu___4 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us) in
                    let uu___5 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts) in
                    let uu___6 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname in
                    let uu___7 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.format4
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
           FStar_Util.starts_with uu___3 uu___4 in
         if uu___2
         then
           let lns =
             let uu___3 = FStar_Ident.ns_of_lid l in
             let uu___4 = let uu___5 = FStar_Ident.ident_of_lid l in [uu___5] in
             FStar_List.append uu___3 uu___4 in
           let cur1 =
             let uu___3 = FStar_Ident.ns_of_lid cur in
             let uu___4 =
               let uu___5 = FStar_Ident.ident_of_lid cur in [uu___5] in
             FStar_List.append uu___3 uu___4 in
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
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Pervasives.either * FStar_Range.range)
    FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env1 ->
    fun lid ->
      let cur_mod = in_cur_mod env1 lid in
      let cache t =
        (let uu___1 = FStar_Ident.string_of_lid lid in
         FStar_Util.smap_add (gamma_cache env1) uu___1 t);
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu___ =
            let uu___1 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (gamma_cache env1) uu___1 in
          match uu___ with
          | FStar_Pervasives_Native.None ->
              let uu___1 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2 ->
                     match uu___2 with
                     | FStar_Syntax_Syntax.Binding_lid (l, (us_names, t))
                         when FStar_Ident.lid_equals lid l ->
                         let us =
                           FStar_List.map
                             (fun uu___3 -> FStar_Syntax_Syntax.U_name uu___3)
                             us_names in
                         let uu___3 =
                           let uu___4 = FStar_Ident.range_of_lid l in
                           ((FStar_Pervasives.Inl (us, t)), uu___4) in
                         FStar_Pervasives_Native.Some uu___3
                     | uu___3 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu___1
                (fun uu___2 ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3 ->
                        match uu___3 with
                        | (uu___4,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle (ses, uu___5);
                             FStar_Syntax_Syntax.sigrng = uu___6;
                             FStar_Syntax_Syntax.sigquals = uu___7;
                             FStar_Syntax_Syntax.sigmeta = uu___8;
                             FStar_Syntax_Syntax.sigattrs = uu___9;
                             FStar_Syntax_Syntax.sigopts = uu___10;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu___11 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu___11
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
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
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
      if FStar_Util.is_some found
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
      let uu___ = FStar_Util.smap_try_find (attrtab env1) attr in
      match uu___ with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      let add_one env2 se1 attr =
        let uu___ = let uu___1 = lookup_attr env2 attr in se1 :: uu___1 in
        FStar_Util.smap_add (attrtab env2) attr uu___ in
      FStar_List.iter
        (fun attr ->
           let uu___ =
             let uu___1 = FStar_Syntax_Subst.compress attr in
             uu___1.FStar_Syntax_Syntax.n in
           match uu___ with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___1 =
                 let uu___2 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_Ident.string_of_lid uu___2 in
               add_one env1 se uu___1
           | uu___1 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu___) -> add_sigelts env1 ses
      | uu___ ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l ->
                let uu___2 = FStar_Ident.string_of_lid l in
                FStar_Util.smap_add (sigtab env1) uu___2 se) lids;
           add_se_to_attrtab env1 se)
and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env1 ->
    fun ses -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env1))
let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Range.range)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun bv ->
      FStar_Util.find_map env1.gamma
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
          FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu___, lb::[]), uu___1) ->
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
        | FStar_Syntax_Syntax.Sig_let ((uu___, lbs), uu___1) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Pervasives.Inl uu___2 -> failwith "impossible"
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
      FStar_Range.range ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
          FStar_Range.range) FStar_Pervasives_Native.option)
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
            (check_effect_is_not_a_template ne rng;
             (match us_opt with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some us ->
                  if
                    (FStar_List.length us) <>
                      (FStar_List.length
                         (FStar_Pervasives_Native.fst
                            ne.FStar_Syntax_Syntax.signature))
                  then
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature)) in
                            let uu___8 =
                              let uu___9 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us) in
                              Prims.op_Hat ", got " uu___9 in
                            Prims.op_Hat uu___7 uu___8 in
                          Prims.op_Hat ", expected " uu___6 in
                        Prims.op_Hat uu___4 uu___5 in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu___3 in
                    failwith uu___2
                  else ());
             (let uu___2 =
                let uu___3 = inst_ts us_opt ne.FStar_Syntax_Syntax.signature in
                (uu___3, (se.FStar_Syntax_Syntax.sigrng)) in
              FStar_Pervasives_Native.Some uu___2))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid, us, binders, uu___, uu___1) ->
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
          FStar_Syntax_Syntax.syntax) * FStar_Range.range)
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
                        (uu___1, uvs, t, uu___2, uu___3, uu___4);
                      FStar_Syntax_Syntax.sigrng = uu___5;
                      FStar_Syntax_Syntax.sigquals = uu___6;
                      FStar_Syntax_Syntax.sigmeta = uu___7;
                      FStar_Syntax_Syntax.sigattrs = uu___8;
                      FStar_Syntax_Syntax.sigopts = uu___9;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu___10 =
                     let uu___11 = inst_tscheme1 (uvs, t) in (uu___11, rng) in
                   FStar_Pervasives_Native.Some uu___10
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu___1;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu___2;
                      FStar_Syntax_Syntax.sigattrs = uu___3;
                      FStar_Syntax_Syntax.sigopts = uu___4;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu___5 =
                     let uu___6 = in_cur_mod env1 l in uu___6 = Yes in
                   if uu___5
                   then
                     let uu___6 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface in
                     (if uu___6
                      then
                        let uu___7 =
                          let uu___8 = inst_tscheme1 (uvs, t) in
                          (uu___8, rng) in
                        FStar_Pervasives_Native.Some uu___7
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu___7 =
                        let uu___8 = inst_tscheme1 (uvs, t) in (uu___8, rng) in
                      FStar_Pervasives_Native.Some uu___7)
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu___1, uu___2);
                      FStar_Syntax_Syntax.sigrng = uu___3;
                      FStar_Syntax_Syntax.sigquals = uu___4;
                      FStar_Syntax_Syntax.sigmeta = uu___5;
                      FStar_Syntax_Syntax.sigattrs = uu___6;
                      FStar_Syntax_Syntax.sigopts = uu___7;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu___8 =
                          let uu___9 = inst_tscheme1 (uvs, k) in
                          (uu___9, rng) in
                        FStar_Pervasives_Native.Some uu___8
                    | uu___8 ->
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              let uu___12 =
                                let uu___13 = FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu___13 in
                              (uvs, uu___12) in
                            inst_tscheme1 uu___11 in
                          (uu___10, rng) in
                        FStar_Pervasives_Native.Some uu___9)
               | FStar_Pervasives.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu___1, uu___2);
                      FStar_Syntax_Syntax.sigrng = uu___3;
                      FStar_Syntax_Syntax.sigquals = uu___4;
                      FStar_Syntax_Syntax.sigmeta = uu___5;
                      FStar_Syntax_Syntax.sigattrs = uu___6;
                      FStar_Syntax_Syntax.sigopts = uu___7;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu___8 =
                          let uu___9 = inst_tscheme_with (uvs, k) us in
                          (uu___9, rng) in
                        FStar_Pervasives_Native.Some uu___8
                    | uu___8 ->
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              let uu___12 =
                                let uu___13 = FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu___13 in
                              (uvs, uu___12) in
                            inst_tscheme_with uu___11 us in
                          (uu___10, rng) in
                        FStar_Pervasives_Native.Some uu___9)
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
                          FStar_Syntax_Syntax.sigopts = uu___7;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu___2 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range in
                   FStar_All.pipe_right uu___1
                     (FStar_Util.map_option
                        (fun uu___2 ->
                           match uu___2 with | (us_t, rng1) -> (us_t, rng1)))) in
        let uu___ =
          let uu___1 = lookup_qname env1 lid in
          FStar_Util.bind_opt uu___1 mapper in
        match uu___ with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = t in
                  let uu___5 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n = (uu___4.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu___5;
                    FStar_Syntax_Syntax.vars =
                      (uu___4.FStar_Syntax_Syntax.vars)
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
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
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
            let uu___3 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu___3 in
          (uu___1, uu___2)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 =
            let uu___1 = FStar_Range.use_range use_range in
            FStar_Range.set_use_range r uu___1 in
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
        (FStar_Syntax_Syntax.typ * FStar_Range.range)
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
              let uu___2 = FStar_Range.use_range use_range in
              FStar_Range.set_use_range r uu___2 in
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.set_use_range use_range t in
              (uu___3, r1) in
            FStar_Pervasives_Native.Some uu___2
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
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
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___ ->
              match uu___ with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu___1 = FStar_Ident.string_of_id x in
                  let uu___2 = FStar_Ident.string_of_id y in uu___1 = uu___2
              | uu___1 -> false) env1.gamma) FStar_Option.isSome
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
                (uu___1, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu___3;
              FStar_Syntax_Syntax.sigattrs = uu___4;
              FStar_Syntax_Syntax.sigopts = uu___5;_},
            FStar_Pervasives_Native.None),
           uu___6)
          ->
          let uu___7 =
            let uu___8 =
              let uu___9 =
                let uu___10 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu___10 t in
              (uvs, uu___9) in
            (uu___8, q) in
          FStar_Pervasives_Native.Some uu___7
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
                (uu___1, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu___2;
              FStar_Syntax_Syntax.sigquals = uu___3;
              FStar_Syntax_Syntax.sigmeta = uu___4;
              FStar_Syntax_Syntax.sigattrs = uu___5;
              FStar_Syntax_Syntax.sigopts = uu___6;_},
            FStar_Pervasives_Native.None),
           uu___7)
          ->
          let uu___8 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu___8 (uvs, t)
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
                (uu___1, uvs, t, uu___2, uu___3, uu___4);
              FStar_Syntax_Syntax.sigrng = uu___5;
              FStar_Syntax_Syntax.sigquals = uu___6;
              FStar_Syntax_Syntax.sigmeta = uu___7;
              FStar_Syntax_Syntax.sigattrs = uu___8;
              FStar_Syntax_Syntax.sigopts = uu___9;_},
            FStar_Pervasives_Native.None),
           uu___10)
          ->
          let uu___11 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu___11 (uvs, t)
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
                (uu___1, uu___2, uu___3, uu___4, uu___5, dcs);
              FStar_Syntax_Syntax.sigrng = uu___6;
              FStar_Syntax_Syntax.sigquals = uu___7;
              FStar_Syntax_Syntax.sigmeta = uu___8;
              FStar_Syntax_Syntax.sigattrs = uu___9;
              FStar_Syntax_Syntax.sigopts = uu___10;_},
            uu___11),
           uu___12)
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
                (uu___1, uu___2, uu___3, l, uu___4, uu___5);
              FStar_Syntax_Syntax.sigrng = uu___6;
              FStar_Syntax_Syntax.sigquals = uu___7;
              FStar_Syntax_Syntax.sigmeta = uu___8;
              FStar_Syntax_Syntax.sigattrs = uu___9;
              FStar_Syntax_Syntax.sigopts = uu___10;_},
            uu___11),
           uu___12)
          -> l
      | uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu___3 in
          failwith uu___2
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
            FStar_All.pipe_right delta_levels
              (FStar_Util.for_some
                 (fun dl ->
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some (visible_at dl)))) in
          match qninfo1 with
          | FStar_Pervasives_Native.Some
              (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None),
               uu___)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu___1) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
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
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid) uu___
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
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu___
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv ->
    fun qn ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu___ = let uu___1 = FStar_Ident.nsstr lid in uu___1 = "Prims" in
      if uu___
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl uu___2, uu___3)
             ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Pervasives.Inr (se, uu___2), uu___3) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu___4 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu___4 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu___4 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu___4 ->
                  let uu___5 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals in
                  FStar_Pervasives_Native.Some uu___5
              | FStar_Syntax_Syntax.Sig_let ((uu___4, lbs), uu___5) ->
                  FStar_Util.find_map lbs
                    (fun lb ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       let uu___6 = FStar_Syntax_Syntax.fv_eq_lid fv1 lid in
                       if uu___6
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu___4 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu___4 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu___4 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu___4 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu___4 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu___4 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu___4 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___4 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___4 ->
                  FStar_Pervasives_Native.None))
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu___ = let uu___1 = FStar_Ident.nsstr lid in uu___1 = "Prims" in
      if uu___
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu___2 =
           let uu___3 = FStar_Ident.string_of_lid lid in
           FStar_All.pipe_right uu___3
             (FStar_Util.smap_try_find env1.fv_delta_depths) in
         FStar_All.pipe_right uu___2
           (fun d_opt ->
              let uu___3 = FStar_All.pipe_right d_opt FStar_Util.is_some in
              if uu___3
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu___5 =
                   let uu___6 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   delta_depth_of_qninfo fv uu___6 in
                 match uu___5 with
                 | FStar_Pervasives_Native.None ->
                     let uu___6 =
                       let uu___7 = FStar_Syntax_Print.fv_to_string fv in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu___7 in
                     failwith uu___6
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu___7 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ()) in
                       if uu___7
                       then
                         let uu___8 = FStar_Syntax_Print.fv_to_string fv in
                         let uu___9 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta in
                         let uu___10 =
                           FStar_Syntax_Print.delta_depth_to_string d in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu___8 uu___9 uu___10
                       else ());
                      (let uu___8 = FStar_Ident.string_of_lid lid in
                       FStar_Util.smap_add env1.fv_delta_depths uu___8 d);
                      d))))
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
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      FStar_All.pipe_left attrs_of_qninfo uu___
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
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm ->
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Util.un_uinst tm in
                        uu___3.FStar_Syntax_Syntax.n in
                      match uu___2 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu___3 -> false)) in
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
    'a FStar_Util.smap ->
      FStar_Syntax_Syntax.fv -> (unit -> (Prims.bool * 'a)) -> 'a
  =
  fun tab ->
    fun fv ->
      fun f ->
        let s =
          let uu___ = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu___ in
        let uu___ = FStar_Util.smap_try_find tab s in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 = f () in
            (match uu___1 with
             | (should_cache, res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1 ->
    fun fv ->
      let f uu___ =
        let uu___1 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr in
        match uu___1 with | (ex, erasable) -> (ex, erasable) in
      cache_in_fv_tab env1.erasable_types_tab fv f
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
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head, uu___1) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) -> non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu___1 -> false
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
              FStar_Util.find_map attrs1
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
                  (lid, univs, binders, c, uu___1);
                FStar_Syntax_Syntax.sigrng = uu___2;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu___3;
                FStar_Syntax_Syntax.sigattrs = uu___4;
                FStar_Syntax_Syntax.sigopts = uu___5;_},
              FStar_Pervasives_Native.None),
             uu___6)
            ->
            let lid1 =
              let uu___7 =
                let uu___8 = FStar_Ident.range_of_lid lid in
                let uu___9 =
                  let uu___10 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu___10 in
                FStar_Range.set_use_range uu___8 uu___9 in
              FStar_Ident.set_lid_range lid uu___7 in
            let uu___7 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___8 ->
                      match uu___8 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu___9 -> false)) in
            if uu___7
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu___10 =
                      let uu___11 =
                        let uu___12 = get_range env1 in
                        FStar_Range.string_of_range uu___12 in
                      let uu___12 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu___13 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu___11 uu___12 uu___13 in
                    failwith uu___10) in
               match (binders, univs) with
               | ([], uu___9) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu___9, uu___10::uu___11::uu___12) ->
                   let uu___13 =
                     let uu___14 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu___15 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu___14 uu___15 in
                   failwith uu___13
               | uu___9 ->
                   let uu___10 =
                     let uu___11 =
                       let uu___12 = FStar_Syntax_Util.arrow binders c in
                       (univs, uu___12) in
                     inst_tscheme_with uu___11 insts in
                   (match uu___10 with
                    | (uu___11, t) ->
                        let t1 =
                          let uu___12 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu___12 t in
                        let uu___12 =
                          let uu___13 = FStar_Syntax_Subst.compress t1 in
                          uu___13.FStar_Syntax_Syntax.n in
                        (match uu___12 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu___13 -> failwith "Impossible")))
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
          FStar_Util.smap_try_find env1.normalized_eff_names uu___1 in
        match uu___ with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu___1 = find l in
            (match uu___1 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu___3 = FStar_Ident.string_of_lid l in
                   FStar_Util.smap_add env1.normalized_eff_names uu___3 m);
                  m)) in
      let uu___ = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu___
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1 ->
    fun name ->
      fun r ->
        let sig_t =
          let uu___ = FStar_All.pipe_right name (lookup_effect_lid env1) in
          FStar_All.pipe_right uu___ FStar_Syntax_Subst.compress in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs, uu___) ->
            FStar_List.length bs
        | uu___ ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Ident.string_of_lid name in
                let uu___4 = FStar_Syntax_Print.term_to_string sig_t in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu___3 uu___4 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu___2) in
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
              FStar_Syntax_Syntax.sigopts = uu___5;_},
            uu___6),
           uu___7)
          -> q
      | uu___1 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      fun i ->
        let fail uu___ =
          let uu___1 =
            let uu___2 = FStar_Util.string_of_int i in
            let uu___3 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu___2 uu___3 in
          failwith uu___1 in
        let uu___ = lookup_datacon env1 lid in
        match uu___ with
        | (uu___1, t) ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.compress t in
              uu___3.FStar_Syntax_Syntax.n in
            (match uu___2 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu___3) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
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
                (uu___1, uu___2, uu___3);
              FStar_Syntax_Syntax.sigrng = uu___4;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu___5;
              FStar_Syntax_Syntax.sigattrs = uu___6;
              FStar_Syntax_Syntax.sigopts = uu___7;_},
            uu___8),
           uu___9)
          ->
          FStar_Util.for_some
            (fun uu___10 ->
               match uu___10 with
               | FStar_Syntax_Syntax.Projector uu___11 -> true
               | uu___11 -> false) quals
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
                (uu___1, uu___2, uu___3, uu___4, uu___5, uu___6);
              FStar_Syntax_Syntax.sigrng = uu___7;
              FStar_Syntax_Syntax.sigquals = uu___8;
              FStar_Syntax_Syntax.sigmeta = uu___9;
              FStar_Syntax_Syntax.sigattrs = uu___10;
              FStar_Syntax_Syntax.sigopts = uu___11;_},
            uu___12),
           uu___13)
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
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu___1, uu___2, uu___3, uu___4, uu___5, uu___6);
              FStar_Syntax_Syntax.sigrng = uu___7;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu___8;
              FStar_Syntax_Syntax.sigattrs = uu___9;
              FStar_Syntax_Syntax.sigopts = uu___10;_},
            uu___11),
           uu___12)
          ->
          FStar_Util.for_some
            (fun uu___13 ->
               match uu___13 with
               | FStar_Syntax_Syntax.RecordType uu___14 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu___14 -> true
               | uu___14 -> false) quals
      | uu___1 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Pervasives.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu___, uu___1);
            FStar_Syntax_Syntax.sigrng = uu___2;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu___3;
            FStar_Syntax_Syntax.sigattrs = uu___4;
            FStar_Syntax_Syntax.sigopts = uu___5;_},
          uu___6),
         uu___7)
        ->
        FStar_Util.for_some
          (fun uu___8 ->
             match uu___8 with
             | FStar_Syntax_Syntax.Action uu___9 -> true
             | uu___9 -> false) quals
    | uu___ -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu___ = lookup_qname env1 lid in
      FStar_All.pipe_left qninfo_is_action uu___
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
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu___1 -> true
           | uu___1 -> false)
      | uu___1 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = lookup_qname env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr (se, uu___1), uu___2) ->
          FStar_Util.for_some
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
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu___1 ->
                 FStar_Pervasives_Native.Some true
             | uu___1 -> FStar_Pervasives_Native.Some false) in
      let uu___ =
        let uu___1 = lookup_qname env1 lid in
        FStar_Util.bind_opt uu___1 mapper in
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
                (uu___1, uu___2, tps, uu___3, uu___4, uu___5);
              FStar_Syntax_Syntax.sigrng = uu___6;
              FStar_Syntax_Syntax.sigquals = uu___7;
              FStar_Syntax_Syntax.sigmeta = uu___8;
              FStar_Syntax_Syntax.sigattrs = uu___9;
              FStar_Syntax_Syntax.sigopts = uu___10;_},
            uu___11),
           uu___12)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu___1 -> FStar_Pervasives_Native.None
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      FStar_All.pipe_right (env1.effects).decls
        (FStar_Util.find_opt
           (fun uu___ ->
              match uu___ with
              | (d, uu___1) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
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
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu___ = FStar_All.pipe_right l (get_effect_decl env1) in
      FStar_All.pipe_right uu___ FStar_Syntax_Util.is_layered
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu___ -> fun c -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu___ -> fun uu___1 -> fun e -> FStar_Util.return_all e))
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
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu___5 ->
                        match uu___5 with
                        | (m1, m2, uu___6, uu___7, uu___8) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
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
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu___3 uu___4 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu___2) in
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
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env1.effects).order
            (FStar_Util.find_opt
               (fun e ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
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
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu___1 ->
                match uu___1 with
                | (d, uu___2) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid m in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu___2 in
          failwith uu___1
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu___1 = inst_tscheme md.FStar_Syntax_Syntax.signature in
          (match uu___1 with
           | (uu___2, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow (b::wp_b::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    ->
                    ((b.FStar_Syntax_Syntax.binder_bv),
                      ((wp_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort))
                | uu___3 -> failwith "Impossible"))
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env1 -> fun m -> wp_sig_aux (env1.effects).decls m
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun c ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
            let u = env1.universe_of env1 t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
            let u = env1.universe_of env1 t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu___ -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun comp ->
      let c = comp_to_comp_typ env1 comp in
      let uu___ =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu___ with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu___1 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu___1 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu___6 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one) in
                       let uu___7 =
                         let uu___8 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu___8 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu___5 uu___6 uu___7 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu___4) in
                   FStar_Errors.raise_error uu___3
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu___3 =
                     let uu___4 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu___4 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun b ->
                        fun uu___4 ->
                          match uu___4 with
                          | (t, uu___5) ->
                              FStar_Syntax_Syntax.NT
                                ((b.FStar_Syntax_Syntax.binder_bv), t))
                     binders1 uu___3 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1 in
                 let c2 =
                   let uu___3 =
                     let uu___4 = comp_to_comp_typ env1 c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___4.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___4.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___4.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___4.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu___3 FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env1 c2)))
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
              ((FStar_List.length args), uu___1) in
            match uu___ with
            | (given, expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu___2 = FStar_Ident.string_of_lid eff_name in
                     let uu___3 = FStar_Util.string_of_int given in
                     let uu___4 = FStar_Util.string_of_int expected in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu___2 uu___3 uu___4 in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r) in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c) in
          let uu___ = effect_decl_opt env1 effect_name in
          match uu___ with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, uu___1) ->
              let uu___2 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
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
                             let uu___8 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg in
                             uu___8 :: (c1.FStar_Syntax_Syntax.effect_args) in
                           (repr, uu___7) in
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
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env1 effect_lid in
      let quals = lookup_effect_quals env1 effect_lid1 in
      FStar_All.pipe_right quals
        (FStar_List.existsb
           (fun uu___ ->
              match uu___ with
              | FStar_Syntax_Syntax.Reflectable uu___1 -> true
              | uu___1 -> false))
let (is_total_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env1 effect_lid in
      let quals = lookup_effect_quals env1 effect_lid1 in
      FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals
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
      | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) -> is_reifiable_comp env1 c
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
               FStar_Util.format1 "Effect %s cannot be reified" uu___4 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu___3) in
           let uu___3 = get_range env1 in
           FStar_Errors.raise_error uu___2 uu___3
         else ());
        (let uu___1 = effect_repr_aux true env1 c u_c in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env2 =
        let uu___ = env1 in
        {
          solver = (uu___.solver);
          range = (uu___.range);
          curmodule = (uu___.curmodule);
          gamma = (uu___.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___.gamma_cache);
          modules = (uu___.modules);
          expected_typ = (uu___.expected_typ);
          sigtab = (uu___.sigtab);
          attrtab = (uu___.attrtab);
          instantiate_imp = (uu___.instantiate_imp);
          effects = (uu___.effects);
          generalize = (uu___.generalize);
          letrecs = (uu___.letrecs);
          top_level = (uu___.top_level);
          check_uvars = (uu___.check_uvars);
          use_eq = (uu___.use_eq);
          use_eq_strict = (uu___.use_eq_strict);
          is_iface = (uu___.is_iface);
          admit = (uu___.admit);
          lax = (uu___.lax);
          lax_universes = (uu___.lax_universes);
          phase1 = (uu___.phase1);
          failhard = (uu___.failhard);
          nosynth = (uu___.nosynth);
          uvar_subtyping = (uu___.uvar_subtyping);
          tc_term = (uu___.tc_term);
          typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
          universe_of = (uu___.universe_of);
          typeof_well_typed_tot_or_gtot_term =
            (uu___.typeof_well_typed_tot_or_gtot_term);
          use_bv_sorts = (uu___.use_bv_sorts);
          qtbl_name_and_index = (uu___.qtbl_name_and_index);
          normalized_eff_names = (uu___.normalized_eff_names);
          fv_delta_depths = (uu___.fv_delta_depths);
          proof_ns = (uu___.proof_ns);
          synth_hook = (uu___.synth_hook);
          try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
          splice = (uu___.splice);
          mpreprocess = (uu___.mpreprocess);
          postprocess = (uu___.postprocess);
          identifier_info = (uu___.identifier_info);
          tc_hooks = (uu___.tc_hooks);
          dsenv = (uu___.dsenv);
          nbe = (uu___.nbe);
          strict_args_tab = (uu___.strict_args_tab);
          erasable_types_tab = (uu___.erasable_types_tab);
          enable_defer_to_tac = (uu___.enable_defer_to_tac);
          unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
        } in
      add_sigelt env2 s;
      (env2.tc_hooks).tc_push_in_gamma_hook env2 (FStar_Pervasives.Inr sb);
      env2
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
              decls = (FStar_List.append (env1.effects).decls [(ed, quals)]);
              order = (uu___1.order);
              joins = (uu___1.joins);
              polymonadic_binds = (uu___1.polymonadic_binds);
              polymonadic_subcomps = (uu___1.polymonadic_subcomps)
            } in
          let uu___1 = env1 in
          {
            solver = (uu___1.solver);
            range = (uu___1.range);
            curmodule = (uu___1.curmodule);
            gamma = (uu___1.gamma);
            gamma_sig = (uu___1.gamma_sig);
            gamma_cache = (uu___1.gamma_cache);
            modules = (uu___1.modules);
            expected_typ = (uu___1.expected_typ);
            sigtab = (uu___1.sigtab);
            attrtab = (uu___1.attrtab);
            instantiate_imp = (uu___1.instantiate_imp);
            effects = effects1;
            generalize = (uu___1.generalize);
            letrecs = (uu___1.letrecs);
            top_level = (uu___1.top_level);
            check_uvars = (uu___1.check_uvars);
            use_eq = (uu___1.use_eq);
            use_eq_strict = (uu___1.use_eq_strict);
            is_iface = (uu___1.is_iface);
            admit = (uu___1.admit);
            lax = (uu___1.lax);
            lax_universes = (uu___1.lax_universes);
            phase1 = (uu___1.phase1);
            failhard = (uu___1.failhard);
            nosynth = (uu___1.nosynth);
            uvar_subtyping = (uu___1.uvar_subtyping);
            tc_term = (uu___1.tc_term);
            typeof_tot_or_gtot_term = (uu___1.typeof_tot_or_gtot_term);
            universe_of = (uu___1.universe_of);
            typeof_well_typed_tot_or_gtot_term =
              (uu___1.typeof_well_typed_tot_or_gtot_term);
            use_bv_sorts = (uu___1.use_bv_sorts);
            qtbl_name_and_index = (uu___1.qtbl_name_and_index);
            normalized_eff_names = (uu___1.normalized_eff_names);
            fv_delta_depths = (uu___1.fv_delta_depths);
            proof_ns = (uu___1.proof_ns);
            synth_hook = (uu___1.synth_hook);
            try_solve_implicits_hook = (uu___1.try_solve_implicits_hook);
            splice = (uu___1.splice);
            mpreprocess = (uu___1.mpreprocess);
            postprocess = (uu___1.postprocess);
            identifier_info = (uu___1.identifier_info);
            tc_hooks = (uu___1.tc_hooks);
            dsenv = (uu___1.dsenv);
            nbe = (uu___1.nbe);
            strict_args_tab = (uu___1.strict_args_tab);
            erasable_types_tab = (uu___1.erasable_types_tab);
            enable_defer_to_tac = (uu___1.enable_defer_to_tac);
            unif_allow_ref_guards = (uu___1.unif_allow_ref_guards)
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
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu___1 ->
                  match uu___1 with
                  | (m1, n1, uu___2, uu___3) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu___ with
        | FStar_Pervasives_Native.Some (uu___1, uu___2, p, t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu___1 -> FStar_Pervasives_Native.None
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun m ->
      fun n ->
        let uu___ =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu___1 ->
                  match uu___1 with
                  | (m1, n1, uu___2) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu___ with
        | FStar_Pervasives_Native.Some (uu___1, uu___2, ts) ->
            FStar_Pervasives_Native.Some ts
        | uu___1 -> FStar_Pervasives_Native.None
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1 ->
    fun src ->
      fun tgt ->
        fun st_mlift ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu___ = FStar_All.pipe_right c ((e1.mlift).mlift_wp env2) in
                FStar_All.pipe_right uu___
                  (fun uu___1 ->
                     match uu___1 with
                     | (c1, g1) ->
                         let uu___2 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2) in
                         FStar_All.pipe_right uu___2
                           (fun uu___3 ->
                              match uu___3 with
                              | (c2, g2) ->
                                  let uu___4 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2 in
                                  (c2, uu___4))) in
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
              mlift = composed_lift
            } in
          let edge1 = { msource = src; mtarget = tgt; mlift = st_mlift } in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift } in
          let find_edge order uu___ =
            match uu___ with
            | (i, j) ->
                let uu___1 = FStar_Ident.lid_equals i j in
                if uu___1
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
                else
                  FStar_All.pipe_right order
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let ms =
            FStar_All.pipe_right (env1.effects).decls
              (FStar_List.map
                 (fun uu___ ->
                    match uu___ with
                    | (e, uu___1) -> e.FStar_Syntax_Syntax.mname)) in
          let all_i_src =
            FStar_All.pipe_right ms
              (FStar_List.fold_left
                 (fun edges ->
                    fun i ->
                      let uu___ =
                        find_edge (env1.effects).order (i, (edge1.msource)) in
                      match uu___ with
                      | FStar_Pervasives_Native.Some e -> e :: edges
                      | FStar_Pervasives_Native.None -> edges) []) in
          let all_tgt_j =
            FStar_All.pipe_right ms
              (FStar_List.fold_left
                 (fun edges ->
                    fun j ->
                      let uu___ =
                        find_edge (env1.effects).order ((edge1.mtarget), j) in
                      match uu___ with
                      | FStar_Pervasives_Native.Some e -> e :: edges
                      | FStar_Pervasives_Native.None -> edges) []) in
          let new_edges =
            FStar_List.fold_left
              (fun edges ->
                 fun i_src ->
                   FStar_List.fold_left
                     (fun edges1 ->
                        fun tgt_j ->
                          let src1 = i_src.msource in
                          let tgt1 = tgt_j.mtarget in
                          (let uu___1 = FStar_Ident.lid_equals src1 tgt1 in
                           if uu___1
                           then
                             let uu___2 =
                               let uu___3 =
                                 let uu___4 =
                                   FStar_Ident.string_of_lid edge1.msource in
                                 let uu___5 =
                                   FStar_Ident.string_of_lid edge1.mtarget in
                                 let uu___6 = FStar_Ident.string_of_lid src1 in
                                 FStar_Util.format3
                                   "Adding an edge %s~>%s induces a cycle %s"
                                   uu___4 uu___5 uu___6 in
                               (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                 uu___3) in
                             FStar_Errors.raise_error uu___2 env1.range
                           else ());
                          (let uu___1 =
                             let uu___2 =
                               find_edge (env1.effects).order (src1, tgt1) in
                             FStar_All.pipe_right uu___2 FStar_Util.is_some in
                           if uu___1
                           then edges1
                           else
                             (let uu___3 =
                                (let uu___4 =
                                   exists_polymonadic_subcomp env1 src1 tgt1 in
                                 FStar_All.pipe_right uu___4
                                   FStar_Util.is_some)
                                  ||
                                  (let uu___4 =
                                     exists_polymonadic_subcomp env1 tgt1
                                       src1 in
                                   FStar_All.pipe_right uu___4
                                     FStar_Util.is_some) in
                              if uu___3
                              then
                                let uu___4 =
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_Ident.string_of_lid edge1.msource in
                                    let uu___7 =
                                      FStar_Ident.string_of_lid edge1.mtarget in
                                    let uu___8 =
                                      FStar_Ident.string_of_lid src1 in
                                    let uu___9 =
                                      FStar_Ident.string_of_lid tgt1 in
                                    FStar_Util.format4
                                      "Adding an edge %s~>%s induces an edge %s~>%s that conflicts with an existing polymonadic subcomp between them"
                                      uu___6 uu___7 uu___8 uu___9 in
                                  (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                    uu___5) in
                                FStar_Errors.raise_error uu___4 env1.range
                              else
                                (let uu___5 =
                                   let uu___6 = compose_edges i_src edge1 in
                                   compose_edges uu___6 tgt_j in
                                 uu___5 :: edges1)))) edges all_tgt_j) []
              all_i_src in
          let order = FStar_List.append new_edges (env1.effects).order in
          FStar_All.pipe_right order
            (FStar_List.iter
               (fun edge2 ->
                  let uu___1 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu___2 = lookup_effect_quals env1 edge2.mtarget in
                       FStar_All.pipe_right uu___2
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)) in
                  if uu___1
                  then
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStar_Ident.string_of_lid edge2.mtarget in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu___4 in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu___3) in
                    let uu___3 = get_range env1 in
                    FStar_Errors.raise_error uu___2 uu___3
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j ->
                             let k_opt =
                               let uu___1 = FStar_Ident.lid_equals i j in
                               if uu___1
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt ->
                                         fun k ->
                                           let uu___3 =
                                             let uu___4 =
                                               find_edge order (i, k) in
                                             let uu___5 =
                                               find_edge order (j, k) in
                                             (uu___4, uu___5) in
                                           match uu___3 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,
                                              FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub, uu___4, uu___5) ->
                                                    let uu___6 =
                                                      let uu___7 =
                                                        let uu___8 =
                                                          find_edge order
                                                            (k, ub) in
                                                        FStar_Util.is_some
                                                          uu___8 in
                                                      let uu___8 =
                                                        let uu___9 =
                                                          find_edge order
                                                            (ub, k) in
                                                        FStar_Util.is_some
                                                          uu___9 in
                                                      (uu___7, uu___8) in
                                                    (match uu___6 with
                                                     | (true, true) ->
                                                         let uu___7 =
                                                           FStar_Ident.lid_equals
                                                             k ub in
                                                         if uu___7
                                                         then
                                                           (FStar_Errors.log_issue
                                                              FStar_Range.dummyRange
                                                              (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                "Looking multiple times at the same upper bound candidate");
                                                            bopt)
                                                         else
                                                           failwith
                                                             "Found a cycle in the lattice"
                                                     | (false, false) ->
                                                         let uu___7 =
                                                           let uu___8 =
                                                             let uu___9 =
                                                               FStar_Ident.string_of_lid
                                                                 i in
                                                             let uu___10 =
                                                               FStar_Ident.string_of_lid
                                                                 j in
                                                             let uu___11 =
                                                               FStar_Ident.string_of_lid
                                                                 k in
                                                             let uu___12 =
                                                               FStar_Ident.string_of_lid
                                                                 ub in
                                                             FStar_Util.format4
                                                               "Uncomparable upper bounds! i=%s, j=%s, k=%s, ub=%s\n"
                                                               uu___9 uu___10
                                                               uu___11
                                                               uu___12 in
                                                           (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                                             uu___8) in
                                                         FStar_Errors.raise_error
                                                           uu___7 env1.range
                                                     | (true, false) ->
                                                         FStar_Pervasives_Native.Some
                                                           (k, ik, jk)
                                                     | (false, true) -> bopt))
                                           | uu___4 -> bopt)
                                      FStar_Pervasives_Native.None) in
                             match k_opt with
                             | FStar_Pervasives_Native.None -> []
                             | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                 let uu___1 =
                                   (let uu___2 =
                                      exists_polymonadic_bind env1 i j in
                                    FStar_All.pipe_right uu___2
                                      FStar_Util.is_some)
                                     ||
                                     (let uu___2 =
                                        exists_polymonadic_bind env1 j i in
                                      FStar_All.pipe_right uu___2
                                        FStar_Util.is_some) in
                                 if uu___1
                                 then
                                   let uu___2 =
                                     let uu___3 =
                                       let uu___4 =
                                         FStar_Ident.string_of_lid src in
                                       let uu___5 =
                                         FStar_Ident.string_of_lid tgt in
                                       let uu___6 =
                                         FStar_Ident.string_of_lid i in
                                       let uu___7 =
                                         FStar_Ident.string_of_lid j in
                                       let uu___8 =
                                         FStar_Ident.string_of_lid k in
                                       FStar_Util.format5
                                         "Updating effect lattice with a lift between %s and %s induces a least upper bound %s of %s and %s, and this conflicts with a polymonadic bind between them"
                                         uu___4 uu___5 uu___6 uu___7 uu___8 in
                                     (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                       uu___3) in
                                   FStar_Errors.raise_error uu___2 env1.range
                                 else
                                   (let j_opt = join_opt env1 i j in
                                    let uu___3 =
                                      (FStar_All.pipe_right j_opt
                                         FStar_Util.is_some)
                                        &&
                                        (let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               FStar_All.pipe_right j_opt
                                                 FStar_Util.must in
                                             FStar_All.pipe_right uu___6
                                               (fun uu___7 ->
                                                  match uu___7 with
                                                  | (l, uu___8, uu___9) -> l) in
                                           FStar_Ident.lid_equals k uu___5 in
                                         Prims.op_Negation uu___4) in
                                    if uu___3
                                    then
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            FStar_Ident.string_of_lid src in
                                          let uu___7 =
                                            FStar_Ident.string_of_lid tgt in
                                          let uu___8 =
                                            FStar_Ident.string_of_lid i in
                                          let uu___9 =
                                            FStar_Ident.string_of_lid j in
                                          let uu___10 =
                                            FStar_Ident.string_of_lid k in
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                FStar_All.pipe_right j_opt
                                                  FStar_Util.must in
                                              FStar_All.pipe_right uu___13
                                                (fun uu___14 ->
                                                   match uu___14 with
                                                   | (l, uu___15, uu___16) ->
                                                       l) in
                                            FStar_All.pipe_right uu___12
                                              FStar_Ident.string_of_lid in
                                          FStar_Util.format6
                                            "Updating effect lattice with %s ~> %s makes the least upper bound of %s and %s as %s, whereas earlier it was %s"
                                            uu___6 uu___7 uu___8 uu___9
                                            uu___10 uu___11 in
                                        (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                          uu___5) in
                                      FStar_Errors.raise_error uu___4
                                        env1.range
                                    else [(i, j, k, (e1.mlift), (e2.mlift))]))))) in
           let effects1 =
             let uu___1 = env1.effects in
             {
               decls = (uu___1.decls);
               order;
               joins;
               polymonadic_binds = (uu___1.polymonadic_binds);
               polymonadic_subcomps = (uu___1.polymonadic_subcomps)
             } in
           let uu___1 = env1 in
           {
             solver = (uu___1.solver);
             range = (uu___1.range);
             curmodule = (uu___1.curmodule);
             gamma = (uu___1.gamma);
             gamma_sig = (uu___1.gamma_sig);
             gamma_cache = (uu___1.gamma_cache);
             modules = (uu___1.modules);
             expected_typ = (uu___1.expected_typ);
             sigtab = (uu___1.sigtab);
             attrtab = (uu___1.attrtab);
             instantiate_imp = (uu___1.instantiate_imp);
             effects = effects1;
             generalize = (uu___1.generalize);
             letrecs = (uu___1.letrecs);
             top_level = (uu___1.top_level);
             check_uvars = (uu___1.check_uvars);
             use_eq = (uu___1.use_eq);
             use_eq_strict = (uu___1.use_eq_strict);
             is_iface = (uu___1.is_iface);
             admit = (uu___1.admit);
             lax = (uu___1.lax);
             lax_universes = (uu___1.lax_universes);
             phase1 = (uu___1.phase1);
             failhard = (uu___1.failhard);
             nosynth = (uu___1.nosynth);
             uvar_subtyping = (uu___1.uvar_subtyping);
             tc_term = (uu___1.tc_term);
             typeof_tot_or_gtot_term = (uu___1.typeof_tot_or_gtot_term);
             universe_of = (uu___1.universe_of);
             typeof_well_typed_tot_or_gtot_term =
               (uu___1.typeof_well_typed_tot_or_gtot_term);
             use_bv_sorts = (uu___1.use_bv_sorts);
             qtbl_name_and_index = (uu___1.qtbl_name_and_index);
             normalized_eff_names = (uu___1.normalized_eff_names);
             fv_delta_depths = (uu___1.fv_delta_depths);
             proof_ns = (uu___1.proof_ns);
             synth_hook = (uu___1.synth_hook);
             try_solve_implicits_hook = (uu___1.try_solve_implicits_hook);
             splice = (uu___1.splice);
             mpreprocess = (uu___1.mpreprocess);
             postprocess = (uu___1.postprocess);
             identifier_info = (uu___1.identifier_info);
             tc_hooks = (uu___1.tc_hooks);
             dsenv = (uu___1.dsenv);
             nbe = (uu___1.nbe);
             strict_args_tab = (uu___1.strict_args_tab);
             erasable_types_tab = (uu___1.erasable_types_tab);
             enable_defer_to_tac = (uu___1.enable_defer_to_tac);
             unif_allow_ref_guards = (uu___1.unif_allow_ref_guards)
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
            let err_msg poly =
              let uu___ = FStar_Ident.string_of_lid m in
              let uu___1 = FStar_Ident.string_of_lid n in
              let uu___2 = FStar_Ident.string_of_lid p in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu___ uu___1 uu___2
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice") in
            let uu___ =
              let uu___1 = exists_polymonadic_bind env1 m n in
              FStar_All.pipe_right uu___1 FStar_Util.is_some in
            if uu___
            then
              let uu___1 =
                let uu___2 = err_msg true in
                (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu___2) in
              FStar_Errors.raise_error uu___1 env1.range
            else
              (let uu___2 =
                 (let uu___3 = join_opt env1 m n in
                  FStar_All.pipe_right uu___3 FStar_Util.is_some) &&
                   (let uu___3 = FStar_Ident.lid_equals m n in
                    Prims.op_Negation uu___3) in
               if uu___2
               then
                 let uu___3 =
                   let uu___4 = err_msg false in
                   (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu___4) in
                 FStar_Errors.raise_error uu___3 env1.range
               else
                 (let uu___4 = env1 in
                  {
                    solver = (uu___4.solver);
                    range = (uu___4.range);
                    curmodule = (uu___4.curmodule);
                    gamma = (uu___4.gamma);
                    gamma_sig = (uu___4.gamma_sig);
                    gamma_cache = (uu___4.gamma_cache);
                    modules = (uu___4.modules);
                    expected_typ = (uu___4.expected_typ);
                    sigtab = (uu___4.sigtab);
                    attrtab = (uu___4.attrtab);
                    instantiate_imp = (uu___4.instantiate_imp);
                    effects =
                      (let uu___5 = env1.effects in
                       {
                         decls = (uu___5.decls);
                         order = (uu___5.order);
                         joins = (uu___5.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps = (uu___5.polymonadic_subcomps)
                       });
                    generalize = (uu___4.generalize);
                    letrecs = (uu___4.letrecs);
                    top_level = (uu___4.top_level);
                    check_uvars = (uu___4.check_uvars);
                    use_eq = (uu___4.use_eq);
                    use_eq_strict = (uu___4.use_eq_strict);
                    is_iface = (uu___4.is_iface);
                    admit = (uu___4.admit);
                    lax = (uu___4.lax);
                    lax_universes = (uu___4.lax_universes);
                    phase1 = (uu___4.phase1);
                    failhard = (uu___4.failhard);
                    nosynth = (uu___4.nosynth);
                    uvar_subtyping = (uu___4.uvar_subtyping);
                    tc_term = (uu___4.tc_term);
                    typeof_tot_or_gtot_term =
                      (uu___4.typeof_tot_or_gtot_term);
                    universe_of = (uu___4.universe_of);
                    typeof_well_typed_tot_or_gtot_term =
                      (uu___4.typeof_well_typed_tot_or_gtot_term);
                    use_bv_sorts = (uu___4.use_bv_sorts);
                    qtbl_name_and_index = (uu___4.qtbl_name_and_index);
                    normalized_eff_names = (uu___4.normalized_eff_names);
                    fv_delta_depths = (uu___4.fv_delta_depths);
                    proof_ns = (uu___4.proof_ns);
                    synth_hook = (uu___4.synth_hook);
                    try_solve_implicits_hook =
                      (uu___4.try_solve_implicits_hook);
                    splice = (uu___4.splice);
                    mpreprocess = (uu___4.mpreprocess);
                    postprocess = (uu___4.postprocess);
                    identifier_info = (uu___4.identifier_info);
                    tc_hooks = (uu___4.tc_hooks);
                    dsenv = (uu___4.dsenv);
                    nbe = (uu___4.nbe);
                    strict_args_tab = (uu___4.strict_args_tab);
                    erasable_types_tab = (uu___4.erasable_types_tab);
                    enable_defer_to_tac = (uu___4.enable_defer_to_tac);
                    unif_allow_ref_guards = (uu___4.unif_allow_ref_guards)
                  }))
let (add_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Syntax_Syntax.tscheme -> env)
  =
  fun env1 ->
    fun m ->
      fun n ->
        fun ts ->
          let err_msg poly =
            let uu___ = FStar_Ident.string_of_lid m in
            let uu___1 = FStar_Ident.string_of_lid n in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu___ uu___1
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice") in
          let uu___ =
            (let uu___1 = exists_polymonadic_subcomp env1 m n in
             FStar_All.pipe_right uu___1 FStar_Util.is_some) ||
              (let uu___1 = exists_polymonadic_subcomp env1 n m in
               FStar_All.pipe_right uu___1 FStar_Util.is_some) in
          if uu___
          then
            let uu___1 =
              let uu___2 = err_msg true in
              (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu___2) in
            FStar_Errors.raise_error uu___1 env1.range
          else
            (let uu___2 =
               (let uu___3 = monad_leq env1 m n in
                FStar_All.pipe_right uu___3 FStar_Util.is_some) ||
                 (let uu___3 = monad_leq env1 n m in
                  FStar_All.pipe_right uu___3 FStar_Util.is_some) in
             if uu___2
             then
               let uu___3 =
                 let uu___4 = err_msg false in
                 (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu___4) in
               FStar_Errors.raise_error uu___3 env1.range
             else
               (let uu___4 = env1 in
                {
                  solver = (uu___4.solver);
                  range = (uu___4.range);
                  curmodule = (uu___4.curmodule);
                  gamma = (uu___4.gamma);
                  gamma_sig = (uu___4.gamma_sig);
                  gamma_cache = (uu___4.gamma_cache);
                  modules = (uu___4.modules);
                  expected_typ = (uu___4.expected_typ);
                  sigtab = (uu___4.sigtab);
                  attrtab = (uu___4.attrtab);
                  instantiate_imp = (uu___4.instantiate_imp);
                  effects =
                    (let uu___5 = env1.effects in
                     {
                       decls = (uu___5.decls);
                       order = (uu___5.order);
                       joins = (uu___5.joins);
                       polymonadic_binds = (uu___5.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___4.generalize);
                  letrecs = (uu___4.letrecs);
                  top_level = (uu___4.top_level);
                  check_uvars = (uu___4.check_uvars);
                  use_eq = (uu___4.use_eq);
                  use_eq_strict = (uu___4.use_eq_strict);
                  is_iface = (uu___4.is_iface);
                  admit = (uu___4.admit);
                  lax = (uu___4.lax);
                  lax_universes = (uu___4.lax_universes);
                  phase1 = (uu___4.phase1);
                  failhard = (uu___4.failhard);
                  nosynth = (uu___4.nosynth);
                  uvar_subtyping = (uu___4.uvar_subtyping);
                  tc_term = (uu___4.tc_term);
                  typeof_tot_or_gtot_term = (uu___4.typeof_tot_or_gtot_term);
                  universe_of = (uu___4.universe_of);
                  typeof_well_typed_tot_or_gtot_term =
                    (uu___4.typeof_well_typed_tot_or_gtot_term);
                  use_bv_sorts = (uu___4.use_bv_sorts);
                  qtbl_name_and_index = (uu___4.qtbl_name_and_index);
                  normalized_eff_names = (uu___4.normalized_eff_names);
                  fv_delta_depths = (uu___4.fv_delta_depths);
                  proof_ns = (uu___4.proof_ns);
                  synth_hook = (uu___4.synth_hook);
                  try_solve_implicits_hook =
                    (uu___4.try_solve_implicits_hook);
                  splice = (uu___4.splice);
                  mpreprocess = (uu___4.mpreprocess);
                  postprocess = (uu___4.postprocess);
                  identifier_info = (uu___4.identifier_info);
                  tc_hooks = (uu___4.tc_hooks);
                  dsenv = (uu___4.dsenv);
                  nbe = (uu___4.nbe);
                  strict_args_tab = (uu___4.strict_args_tab);
                  erasable_types_tab = (uu___4.erasable_types_tab);
                  enable_defer_to_tac = (uu___4.enable_defer_to_tac);
                  unif_allow_ref_guards = (uu___4.unif_allow_ref_guards)
                }))
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1 ->
    fun b ->
      let uu___ = env1 in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = (uu___.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (uu___.expected_typ);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = (uu___.use_eq);
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = (uu___.proof_ns);
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = (uu___.tc_hooks);
        dsenv = (uu___.dsenv);
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env1 ->
    fun x -> push_local_binding env1 (FStar_Syntax_Syntax.Binding_var x)
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env1 ->
    fun bvs ->
      FStar_List.fold_left (fun env2 -> fun bv -> push_bv env2 bv) env1 bvs
let (pop_bv :
  env -> (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option) =
  fun env1 ->
    match env1.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___ = env1 in
             {
               solver = (uu___.solver);
               range = (uu___.range);
               curmodule = (uu___.curmodule);
               gamma = rest;
               gamma_sig = (uu___.gamma_sig);
               gamma_cache = (uu___.gamma_cache);
               modules = (uu___.modules);
               expected_typ = (uu___.expected_typ);
               sigtab = (uu___.sigtab);
               attrtab = (uu___.attrtab);
               instantiate_imp = (uu___.instantiate_imp);
               effects = (uu___.effects);
               generalize = (uu___.generalize);
               letrecs = (uu___.letrecs);
               top_level = (uu___.top_level);
               check_uvars = (uu___.check_uvars);
               use_eq = (uu___.use_eq);
               use_eq_strict = (uu___.use_eq_strict);
               is_iface = (uu___.is_iface);
               admit = (uu___.admit);
               lax = (uu___.lax);
               lax_universes = (uu___.lax_universes);
               phase1 = (uu___.phase1);
               failhard = (uu___.failhard);
               nosynth = (uu___.nosynth);
               uvar_subtyping = (uu___.uvar_subtyping);
               tc_term = (uu___.tc_term);
               typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
               universe_of = (uu___.universe_of);
               typeof_well_typed_tot_or_gtot_term =
                 (uu___.typeof_well_typed_tot_or_gtot_term);
               use_bv_sorts = (uu___.use_bv_sorts);
               qtbl_name_and_index = (uu___.qtbl_name_and_index);
               normalized_eff_names = (uu___.normalized_eff_names);
               fv_delta_depths = (uu___.fv_delta_depths);
               proof_ns = (uu___.proof_ns);
               synth_hook = (uu___.synth_hook);
               try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
               splice = (uu___.splice);
               mpreprocess = (uu___.mpreprocess);
               postprocess = (uu___.postprocess);
               identifier_info = (uu___.identifier_info);
               tc_hooks = (uu___.tc_hooks);
               dsenv = (uu___.dsenv);
               nbe = (uu___.nbe);
               strict_args_tab = (uu___.strict_args_tab);
               erasable_types_tab = (uu___.erasable_types_tab);
               enable_defer_to_tac = (uu___.enable_defer_to_tac);
               unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
             }))
    | uu___ -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1 ->
    fun bs ->
      FStar_List.fold_left
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
            let uu___1 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___1.FStar_Syntax_Syntax.index);
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
      FStar_List.fold_left
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
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu___1)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1 ->
    fun t ->
      let uu___ = env1 in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = (uu___.curmodule);
        gamma = (uu___.gamma);
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = (uu___.proof_ns);
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = (uu___.tc_hooks);
        dsenv = (uu___.dsenv);
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env1 ->
    match env1.expected_typ with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let (clear_expected_typ :
  env -> (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)) =
  fun env_ ->
    let uu___ = expected_typ env_ in
    ((let uu___1 = env_ in
      {
        solver = (uu___1.solver);
        range = (uu___1.range);
        curmodule = (uu___1.curmodule);
        gamma = (uu___1.gamma);
        gamma_sig = (uu___1.gamma_sig);
        gamma_cache = (uu___1.gamma_cache);
        modules = (uu___1.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1.sigtab);
        attrtab = (uu___1.attrtab);
        instantiate_imp = (uu___1.instantiate_imp);
        effects = (uu___1.effects);
        generalize = (uu___1.generalize);
        letrecs = (uu___1.letrecs);
        top_level = (uu___1.top_level);
        check_uvars = (uu___1.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1.use_eq_strict);
        is_iface = (uu___1.is_iface);
        admit = (uu___1.admit);
        lax = (uu___1.lax);
        lax_universes = (uu___1.lax_universes);
        phase1 = (uu___1.phase1);
        failhard = (uu___1.failhard);
        nosynth = (uu___1.nosynth);
        uvar_subtyping = (uu___1.uvar_subtyping);
        tc_term = (uu___1.tc_term);
        typeof_tot_or_gtot_term = (uu___1.typeof_tot_or_gtot_term);
        universe_of = (uu___1.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___1.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___1.use_bv_sorts);
        qtbl_name_and_index = (uu___1.qtbl_name_and_index);
        normalized_eff_names = (uu___1.normalized_eff_names);
        fv_delta_depths = (uu___1.fv_delta_depths);
        proof_ns = (uu___1.proof_ns);
        synth_hook = (uu___1.synth_hook);
        try_solve_implicits_hook = (uu___1.try_solve_implicits_hook);
        splice = (uu___1.splice);
        mpreprocess = (uu___1.mpreprocess);
        postprocess = (uu___1.postprocess);
        identifier_info = (uu___1.identifier_info);
        tc_hooks = (uu___1.tc_hooks);
        dsenv = (uu___1.dsenv);
        nbe = (uu___1.nbe);
        strict_args_tab = (uu___1.strict_args_tab);
        erasable_types_tab = (uu___1.erasable_types_tab);
        enable_defer_to_tac = (uu___1.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___1.unif_allow_ref_guards)
      }), uu___)
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
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu___1 FStar_List.rev
        else m.FStar_Syntax_Syntax.declarations in
      add_sigelts env1 sigs;
      (let uu___1 = env1 in
       {
         solver = (uu___1.solver);
         range = (uu___1.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1.expected_typ);
         sigtab = (uu___1.sigtab);
         attrtab = (uu___1.attrtab);
         instantiate_imp = (uu___1.instantiate_imp);
         effects = (uu___1.effects);
         generalize = (uu___1.generalize);
         letrecs = (uu___1.letrecs);
         top_level = (uu___1.top_level);
         check_uvars = (uu___1.check_uvars);
         use_eq = (uu___1.use_eq);
         use_eq_strict = (uu___1.use_eq_strict);
         is_iface = (uu___1.is_iface);
         admit = (uu___1.admit);
         lax = (uu___1.lax);
         lax_universes = (uu___1.lax_universes);
         phase1 = (uu___1.phase1);
         failhard = (uu___1.failhard);
         nosynth = (uu___1.nosynth);
         uvar_subtyping = (uu___1.uvar_subtyping);
         tc_term = (uu___1.tc_term);
         typeof_tot_or_gtot_term = (uu___1.typeof_tot_or_gtot_term);
         universe_of = (uu___1.universe_of);
         typeof_well_typed_tot_or_gtot_term =
           (uu___1.typeof_well_typed_tot_or_gtot_term);
         use_bv_sorts = (uu___1.use_bv_sorts);
         qtbl_name_and_index = (uu___1.qtbl_name_and_index);
         normalized_eff_names = (uu___1.normalized_eff_names);
         fv_delta_depths = (uu___1.fv_delta_depths);
         proof_ns = (uu___1.proof_ns);
         synth_hook = (uu___1.synth_hook);
         try_solve_implicits_hook = (uu___1.try_solve_implicits_hook);
         splice = (uu___1.splice);
         mpreprocess = (uu___1.mpreprocess);
         postprocess = (uu___1.postprocess);
         identifier_info = (uu___1.identifier_info);
         tc_hooks = (uu___1.tc_hooks);
         dsenv = (uu___1.dsenv);
         nbe = (uu___1.nbe);
         strict_args_tab = (uu___1.strict_args_tab);
         erasable_types_tab = (uu___1.erasable_types_tab);
         enable_defer_to_tac = (uu___1.enable_defer_to_tac);
         unif_allow_ref_guards = (uu___1.unif_allow_ref_guards)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1 ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu___)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.uvars t in ext out uu___3 in
          aux uu___2 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.uvars t in ext out uu___3 in
          aux uu___2 tl in
    aux no_uvs env1.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1 ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu___)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univs t in ext out uu___3 in
          aux uu___2 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univs t in ext out uu___3 in
          aux uu___2 tl in
    aux no_univs env1.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env1 ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu___ = FStar_Util.set_add uname out in aux uu___ tl
      | (FStar_Syntax_Syntax.Binding_lid (uu___, (uu___1, t)))::tl ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univnames t in ext out uu___3 in
          aux uu___2 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Free.univnames t in ext out uu___3 in
          aux uu___2 tl in
    aux no_univ_names env1.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu___1 -> []
            | FStar_Syntax_Syntax.Binding_univ uu___1 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu___ =
      let uu___1 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu___1
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu___ FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1 -> bound_vars_of_bindings env1.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1 -> binders_of_bindings env1.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu___ =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___1 ->
              match uu___1 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu___2 = FStar_Syntax_Print.bv_to_string x in
                  Prims.op_Hat "Binding_var " uu___2
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu___2 = FStar_Ident.string_of_id u in
                  Prims.op_Hat "Binding_univ " uu___2
              | FStar_Syntax_Syntax.Binding_lid (l, uu___2) ->
                  let uu___3 = FStar_Ident.string_of_lid l in
                  Prims.op_Hat "Binding_lid " uu___3)) in
    FStar_All.pipe_right uu___ (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu___1 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.op_Hat "Unfold " uu___1
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu___ ->
         fun v ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1 ->
    fun path ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([], uu___) -> true
        | (x::xs1, y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu___, uu___1) -> false in
      let uu___ =
        FStar_List.tryFind
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
        let uu___ = e in
        {
          solver = (uu___.solver);
          range = (uu___.range);
          curmodule = (uu___.curmodule);
          gamma = (uu___.gamma);
          gamma_sig = (uu___.gamma_sig);
          gamma_cache = (uu___.gamma_cache);
          modules = (uu___.modules);
          expected_typ = (uu___.expected_typ);
          sigtab = (uu___.sigtab);
          attrtab = (uu___.attrtab);
          instantiate_imp = (uu___.instantiate_imp);
          effects = (uu___.effects);
          generalize = (uu___.generalize);
          letrecs = (uu___.letrecs);
          top_level = (uu___.top_level);
          check_uvars = (uu___.check_uvars);
          use_eq = (uu___.use_eq);
          use_eq_strict = (uu___.use_eq_strict);
          is_iface = (uu___.is_iface);
          admit = (uu___.admit);
          lax = (uu___.lax);
          lax_universes = (uu___.lax_universes);
          phase1 = (uu___.phase1);
          failhard = (uu___.failhard);
          nosynth = (uu___.nosynth);
          uvar_subtyping = (uu___.uvar_subtyping);
          tc_term = (uu___.tc_term);
          typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
          universe_of = (uu___.universe_of);
          typeof_well_typed_tot_or_gtot_term =
            (uu___.typeof_well_typed_tot_or_gtot_term);
          use_bv_sorts = (uu___.use_bv_sorts);
          qtbl_name_and_index = (uu___.qtbl_name_and_index);
          normalized_eff_names = (uu___.normalized_eff_names);
          fv_delta_depths = (uu___.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___.synth_hook);
          try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
          splice = (uu___.splice);
          mpreprocess = (uu___.mpreprocess);
          postprocess = (uu___.postprocess);
          identifier_info = (uu___.identifier_info);
          tc_hooks = (uu___.tc_hooks);
          dsenv = (uu___.dsenv);
          nbe = (uu___.nbe);
          strict_args_tab = (uu___.strict_args_tab);
          erasable_types_tab = (uu___.erasable_types_tab);
          enable_defer_to_tac = (uu___.enable_defer_to_tac);
          unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___ = e in
      {
        solver = (uu___.solver);
        range = (uu___.range);
        curmodule = (uu___.curmodule);
        gamma = (uu___.gamma);
        gamma_sig = (uu___.gamma_sig);
        gamma_cache = (uu___.gamma_cache);
        modules = (uu___.modules);
        expected_typ = (uu___.expected_typ);
        sigtab = (uu___.sigtab);
        attrtab = (uu___.attrtab);
        instantiate_imp = (uu___.instantiate_imp);
        effects = (uu___.effects);
        generalize = (uu___.generalize);
        letrecs = (uu___.letrecs);
        top_level = (uu___.top_level);
        check_uvars = (uu___.check_uvars);
        use_eq = (uu___.use_eq);
        use_eq_strict = (uu___.use_eq_strict);
        is_iface = (uu___.is_iface);
        admit = (uu___.admit);
        lax = (uu___.lax);
        lax_universes = (uu___.lax_universes);
        phase1 = (uu___.phase1);
        failhard = (uu___.failhard);
        nosynth = (uu___.nosynth);
        uvar_subtyping = (uu___.uvar_subtyping);
        tc_term = (uu___.tc_term);
        typeof_tot_or_gtot_term = (uu___.typeof_tot_or_gtot_term);
        universe_of = (uu___.universe_of);
        typeof_well_typed_tot_or_gtot_term =
          (uu___.typeof_well_typed_tot_or_gtot_term);
        use_bv_sorts = (uu___.use_bv_sorts);
        qtbl_name_and_index = (uu___.qtbl_name_and_index);
        normalized_eff_names = (uu___.normalized_eff_names);
        fv_delta_depths = (uu___.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___.synth_hook);
        try_solve_implicits_hook = (uu___.try_solve_implicits_hook);
        splice = (uu___.splice);
        mpreprocess = (uu___.mpreprocess);
        postprocess = (uu___.postprocess);
        identifier_info = (uu___.identifier_info);
        tc_hooks = (uu___.tc_hooks);
        dsenv = (uu___.dsenv);
        nbe = (uu___.nbe);
        strict_args_tab = (uu___.strict_args_tab);
        erasable_types_tab = (uu___.erasable_types_tab);
        enable_defer_to_tac = (uu___.enable_defer_to_tac);
        unif_allow_ref_guards = (uu___.unif_allow_ref_guards)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu___ = FStar_Syntax_Free.names t in
      let uu___1 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu___ uu___1
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t -> let uu___ = unbound_vars e t in FStar_Util.set_is_empty uu___
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Free.names t in FStar_Util.set_is_empty uu___
let (string_of_proof_ns : env -> Prims.string) =
  fun env1 ->
    let aux uu___ =
      match uu___ with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu___2 = FStar_Ident.text_of_path p in
             Prims.op_Hat (if b then "+" else "-") uu___2) in
    let uu___ =
      let uu___1 = FStar_List.map aux env1.proof_ns in
      FStar_All.pipe_right uu___1 FStar_List.rev in
    FStar_All.pipe_right uu___ (FStar_String.concat " ")
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
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu___1 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu___1 with
                   | FStar_Pervasives_Native.Some uu___2 -> true
                   | FStar_Pervasives_Native.None -> false)))
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
          let uu___ = g in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___.FStar_TypeChecker_Common.implicits)
          }
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b -> fun g -> abstract_guard_n [b] g
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun vset ->
        fun t ->
          let uu___ = FStar_Options.defensive () in
          if uu___
          then
            let s = FStar_Syntax_Free.names t in
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu___3 in
              Prims.op_Negation uu___2 in
            (if uu___1
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Print.term_to_string t in
                   let uu___5 =
                     let uu___6 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu___6
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu___4 uu___5 in
                 (FStar_Errors.Warning_Defensive, uu___3) in
               FStar_Errors.log_issue rng uu___2
             else ())
          else ()
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun l ->
        fun t ->
          let uu___ =
            let uu___1 = FStar_Options.defensive () in
            Prims.op_Negation uu___1 in
          if uu___
          then ()
          else
            (let uu___2 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu___2 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu___ =
            let uu___1 = FStar_Options.defensive () in
            Prims.op_Negation uu___1 in
          if uu___
          then ()
          else
            (let uu___2 = bound_vars e in
             def_check_closed_in rng msg uu___2 t)
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng ->
    fun msg ->
      fun env1 ->
        fun g ->
          match g.FStar_TypeChecker_Common.guard_f with
          | FStar_TypeChecker_Common.Trivial -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env1 f
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g ->
    fun e ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___ = g in
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Syntax.as_arg e in [uu___6] in
                  (f, uu___5) in
                FStar_Syntax_Syntax.Tm_app uu___4 in
              FStar_Syntax_Syntax.mk uu___3 f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun uu___3 -> FStar_TypeChecker_Common.NonTrivial uu___3)
              uu___2 in
          {
            FStar_TypeChecker_Common.guard_f = uu___1;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___.FStar_TypeChecker_Common.implicits)
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
          let uu___ = g in
          let uu___1 =
            let uu___2 = map f in FStar_TypeChecker_Common.NonTrivial uu___2 in
          {
            FStar_TypeChecker_Common.guard_f = uu___1;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___.FStar_TypeChecker_Common.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___ = g in
          let uu___1 =
            let uu___2 = map FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu___2 in
          {
            FStar_TypeChecker_Common.guard_f = uu___1;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___ = g in
          let uu___1 =
            let uu___2 = map f in FStar_TypeChecker_Common.NonTrivial uu___2 in
          {
            FStar_TypeChecker_Common.guard_f = uu___1;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___.FStar_TypeChecker_Common.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu___ -> failwith "impossible"
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
              FStar_List.fold_right2
                (fun u ->
                   fun b ->
                     fun f2 ->
                       let uu___ = FStar_Syntax_Syntax.is_null_binder b in
                       if uu___
                       then f2
                       else
                         FStar_Syntax_Util.mk_forall u
                           b.FStar_Syntax_Syntax.binder_bv f2) us bs f in
            let uu___ = g in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___.FStar_TypeChecker_Common.implicits)
            }
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun bs ->
      fun f ->
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               let uu___ = FStar_Syntax_Syntax.is_null_binder b in
               if uu___
               then f1
               else
                 (let u =
                    env1.universe_of env1
                      (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    b.FStar_Syntax_Syntax.binder_bv f1)) bs f
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env1 ->
    fun binders ->
      fun g ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___ = g in
            let uu___1 =
              let uu___2 = close_forall env1 binders f in
              FStar_TypeChecker_Common.NonTrivial uu___2 in
            {
              FStar_TypeChecker_Common.guard_f = uu___1;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___.FStar_TypeChecker_Common.implicits)
            }
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            FStar_Syntax_Syntax.ctx_uvar_meta_t
              FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
                FStar_Range.range) Prims.list * guard_t))
  =
  fun reason ->
    fun r ->
      fun env1 ->
        fun k ->
          fun should_check ->
            fun meta ->
              let uu___ =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
              match uu___ with
              | FStar_Pervasives_Native.Some (uu___1::(tm, uu___2)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos in
                  (t, [], trivial_guard)
              | uu___1 ->
                  let binders = all_binders env1 in
                  let gamma = env1.gamma in
                  let ctx_uvar =
                    let uu___2 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu___2;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    } in
                  (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                     true gamma binders;
                   (let t =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uvar
                           (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                        r in
                    let imp =
                      {
                        FStar_TypeChecker_Common.imp_reason = reason;
                        FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                        FStar_TypeChecker_Common.imp_tm = t;
                        FStar_TypeChecker_Common.imp_range = r
                      } in
                    (let uu___4 =
                       debug env1 (FStar_Options.Other "ImplicitTrace") in
                     if uu___4
                     then
                       let uu___5 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu___5
                     else ());
                    (let g =
                       let uu___4 = trivial_guard in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___4.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___4.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___4.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___4.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits = [imp]
                       } in
                     (t, [(ctx_uvar, r)], g))))
let (uvars_for_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.subst_t ->
        (FStar_Syntax_Syntax.binder -> Prims.string) ->
          FStar_Range.range ->
            (FStar_Syntax_Syntax.term Prims.list * guard_t))
  =
  fun env1 ->
    fun bs ->
      fun substs ->
        fun reason ->
          fun r ->
            let uu___ =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu___1 ->
                      fun b ->
                        match uu___1 with
                        | (substs1, uvars, g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                            let uu___2 =
                              match ((b.FStar_Syntax_Syntax.binder_qual),
                                      (b.FStar_Syntax_Syntax.binder_attrs))
                              with
                              | (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Meta t), []) ->
                                  let uu___3 =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 = FStar_Dyn.mkdyn env1 in
                                        (uu___6, t) in
                                      FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                        uu___5 in
                                    FStar_Pervasives_Native.Some uu___4 in
                                  (uu___3, false)
                              | (uu___3, t::uu___4) ->
                                  ((FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         t)), true)
                              | uu___3 ->
                                  (FStar_Pervasives_Native.None, false) in
                            (match uu___2 with
                             | (ctx_uvar_meta_t, strict) ->
                                 let uu___3 =
                                   let uu___4 = reason b in
                                   new_implicit_var_aux uu___4 r env1 sort
                                     (if strict
                                      then FStar_Syntax_Syntax.Strict
                                      else FStar_Syntax_Syntax.Allow_untyped)
                                     ctx_uvar_meta_t in
                                 (match uu___3 with
                                  | (t, l_ctx_uvars, g_t) ->
                                      ((let uu___5 =
                                          FStar_All.pipe_left (debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsEqns") in
                                        if uu___5
                                        then
                                          FStar_List.iter
                                            (fun uu___6 ->
                                               match uu___6 with
                                               | (ctx_uvar, uu___7) ->
                                                   let uu___8 =
                                                     FStar_Syntax_Print.ctx_uvar_to_string_no_reason
                                                       ctx_uvar in
                                                   FStar_Util.print1
                                                     "Layered Effect uvar : %s\n"
                                                     uu___8) l_ctx_uvars
                                        else ());
                                       (let uu___5 = conj_guard g g_t in
                                        ((FStar_List.append substs1
                                            [FStar_Syntax_Syntax.NT
                                               ((b.FStar_Syntax_Syntax.binder_bv),
                                                 t)]),
                                          (FStar_List.append uvars [t]),
                                          uu___5))))))
                   (substs, [], trivial_guard)) in
            FStar_All.pipe_right uu___
              (fun uu___1 ->
                 match uu___1 with | (uu___2, uvars, g) -> (uvars, g))
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Range.range -> FStar_Syntax_Syntax.typ)
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
                FStar_All.pipe_right uu___ FStar_Util.must in
              let uu___ = inst_tscheme_with post_ts [u] in
              match uu___ with
              | (uu___1, post) ->
                  let uu___2 =
                    let uu___3 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                    [uu___3] in
                  FStar_Syntax_Syntax.mk_Tm_app post uu___2 r in
            let uu___ =
              let uu___1 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg in
              [uu___1] in
            FStar_Syntax_Syntax.mk_Tm_app wp uu___ r
let (dummy_solver : solver_t) =
  {
    init = (fun uu___ -> ());
    push = (fun uu___ -> ());
    pop = (fun uu___ -> ());
    snapshot =
      (fun uu___ -> ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu___ -> fun uu___1 -> ());
    encode_sig = (fun uu___ -> fun uu___1 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu___ = let uu___1 = FStar_Options.peek () in (e, g, uu___1) in
           [uu___]);
    solve = (fun uu___ -> fun uu___1 -> fun uu___2 -> ());
    finish = (fun uu___ -> ());
    refresh = (fun uu___ -> ())
  }
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
        FStar_Util.find_opt
          (fun uu___1 ->
             match uu___1 with
             | (lbname', uu___2, uu___3, uu___4) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
      match uu___ with
      | FStar_Pervasives_Native.Some (uu___1, arity, uu___2, uu___3) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None