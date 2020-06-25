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
  fun projectee -> match projectee with | Beta -> true | uu____107 -> false
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____118 -> false
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____129 -> false
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____140 -> false
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Exclude _0 -> true | uu____152 -> false
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee -> match projectee with | Exclude _0 -> _0
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____170 -> false
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____181 -> false
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____192 -> false
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding -> true | uu____203 -> false
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Inlining -> true | uu____214 -> false
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee ->
    match projectee with | DoNotUnfoldPureLets -> true | uu____225 -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu____237 -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____258 -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____285 -> false
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____312 -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldTac -> true | uu____336 -> false
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PureSubtermsWithinComputations -> true
    | uu____347 -> false
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Simplify -> true | uu____358 -> false
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | EraseUniverses -> true | uu____369 -> false
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowUnboundUniverses -> true | uu____380 -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____391 -> false
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CompressUvars -> true | uu____402 -> false
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee ->
    match projectee with | NoFullNorm -> true | uu____413 -> false
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckNoUvars -> true | uu____424 -> false
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu____435 -> false
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Unascribe -> true | uu____446 -> false
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____457 -> false
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ForExtraction -> true | uu____468 -> false
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
      | uu____529 -> false
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | NoDelta -> true | uu____555 -> false
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | InliningDelta -> true | uu____566 -> false
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding_only -> true | uu____577 -> false
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Unfold _0 -> true | uu____589 -> false
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee -> match projectee with | Unfold _0 -> _0
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
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
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t
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
  enable_defer_to_tac: Prims.bool }
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
      (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either -> unit
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> solver
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> range
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> curmodule
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> gamma
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> gamma_sig
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> gamma_cache
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> modules
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> expected_typ
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> sigtab
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> attrtab
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> instantiate_imp
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> effects1
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> generalize
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> letrecs
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> top_level
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> check_uvars
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> use_eq
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> use_eq_strict
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> is_iface
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> admit
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> lax
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> lax_universes
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> phase1
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> failhard
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> nosynth
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> uvar_subtyping
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> tc_term
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> type_of
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> universe_of
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> check_type_of
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> use_bv_sorts
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> qtbl_name_and_index
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> normalized_eff_names
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> fv_delta_depths
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> proof_ns
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> synth_hook
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> try_solve_implicits_hook
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> splice
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> mpreprocess
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> postprocess
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> identifier_info
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> tc_hooks
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> dsenv
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
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> nbe
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> strict_args_tab
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> erasable_types_tab
let (__proj__Mkenv__item__enable_defer_to_tac : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> enable_defer_to_tac
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
      (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either -> unit)
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
           (fun uu___0_14633 ->
              match uu___0_14633 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14636 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst uu____14636 in
                  let uu____14637 =
                    let uu____14638 = FStar_Syntax_Subst.compress y in
                    uu____14638.FStar_Syntax_Syntax.n in
                  (match uu____14637 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14642 =
                         let uu___330_14643 = y1 in
                         let uu____14644 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___330_14643.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___330_14643.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14644
                         } in
                       FStar_Syntax_Syntax.Binding_var uu____14642
                   | uu____14647 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst ->
    fun env1 ->
      let uu___336_14661 = env1 in
      let uu____14662 = rename_gamma subst env1.gamma in
      {
        solver = (uu___336_14661.solver);
        range = (uu___336_14661.range);
        curmodule = (uu___336_14661.curmodule);
        gamma = uu____14662;
        gamma_sig = (uu___336_14661.gamma_sig);
        gamma_cache = (uu___336_14661.gamma_cache);
        modules = (uu___336_14661.modules);
        expected_typ = (uu___336_14661.expected_typ);
        sigtab = (uu___336_14661.sigtab);
        attrtab = (uu___336_14661.attrtab);
        instantiate_imp = (uu___336_14661.instantiate_imp);
        effects = (uu___336_14661.effects);
        generalize = (uu___336_14661.generalize);
        letrecs = (uu___336_14661.letrecs);
        top_level = (uu___336_14661.top_level);
        check_uvars = (uu___336_14661.check_uvars);
        use_eq = (uu___336_14661.use_eq);
        use_eq_strict = (uu___336_14661.use_eq_strict);
        is_iface = (uu___336_14661.is_iface);
        admit = (uu___336_14661.admit);
        lax = (uu___336_14661.lax);
        lax_universes = (uu___336_14661.lax_universes);
        phase1 = (uu___336_14661.phase1);
        failhard = (uu___336_14661.failhard);
        nosynth = (uu___336_14661.nosynth);
        uvar_subtyping = (uu___336_14661.uvar_subtyping);
        tc_term = (uu___336_14661.tc_term);
        type_of = (uu___336_14661.type_of);
        universe_of = (uu___336_14661.universe_of);
        check_type_of = (uu___336_14661.check_type_of);
        use_bv_sorts = (uu___336_14661.use_bv_sorts);
        qtbl_name_and_index = (uu___336_14661.qtbl_name_and_index);
        normalized_eff_names = (uu___336_14661.normalized_eff_names);
        fv_delta_depths = (uu___336_14661.fv_delta_depths);
        proof_ns = (uu___336_14661.proof_ns);
        synth_hook = (uu___336_14661.synth_hook);
        try_solve_implicits_hook = (uu___336_14661.try_solve_implicits_hook);
        splice = (uu___336_14661.splice);
        mpreprocess = (uu___336_14661.mpreprocess);
        postprocess = (uu___336_14661.postprocess);
        identifier_info = (uu___336_14661.identifier_info);
        tc_hooks = (uu___336_14661.tc_hooks);
        dsenv = (uu___336_14661.dsenv);
        nbe = (uu___336_14661.nbe);
        strict_args_tab = (uu___336_14661.strict_args_tab);
        erasable_types_tab = (uu___336_14661.erasable_types_tab);
        enable_defer_to_tac = (uu___336_14661.enable_defer_to_tac)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14670 -> fun uu____14671 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env1 -> env1.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___343_14693 = env1 in
      {
        solver = (uu___343_14693.solver);
        range = (uu___343_14693.range);
        curmodule = (uu___343_14693.curmodule);
        gamma = (uu___343_14693.gamma);
        gamma_sig = (uu___343_14693.gamma_sig);
        gamma_cache = (uu___343_14693.gamma_cache);
        modules = (uu___343_14693.modules);
        expected_typ = (uu___343_14693.expected_typ);
        sigtab = (uu___343_14693.sigtab);
        attrtab = (uu___343_14693.attrtab);
        instantiate_imp = (uu___343_14693.instantiate_imp);
        effects = (uu___343_14693.effects);
        generalize = (uu___343_14693.generalize);
        letrecs = (uu___343_14693.letrecs);
        top_level = (uu___343_14693.top_level);
        check_uvars = (uu___343_14693.check_uvars);
        use_eq = (uu___343_14693.use_eq);
        use_eq_strict = (uu___343_14693.use_eq_strict);
        is_iface = (uu___343_14693.is_iface);
        admit = (uu___343_14693.admit);
        lax = (uu___343_14693.lax);
        lax_universes = (uu___343_14693.lax_universes);
        phase1 = (uu___343_14693.phase1);
        failhard = (uu___343_14693.failhard);
        nosynth = (uu___343_14693.nosynth);
        uvar_subtyping = (uu___343_14693.uvar_subtyping);
        tc_term = (uu___343_14693.tc_term);
        type_of = (uu___343_14693.type_of);
        universe_of = (uu___343_14693.universe_of);
        check_type_of = (uu___343_14693.check_type_of);
        use_bv_sorts = (uu___343_14693.use_bv_sorts);
        qtbl_name_and_index = (uu___343_14693.qtbl_name_and_index);
        normalized_eff_names = (uu___343_14693.normalized_eff_names);
        fv_delta_depths = (uu___343_14693.fv_delta_depths);
        proof_ns = (uu___343_14693.proof_ns);
        synth_hook = (uu___343_14693.synth_hook);
        try_solve_implicits_hook = (uu___343_14693.try_solve_implicits_hook);
        splice = (uu___343_14693.splice);
        mpreprocess = (uu___343_14693.mpreprocess);
        postprocess = (uu___343_14693.postprocess);
        identifier_info = (uu___343_14693.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___343_14693.dsenv);
        nbe = (uu___343_14693.nbe);
        strict_args_tab = (uu___343_14693.strict_args_tab);
        erasable_types_tab = (uu___343_14693.erasable_types_tab);
        enable_defer_to_tac = (uu___343_14693.enable_defer_to_tac)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___347_14705 = e in
      let uu____14706 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
      {
        solver = (uu___347_14705.solver);
        range = (uu___347_14705.range);
        curmodule = (uu___347_14705.curmodule);
        gamma = (uu___347_14705.gamma);
        gamma_sig = (uu___347_14705.gamma_sig);
        gamma_cache = (uu___347_14705.gamma_cache);
        modules = (uu___347_14705.modules);
        expected_typ = (uu___347_14705.expected_typ);
        sigtab = (uu___347_14705.sigtab);
        attrtab = (uu___347_14705.attrtab);
        instantiate_imp = (uu___347_14705.instantiate_imp);
        effects = (uu___347_14705.effects);
        generalize = (uu___347_14705.generalize);
        letrecs = (uu___347_14705.letrecs);
        top_level = (uu___347_14705.top_level);
        check_uvars = (uu___347_14705.check_uvars);
        use_eq = (uu___347_14705.use_eq);
        use_eq_strict = (uu___347_14705.use_eq_strict);
        is_iface = (uu___347_14705.is_iface);
        admit = (uu___347_14705.admit);
        lax = (uu___347_14705.lax);
        lax_universes = (uu___347_14705.lax_universes);
        phase1 = (uu___347_14705.phase1);
        failhard = (uu___347_14705.failhard);
        nosynth = (uu___347_14705.nosynth);
        uvar_subtyping = (uu___347_14705.uvar_subtyping);
        tc_term = (uu___347_14705.tc_term);
        type_of = (uu___347_14705.type_of);
        universe_of = (uu___347_14705.universe_of);
        check_type_of = (uu___347_14705.check_type_of);
        use_bv_sorts = (uu___347_14705.use_bv_sorts);
        qtbl_name_and_index = (uu___347_14705.qtbl_name_and_index);
        normalized_eff_names = (uu___347_14705.normalized_eff_names);
        fv_delta_depths = (uu___347_14705.fv_delta_depths);
        proof_ns = (uu___347_14705.proof_ns);
        synth_hook = (uu___347_14705.synth_hook);
        try_solve_implicits_hook = (uu___347_14705.try_solve_implicits_hook);
        splice = (uu___347_14705.splice);
        mpreprocess = (uu___347_14705.mpreprocess);
        postprocess = (uu___347_14705.postprocess);
        identifier_info = (uu___347_14705.identifier_info);
        tc_hooks = (uu___347_14705.tc_hooks);
        dsenv = uu____14706;
        nbe = (uu___347_14705.nbe);
        strict_args_tab = (uu___347_14705.strict_args_tab);
        erasable_types_tab = (uu___347_14705.erasable_types_tab);
        enable_defer_to_tac = (uu___347_14705.enable_defer_to_tac)
      }
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e -> FStar_Syntax_DsEnv.dep_graph e.dsenv
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1 ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14723 = FStar_Ident.string_of_lid env1.curmodule in
       FStar_Options.should_verify uu____14723)
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d ->
    fun q ->
      match (d, q) with
      | (NoDelta, uu____14738) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____14741,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____14743, FStar_Syntax_Syntax.Visible_default) -> true
      | (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu____14746 -> false
let (default_table_size : Prims.int) = (Prims.of_int (200))
let new_sigtab : 'uuuuuu14760 . unit -> 'uuuuuu14760 FStar_Util.smap =
  fun uu____14767 -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'uuuuuu14773 . unit -> 'uuuuuu14773 FStar_Util.smap =
  fun uu____14780 -> FStar_Util.smap_create (Prims.of_int (100))
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
           guard_t))
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
        ->
        (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
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
      fun type_of ->
        fun universe_of ->
          fun check_type_of ->
            fun solver ->
              fun module_lid ->
                fun nbe ->
                  let uu____14918 = new_gamma_cache () in
                  let uu____14921 = new_sigtab () in
                  let uu____14924 = new_sigtab () in
                  let uu____14931 =
                    let uu____14946 =
                      FStar_Util.smap_create (Prims.of_int (10)) in
                    (uu____14946, FStar_Pervasives_Native.None) in
                  let uu____14967 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu____14971 =
                    FStar_Util.smap_create (Prims.of_int (50)) in
                  let uu____14975 = FStar_Options.using_facts_from () in
                  let uu____14976 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty in
                  let uu____14979 = FStar_Syntax_DsEnv.empty_env deps in
                  let uu____14980 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu____14994 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14918;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14921;
                    attrtab = uu____14924;
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
                    type_of;
                    universe_of;
                    check_type_of;
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu____14931;
                    normalized_eff_names = uu____14967;
                    fv_delta_depths = uu____14971;
                    proof_ns = uu____14975;
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
                    identifier_info = uu____14976;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14979;
                    nbe;
                    strict_args_tab = uu____14980;
                    erasable_types_tab = uu____14994;
                    enable_defer_to_tac = true
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
  fun uu____15197 ->
    let uu____15198 = FStar_ST.op_Bang query_indices in
    match uu____15198 with
    | [] -> failwith "Empty query indices!"
    | uu____15253 ->
        let uu____15263 =
          let uu____15273 =
            let uu____15281 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____15281 in
          let uu____15335 = FStar_ST.op_Bang query_indices in uu____15273 ::
            uu____15335 in
        FStar_ST.op_Colon_Equals query_indices uu____15263
let (pop_query_indices : unit -> unit) =
  fun uu____15431 ->
    let uu____15432 = FStar_ST.op_Bang query_indices in
    match uu____15432 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15559 ->
    FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15596 ->
    match uu____15596 with
    | (l, n) ->
        let uu____15606 = FStar_ST.op_Bang query_indices in
        (match uu____15606 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15728 -> failwith "Empty query indices")
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15751 ->
    let uu____15752 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____15752
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env1 ->
    (let uu____15820 =
       let uu____15823 = FStar_ST.op_Bang stack in env1 :: uu____15823 in
     FStar_ST.op_Colon_Equals stack uu____15820);
    (let uu___421_15872 = env1 in
     let uu____15873 = FStar_Util.smap_copy (gamma_cache env1) in
     let uu____15876 = FStar_Util.smap_copy (sigtab env1) in
     let uu____15879 = FStar_Util.smap_copy (attrtab env1) in
     let uu____15886 =
       let uu____15901 =
         let uu____15905 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu____15905 in
       let uu____15937 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu____15901, uu____15937) in
     let uu____15986 = FStar_Util.smap_copy env1.normalized_eff_names in
     let uu____15989 = FStar_Util.smap_copy env1.fv_delta_depths in
     let uu____15992 =
       let uu____15995 = FStar_ST.op_Bang env1.identifier_info in
       FStar_Util.mk_ref uu____15995 in
     let uu____16015 = FStar_Util.smap_copy env1.strict_args_tab in
     let uu____16028 = FStar_Util.smap_copy env1.erasable_types_tab in
     {
       solver = (uu___421_15872.solver);
       range = (uu___421_15872.range);
       curmodule = (uu___421_15872.curmodule);
       gamma = (uu___421_15872.gamma);
       gamma_sig = (uu___421_15872.gamma_sig);
       gamma_cache = uu____15873;
       modules = (uu___421_15872.modules);
       expected_typ = (uu___421_15872.expected_typ);
       sigtab = uu____15876;
       attrtab = uu____15879;
       instantiate_imp = (uu___421_15872.instantiate_imp);
       effects = (uu___421_15872.effects);
       generalize = (uu___421_15872.generalize);
       letrecs = (uu___421_15872.letrecs);
       top_level = (uu___421_15872.top_level);
       check_uvars = (uu___421_15872.check_uvars);
       use_eq = (uu___421_15872.use_eq);
       use_eq_strict = (uu___421_15872.use_eq_strict);
       is_iface = (uu___421_15872.is_iface);
       admit = (uu___421_15872.admit);
       lax = (uu___421_15872.lax);
       lax_universes = (uu___421_15872.lax_universes);
       phase1 = (uu___421_15872.phase1);
       failhard = (uu___421_15872.failhard);
       nosynth = (uu___421_15872.nosynth);
       uvar_subtyping = (uu___421_15872.uvar_subtyping);
       tc_term = (uu___421_15872.tc_term);
       type_of = (uu___421_15872.type_of);
       universe_of = (uu___421_15872.universe_of);
       check_type_of = (uu___421_15872.check_type_of);
       use_bv_sorts = (uu___421_15872.use_bv_sorts);
       qtbl_name_and_index = uu____15886;
       normalized_eff_names = uu____15986;
       fv_delta_depths = uu____15989;
       proof_ns = (uu___421_15872.proof_ns);
       synth_hook = (uu___421_15872.synth_hook);
       try_solve_implicits_hook = (uu___421_15872.try_solve_implicits_hook);
       splice = (uu___421_15872.splice);
       mpreprocess = (uu___421_15872.mpreprocess);
       postprocess = (uu___421_15872.postprocess);
       identifier_info = uu____15992;
       tc_hooks = (uu___421_15872.tc_hooks);
       dsenv = (uu___421_15872.dsenv);
       nbe = (uu___421_15872.nbe);
       strict_args_tab = uu____16015;
       erasable_types_tab = uu____16028;
       enable_defer_to_tac = (uu___421_15872.enable_defer_to_tac)
     })
let (pop_stack : unit -> env) =
  fun uu____16038 ->
    let uu____16039 = FStar_ST.op_Bang stack in
    match uu____16039 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____16093 -> failwith "Impossible: Too many pops"
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push_stack stack env1
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop_stack stack depth
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1 ->
    fun msg ->
      FStar_Util.atomically
        (fun uu____16183 ->
           let uu____16184 = snapshot_stack env1 in
           match uu____16184 with
           | (stack_depth, env2) ->
               let uu____16218 = snapshot_query_indices () in
               (match uu____16218 with
                | (query_indices_depth, ()) ->
                    let uu____16251 = (env2.solver).snapshot msg in
                    (match uu____16251 with
                     | (solver_depth, ()) ->
                         let uu____16308 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv in
                         (match uu____16308 with
                          | (dsenv_depth, dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___446_16375 = env2 in
                                 {
                                   solver = (uu___446_16375.solver);
                                   range = (uu___446_16375.range);
                                   curmodule = (uu___446_16375.curmodule);
                                   gamma = (uu___446_16375.gamma);
                                   gamma_sig = (uu___446_16375.gamma_sig);
                                   gamma_cache = (uu___446_16375.gamma_cache);
                                   modules = (uu___446_16375.modules);
                                   expected_typ =
                                     (uu___446_16375.expected_typ);
                                   sigtab = (uu___446_16375.sigtab);
                                   attrtab = (uu___446_16375.attrtab);
                                   instantiate_imp =
                                     (uu___446_16375.instantiate_imp);
                                   effects = (uu___446_16375.effects);
                                   generalize = (uu___446_16375.generalize);
                                   letrecs = (uu___446_16375.letrecs);
                                   top_level = (uu___446_16375.top_level);
                                   check_uvars = (uu___446_16375.check_uvars);
                                   use_eq = (uu___446_16375.use_eq);
                                   use_eq_strict =
                                     (uu___446_16375.use_eq_strict);
                                   is_iface = (uu___446_16375.is_iface);
                                   admit = (uu___446_16375.admit);
                                   lax = (uu___446_16375.lax);
                                   lax_universes =
                                     (uu___446_16375.lax_universes);
                                   phase1 = (uu___446_16375.phase1);
                                   failhard = (uu___446_16375.failhard);
                                   nosynth = (uu___446_16375.nosynth);
                                   uvar_subtyping =
                                     (uu___446_16375.uvar_subtyping);
                                   tc_term = (uu___446_16375.tc_term);
                                   type_of = (uu___446_16375.type_of);
                                   universe_of = (uu___446_16375.universe_of);
                                   check_type_of =
                                     (uu___446_16375.check_type_of);
                                   use_bv_sorts =
                                     (uu___446_16375.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___446_16375.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___446_16375.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___446_16375.fv_delta_depths);
                                   proof_ns = (uu___446_16375.proof_ns);
                                   synth_hook = (uu___446_16375.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___446_16375.try_solve_implicits_hook);
                                   splice = (uu___446_16375.splice);
                                   mpreprocess = (uu___446_16375.mpreprocess);
                                   postprocess = (uu___446_16375.postprocess);
                                   identifier_info =
                                     (uu___446_16375.identifier_info);
                                   tc_hooks = (uu___446_16375.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___446_16375.nbe);
                                   strict_args_tab =
                                     (uu___446_16375.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___446_16375.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___446_16375.enable_defer_to_tac)
                                 }))))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
          (fun uu____16409 ->
             let uu____16410 =
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
             match uu____16410 with
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
                             ((let uu____16590 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1 in
                               FStar_Common.runtime_assert uu____16590
                                 "Inconsistent stack state");
                              tcenv))))))
let (push : env -> Prims.string -> env) =
  fun env1 ->
    fun msg ->
      let uu____16606 = snapshot env1 msg in
      FStar_Pervasives_Native.snd uu____16606
let (pop : env -> Prims.string -> env) =
  fun env1 ->
    fun msg -> rollback env1.solver msg FStar_Pervasives_Native.None
let (incr_query_index : env -> env) =
  fun env1 ->
    let qix = peek_query_indices () in
    match env1.qtbl_name_and_index with
    | (uu____16638, FStar_Pervasives_Native.None) -> env1
    | (tbl, FStar_Pervasives_Native.Some (l, n)) ->
        let uu____16680 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16710 ->
                  match uu____16710 with
                  | (m, uu____16718) -> FStar_Ident.lid_equals l m)) in
        (match uu____16680 with
         | FStar_Pervasives_Native.None ->
             let next = n + Prims.int_one in
             (add_query_index (l, next);
              (let uu____16732 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu____16732 next);
              (let uu___491_16735 = env1 in
               {
                 solver = (uu___491_16735.solver);
                 range = (uu___491_16735.range);
                 curmodule = (uu___491_16735.curmodule);
                 gamma = (uu___491_16735.gamma);
                 gamma_sig = (uu___491_16735.gamma_sig);
                 gamma_cache = (uu___491_16735.gamma_cache);
                 modules = (uu___491_16735.modules);
                 expected_typ = (uu___491_16735.expected_typ);
                 sigtab = (uu___491_16735.sigtab);
                 attrtab = (uu___491_16735.attrtab);
                 instantiate_imp = (uu___491_16735.instantiate_imp);
                 effects = (uu___491_16735.effects);
                 generalize = (uu___491_16735.generalize);
                 letrecs = (uu___491_16735.letrecs);
                 top_level = (uu___491_16735.top_level);
                 check_uvars = (uu___491_16735.check_uvars);
                 use_eq = (uu___491_16735.use_eq);
                 use_eq_strict = (uu___491_16735.use_eq_strict);
                 is_iface = (uu___491_16735.is_iface);
                 admit = (uu___491_16735.admit);
                 lax = (uu___491_16735.lax);
                 lax_universes = (uu___491_16735.lax_universes);
                 phase1 = (uu___491_16735.phase1);
                 failhard = (uu___491_16735.failhard);
                 nosynth = (uu___491_16735.nosynth);
                 uvar_subtyping = (uu___491_16735.uvar_subtyping);
                 tc_term = (uu___491_16735.tc_term);
                 type_of = (uu___491_16735.type_of);
                 universe_of = (uu___491_16735.universe_of);
                 check_type_of = (uu___491_16735.check_type_of);
                 use_bv_sorts = (uu___491_16735.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___491_16735.normalized_eff_names);
                 fv_delta_depths = (uu___491_16735.fv_delta_depths);
                 proof_ns = (uu___491_16735.proof_ns);
                 synth_hook = (uu___491_16735.synth_hook);
                 try_solve_implicits_hook =
                   (uu___491_16735.try_solve_implicits_hook);
                 splice = (uu___491_16735.splice);
                 mpreprocess = (uu___491_16735.mpreprocess);
                 postprocess = (uu___491_16735.postprocess);
                 identifier_info = (uu___491_16735.identifier_info);
                 tc_hooks = (uu___491_16735.tc_hooks);
                 dsenv = (uu___491_16735.dsenv);
                 nbe = (uu___491_16735.nbe);
                 strict_args_tab = (uu___491_16735.strict_args_tab);
                 erasable_types_tab = (uu___491_16735.erasable_types_tab);
                 enable_defer_to_tac = (uu___491_16735.enable_defer_to_tac)
               }))
         | FStar_Pervasives_Native.Some (uu____16752, m) ->
             let next = m + Prims.int_one in
             (add_query_index (l, next);
              (let uu____16767 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu____16767 next);
              (let uu___500_16770 = env1 in
               {
                 solver = (uu___500_16770.solver);
                 range = (uu___500_16770.range);
                 curmodule = (uu___500_16770.curmodule);
                 gamma = (uu___500_16770.gamma);
                 gamma_sig = (uu___500_16770.gamma_sig);
                 gamma_cache = (uu___500_16770.gamma_cache);
                 modules = (uu___500_16770.modules);
                 expected_typ = (uu___500_16770.expected_typ);
                 sigtab = (uu___500_16770.sigtab);
                 attrtab = (uu___500_16770.attrtab);
                 instantiate_imp = (uu___500_16770.instantiate_imp);
                 effects = (uu___500_16770.effects);
                 generalize = (uu___500_16770.generalize);
                 letrecs = (uu___500_16770.letrecs);
                 top_level = (uu___500_16770.top_level);
                 check_uvars = (uu___500_16770.check_uvars);
                 use_eq = (uu___500_16770.use_eq);
                 use_eq_strict = (uu___500_16770.use_eq_strict);
                 is_iface = (uu___500_16770.is_iface);
                 admit = (uu___500_16770.admit);
                 lax = (uu___500_16770.lax);
                 lax_universes = (uu___500_16770.lax_universes);
                 phase1 = (uu___500_16770.phase1);
                 failhard = (uu___500_16770.failhard);
                 nosynth = (uu___500_16770.nosynth);
                 uvar_subtyping = (uu___500_16770.uvar_subtyping);
                 tc_term = (uu___500_16770.tc_term);
                 type_of = (uu___500_16770.type_of);
                 universe_of = (uu___500_16770.universe_of);
                 check_type_of = (uu___500_16770.check_type_of);
                 use_bv_sorts = (uu___500_16770.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___500_16770.normalized_eff_names);
                 fv_delta_depths = (uu___500_16770.fv_delta_depths);
                 proof_ns = (uu___500_16770.proof_ns);
                 synth_hook = (uu___500_16770.synth_hook);
                 try_solve_implicits_hook =
                   (uu___500_16770.try_solve_implicits_hook);
                 splice = (uu___500_16770.splice);
                 mpreprocess = (uu___500_16770.mpreprocess);
                 postprocess = (uu___500_16770.postprocess);
                 identifier_info = (uu___500_16770.identifier_info);
                 tc_hooks = (uu___500_16770.tc_hooks);
                 dsenv = (uu___500_16770.dsenv);
                 nbe = (uu___500_16770.nbe);
                 strict_args_tab = (uu___500_16770.strict_args_tab);
                 erasable_types_tab = (uu___500_16770.erasable_types_tab);
                 enable_defer_to_tac = (uu___500_16770.enable_defer_to_tac)
               })))
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____16799 = FStar_Ident.string_of_lid env1.curmodule in
      FStar_Options.debug_at_level uu____16799 l
let (set_range : env -> FStar_Range.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___507_16815 = e in
         {
           solver = (uu___507_16815.solver);
           range = r;
           curmodule = (uu___507_16815.curmodule);
           gamma = (uu___507_16815.gamma);
           gamma_sig = (uu___507_16815.gamma_sig);
           gamma_cache = (uu___507_16815.gamma_cache);
           modules = (uu___507_16815.modules);
           expected_typ = (uu___507_16815.expected_typ);
           sigtab = (uu___507_16815.sigtab);
           attrtab = (uu___507_16815.attrtab);
           instantiate_imp = (uu___507_16815.instantiate_imp);
           effects = (uu___507_16815.effects);
           generalize = (uu___507_16815.generalize);
           letrecs = (uu___507_16815.letrecs);
           top_level = (uu___507_16815.top_level);
           check_uvars = (uu___507_16815.check_uvars);
           use_eq = (uu___507_16815.use_eq);
           use_eq_strict = (uu___507_16815.use_eq_strict);
           is_iface = (uu___507_16815.is_iface);
           admit = (uu___507_16815.admit);
           lax = (uu___507_16815.lax);
           lax_universes = (uu___507_16815.lax_universes);
           phase1 = (uu___507_16815.phase1);
           failhard = (uu___507_16815.failhard);
           nosynth = (uu___507_16815.nosynth);
           uvar_subtyping = (uu___507_16815.uvar_subtyping);
           tc_term = (uu___507_16815.tc_term);
           type_of = (uu___507_16815.type_of);
           universe_of = (uu___507_16815.universe_of);
           check_type_of = (uu___507_16815.check_type_of);
           use_bv_sorts = (uu___507_16815.use_bv_sorts);
           qtbl_name_and_index = (uu___507_16815.qtbl_name_and_index);
           normalized_eff_names = (uu___507_16815.normalized_eff_names);
           fv_delta_depths = (uu___507_16815.fv_delta_depths);
           proof_ns = (uu___507_16815.proof_ns);
           synth_hook = (uu___507_16815.synth_hook);
           try_solve_implicits_hook =
             (uu___507_16815.try_solve_implicits_hook);
           splice = (uu___507_16815.splice);
           mpreprocess = (uu___507_16815.mpreprocess);
           postprocess = (uu___507_16815.postprocess);
           identifier_info = (uu___507_16815.identifier_info);
           tc_hooks = (uu___507_16815.tc_hooks);
           dsenv = (uu___507_16815.dsenv);
           nbe = (uu___507_16815.nbe);
           strict_args_tab = (uu___507_16815.strict_args_tab);
           erasable_types_tab = (uu___507_16815.erasable_types_tab);
           enable_defer_to_tac = (uu___507_16815.enable_defer_to_tac)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1 ->
    fun enabled ->
      let uu____16835 =
        let uu____16836 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____16836 enabled in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16835
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun bv ->
      fun ty ->
        let uu____16891 =
          let uu____16892 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16892 bv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16891
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun fv ->
      fun ty ->
        let uu____16947 =
          let uu____16948 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16948 fv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16947
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1 ->
    fun ty_map ->
      let uu____17003 =
        let uu____17004 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____17004 ty_map in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____17003
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1 -> env1.modules
let (current_module : env -> FStar_Ident.lident) = fun env1 -> env1.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun lid ->
      let uu___524_17068 = env1 in
      {
        solver = (uu___524_17068.solver);
        range = (uu___524_17068.range);
        curmodule = lid;
        gamma = (uu___524_17068.gamma);
        gamma_sig = (uu___524_17068.gamma_sig);
        gamma_cache = (uu___524_17068.gamma_cache);
        modules = (uu___524_17068.modules);
        expected_typ = (uu___524_17068.expected_typ);
        sigtab = (uu___524_17068.sigtab);
        attrtab = (uu___524_17068.attrtab);
        instantiate_imp = (uu___524_17068.instantiate_imp);
        effects = (uu___524_17068.effects);
        generalize = (uu___524_17068.generalize);
        letrecs = (uu___524_17068.letrecs);
        top_level = (uu___524_17068.top_level);
        check_uvars = (uu___524_17068.check_uvars);
        use_eq = (uu___524_17068.use_eq);
        use_eq_strict = (uu___524_17068.use_eq_strict);
        is_iface = (uu___524_17068.is_iface);
        admit = (uu___524_17068.admit);
        lax = (uu___524_17068.lax);
        lax_universes = (uu___524_17068.lax_universes);
        phase1 = (uu___524_17068.phase1);
        failhard = (uu___524_17068.failhard);
        nosynth = (uu___524_17068.nosynth);
        uvar_subtyping = (uu___524_17068.uvar_subtyping);
        tc_term = (uu___524_17068.tc_term);
        type_of = (uu___524_17068.type_of);
        universe_of = (uu___524_17068.universe_of);
        check_type_of = (uu___524_17068.check_type_of);
        use_bv_sorts = (uu___524_17068.use_bv_sorts);
        qtbl_name_and_index = (uu___524_17068.qtbl_name_and_index);
        normalized_eff_names = (uu___524_17068.normalized_eff_names);
        fv_delta_depths = (uu___524_17068.fv_delta_depths);
        proof_ns = (uu___524_17068.proof_ns);
        synth_hook = (uu___524_17068.synth_hook);
        try_solve_implicits_hook = (uu___524_17068.try_solve_implicits_hook);
        splice = (uu___524_17068.splice);
        mpreprocess = (uu___524_17068.mpreprocess);
        postprocess = (uu___524_17068.postprocess);
        identifier_info = (uu___524_17068.identifier_info);
        tc_hooks = (uu___524_17068.tc_hooks);
        dsenv = (uu___524_17068.dsenv);
        nbe = (uu___524_17068.nbe);
        strict_args_tab = (uu___524_17068.strict_args_tab);
        erasable_types_tab = (uu___524_17068.erasable_types_tab);
        enable_defer_to_tac = (uu___524_17068.enable_defer_to_tac)
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
      let uu____17099 = FStar_Ident.string_of_lid lid in
      FStar_Util.smap_try_find (sigtab env1) uu____17099
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu____17112 =
      let uu____17114 = FStar_Ident.string_of_lid l in
      FStar_Util.format1 "Name \"%s\" not found" uu____17114 in
    (FStar_Errors.Fatal_NameNotFound, uu____17112)
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v ->
    let uu____17129 =
      let uu____17131 = FStar_Syntax_Print.bv_to_string v in
      FStar_Util.format1 "Variable \"%s\" not found" uu____17131 in
    (FStar_Errors.Fatal_VariableNotFound, uu____17129)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____17140 ->
    let uu____17141 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
    FStar_Syntax_Syntax.U_unif uu____17141
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
      | ((formals, t), uu____17243) ->
          let vs = mk_univ_subst formals us in
          let uu____17267 = FStar_Syntax_Subst.subst vs t in
          (us, uu____17267)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17284 ->
    match uu___1_17284 with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17310 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r ->
    fun t ->
      let uu____17330 = inst_tscheme t in
      match uu____17330 with
      | (us, t1) ->
          let uu____17341 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____17341)
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
          let uu____17366 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu____17368 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17366 uu____17368 in
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
        fun uu____17395 ->
          match uu____17395 with
          | (us, t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17409 =
                    let uu____17411 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us) in
                    let uu____17415 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts) in
                    let uu____17419 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname in
                    let uu____17421 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17411 uu____17415 uu____17419 uu____17421 in
                  failwith uu____17409)
               else ();
               (let uu____17426 = inst_tscheme_with (us, t) insts in
                FStar_Pervasives_Native.snd uu____17426))
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu____17444 -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____17455 -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____17466 -> false
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1 ->
    fun l ->
      let cur = current_module env1 in
      let uu____17480 =
        let uu____17482 = FStar_Ident.nsstr l in
        let uu____17484 = FStar_Ident.string_of_lid cur in
        uu____17482 = uu____17484 in
      if uu____17480
      then Yes
      else
        (let uu____17490 =
           let uu____17492 = FStar_Ident.nsstr l in
           let uu____17494 = FStar_Ident.string_of_lid cur in
           FStar_Util.starts_with uu____17492 uu____17494 in
         if uu____17490
         then
           let lns =
             let uu____17500 = FStar_Ident.ns_of_lid l in
             let uu____17503 =
               let uu____17506 = FStar_Ident.ident_of_lid l in [uu____17506] in
             FStar_List.append uu____17500 uu____17503 in
           let cur1 =
             let uu____17510 = FStar_Ident.ns_of_lid cur in
             let uu____17513 =
               let uu____17516 = FStar_Ident.ident_of_lid cur in
               [uu____17516] in
             FStar_List.append uu____17510 uu____17513 in
           let rec aux c l1 =
             match (c, l1) with
             | ([], uu____17540) -> Maybe
             | (uu____17547, []) -> No
             | (hd::tl, hd'::tl') when
                 let uu____17566 = FStar_Ident.string_of_id hd in
                 let uu____17568 = FStar_Ident.string_of_id hd' in
                 uu____17566 = uu____17568 -> aux tl tl'
             | uu____17571 -> No in
           aux cur1 lns
         else No)
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes
      FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env1 ->
    fun lid ->
      let cur_mod = in_cur_mod env1 lid in
      let cache t =
        (let uu____17623 = FStar_Ident.string_of_lid lid in
         FStar_Util.smap_add (gamma_cache env1) uu____17623 t);
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____17667 =
            let uu____17670 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17670 in
          match uu____17667 with
          | FStar_Pervasives_Native.None ->
              let uu____17692 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17736 ->
                     match uu___2_17736 with
                     | FStar_Syntax_Syntax.Binding_lid (l, t) ->
                         let uu____17775 = FStar_Ident.lid_equals lid l in
                         if uu____17775
                         then
                           let uu____17798 =
                             let uu____17817 =
                               let uu____17832 = inst_tscheme t in
                               FStar_Util.Inl uu____17832 in
                             let uu____17847 = FStar_Ident.range_of_lid l in
                             (uu____17817, uu____17847) in
                           FStar_Pervasives_Native.Some uu____17798
                         else FStar_Pervasives_Native.None
                     | uu____17900 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu____17692
                (fun uu____17938 ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17948 ->
                        match uu___3_17948 with
                        | (uu____17951,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               (ses, uu____17953);
                             FStar_Syntax_Syntax.sigrng = uu____17954;
                             FStar_Syntax_Syntax.sigquals = uu____17955;
                             FStar_Syntax_Syntax.sigmeta = uu____17956;
                             FStar_Syntax_Syntax.sigattrs = uu____17957;
                             FStar_Syntax_Syntax.sigopts = uu____17958;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu____17980 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu____17980
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids, s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____18032 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____18039 -> cache t in
                            let uu____18040 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
                            (match uu____18040 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____18046 =
                                   let uu____18047 =
                                     FStar_Ident.range_of_lid l in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____18047) in
                                 maybe_cache uu____18046)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____18118 = find_in_sigtab env1 lid in
         match uu____18118 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____18199 = lookup_qname env1 lid in
      match uu____18199 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____18220, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1 ->
    fun attr ->
      let uu____18334 = FStar_Util.smap_try_find (attrtab env1) attr in
      match uu____18334 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      let add_one env2 se1 attr =
        let uu____18379 =
          let uu____18382 = lookup_attr env2 attr in se1 :: uu____18382 in
        FStar_Util.smap_add (attrtab env2) attr uu____18379 in
      FStar_List.iter
        (fun attr ->
           let uu____18392 =
             let uu____18393 = FStar_Syntax_Subst.compress attr in
             uu____18393.FStar_Syntax_Syntax.n in
           match uu____18392 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18397 =
                 let uu____18399 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_Ident.string_of_lid uu____18399 in
               add_one env1 se uu____18397
           | uu____18400 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____18423) ->
          add_sigelts env1 ses
      | uu____18432 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l ->
                let uu____18440 = FStar_Ident.string_of_lid l in
                FStar_Util.smap_add (sigtab env1) uu____18440 se) lids;
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
        (fun uu___4_18474 ->
           match uu___4_18474 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____18484 =
                 let uu____18491 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname in
                 ((id.FStar_Syntax_Syntax.sort), uu____18491) in
               FStar_Pervasives_Native.Some uu____18484
           | uu____18500 -> FStar_Pervasives_Native.None)
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18562, lb::[]), uu____18564) ->
            let uu____18573 =
              let uu____18582 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____18591 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____18582, uu____18591) in
            FStar_Pervasives_Native.Some uu____18573
        | FStar_Syntax_Syntax.Sig_let ((uu____18604, lbs), uu____18606) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18638 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18651 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____18651
                     then
                       let uu____18664 =
                         let uu____18673 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____18682 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____18673, uu____18682) in
                       FStar_Pervasives_Native.Some uu____18664
                     else FStar_Pervasives_Native.None)
        | uu____18705 -> FStar_Pervasives_Native.None
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
                    let uu____18797 =
                      let uu____18799 =
                        let uu____18801 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname in
                        let uu____18803 =
                          let uu____18805 =
                            let uu____18807 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature)) in
                            let uu____18813 =
                              let uu____18815 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us) in
                              Prims.op_Hat ", got " uu____18815 in
                            Prims.op_Hat uu____18807 uu____18813 in
                          Prims.op_Hat ", expected " uu____18805 in
                        Prims.op_Hat uu____18801 uu____18803 in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18799 in
                    failwith uu____18797
                  else ());
             (let uu____18822 =
                let uu____18831 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature in
                (uu____18831, (se.FStar_Syntax_Syntax.sigrng)) in
              FStar_Pervasives_Native.Some uu____18822))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid, us, binders, uu____18851, uu____18852) ->
            let uu____18857 =
              let uu____18866 =
                let uu____18871 =
                  let uu____18872 =
                    let uu____18875 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                    FStar_Syntax_Util.arrow binders uu____18875 in
                  (us, uu____18872) in
                inst_ts us_opt uu____18871 in
              (uu____18866, (se.FStar_Syntax_Syntax.sigrng)) in
            FStar_Pervasives_Native.Some uu____18857
        | uu____18894 -> FStar_Pervasives_Native.None
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
        let mapper uu____18983 =
          match uu____18983 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____19079, uvs, t, uu____19082, uu____19083,
                         uu____19084);
                      FStar_Syntax_Syntax.sigrng = uu____19085;
                      FStar_Syntax_Syntax.sigquals = uu____19086;
                      FStar_Syntax_Syntax.sigmeta = uu____19087;
                      FStar_Syntax_Syntax.sigattrs = uu____19088;
                      FStar_Syntax_Syntax.sigopts = uu____19089;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____19114 =
                     let uu____19123 = inst_tscheme1 (uvs, t) in
                     (uu____19123, rng) in
                   FStar_Pervasives_Native.Some uu____19114
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____19147;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____19149;
                      FStar_Syntax_Syntax.sigattrs = uu____19150;
                      FStar_Syntax_Syntax.sigopts = uu____19151;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____19170 =
                     let uu____19172 = in_cur_mod env1 l in uu____19172 = Yes in
                   if uu____19170
                   then
                     let uu____19184 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface in
                     (if uu____19184
                      then
                        let uu____19200 =
                          let uu____19209 = inst_tscheme1 (uvs, t) in
                          (uu____19209, rng) in
                        FStar_Pervasives_Native.Some uu____19200
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____19242 =
                        let uu____19251 = inst_tscheme1 (uvs, t) in
                        (uu____19251, rng) in
                      FStar_Pervasives_Native.Some uu____19242)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____19276, uu____19277);
                      FStar_Syntax_Syntax.sigrng = uu____19278;
                      FStar_Syntax_Syntax.sigquals = uu____19279;
                      FStar_Syntax_Syntax.sigmeta = uu____19280;
                      FStar_Syntax_Syntax.sigattrs = uu____19281;
                      FStar_Syntax_Syntax.sigopts = uu____19282;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19325 =
                          let uu____19334 = inst_tscheme1 (uvs, k) in
                          (uu____19334, rng) in
                        FStar_Pervasives_Native.Some uu____19325
                    | uu____19355 ->
                        let uu____19356 =
                          let uu____19365 =
                            let uu____19370 =
                              let uu____19371 =
                                let uu____19374 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____19374 in
                              (uvs, uu____19371) in
                            inst_tscheme1 uu____19370 in
                          (uu____19365, rng) in
                        FStar_Pervasives_Native.Some uu____19356)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____19397, uu____19398);
                      FStar_Syntax_Syntax.sigrng = uu____19399;
                      FStar_Syntax_Syntax.sigquals = uu____19400;
                      FStar_Syntax_Syntax.sigmeta = uu____19401;
                      FStar_Syntax_Syntax.sigattrs = uu____19402;
                      FStar_Syntax_Syntax.sigopts = uu____19403;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19447 =
                          let uu____19456 = inst_tscheme_with (uvs, k) us in
                          (uu____19456, rng) in
                        FStar_Pervasives_Native.Some uu____19447
                    | uu____19477 ->
                        let uu____19478 =
                          let uu____19487 =
                            let uu____19492 =
                              let uu____19493 =
                                let uu____19496 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____19496 in
                              (uvs, uu____19493) in
                            inst_tscheme_with uu____19492 us in
                          (uu____19487, rng) in
                        FStar_Pervasives_Native.Some uu____19478)
               | FStar_Util.Inr se ->
                   let uu____19532 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19553;
                          FStar_Syntax_Syntax.sigrng = uu____19554;
                          FStar_Syntax_Syntax.sigquals = uu____19555;
                          FStar_Syntax_Syntax.sigmeta = uu____19556;
                          FStar_Syntax_Syntax.sigattrs = uu____19557;
                          FStar_Syntax_Syntax.sigopts = uu____19558;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19575 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range in
                   FStar_All.pipe_right uu____19532
                     (FStar_Util.map_option
                        (fun uu____19623 ->
                           match uu____19623 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____19654 =
          let uu____19665 = lookup_qname env1 lid in
          FStar_Util.bind_opt uu____19665 mapper in
        match uu____19654 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____19739 =
              let uu____19750 =
                let uu____19757 =
                  let uu___861_19760 = t in
                  let uu____19761 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___861_19760.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19761;
                    FStar_Syntax_Syntax.vars =
                      (uu___861_19760.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____19757) in
              (uu____19750, r) in
            FStar_Pervasives_Native.Some uu____19739
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____19810 = lookup_qname env1 l in
      match uu____19810 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____19831 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1 ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____19885 = try_lookup_bv env1 bv in
      match uu____19885 with
      | FStar_Pervasives_Native.None ->
          let uu____19900 = variable_not_found bv in
          FStar_Errors.raise_error uu____19900 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____19916 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____19917 =
            let uu____19918 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____19918 in
          (uu____19916, uu____19917)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____19940 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
      match uu____19940 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____20006 = FStar_Range.use_range use_range in
            FStar_Range.set_use_range r uu____20006 in
          let uu____20007 =
            let uu____20016 =
              let uu____20021 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____20021) in
            (uu____20016, r1) in
          FStar_Pervasives_Native.Some uu____20007
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
        let uu____20056 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l in
        match uu____20056 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____20089, t), r) ->
            let use_range = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____20114 = FStar_Range.use_range use_range in
              FStar_Range.set_use_range r uu____20114 in
            let uu____20115 =
              let uu____20120 = FStar_Syntax_Subst.set_use_range use_range t in
              (uu____20120, r1) in
            FStar_Pervasives_Native.Some uu____20115
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1 ->
    fun l ->
      let uu____20144 = try_lookup_lid env1 l in
      match uu____20144 with
      | FStar_Pervasives_Native.None ->
          let uu____20171 = name_not_found l in
          let uu____20177 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____20171 uu____20177
      | FStar_Pervasives_Native.Some v -> v
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1 ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_20222 ->
              match uu___5_20222 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____20225 = FStar_Ident.string_of_id x in
                  let uu____20227 = FStar_Ident.string_of_id y in
                  uu____20225 = uu____20227
              | uu____20230 -> false) env1.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____20251 = lookup_qname env1 lid in
      match uu____20251 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20260, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____20263;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20265;
              FStar_Syntax_Syntax.sigattrs = uu____20266;
              FStar_Syntax_Syntax.sigopts = uu____20267;_},
            FStar_Pervasives_Native.None),
           uu____20268)
          ->
          let uu____20319 =
            let uu____20326 =
              let uu____20327 =
                let uu____20330 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____20330 t in
              (uvs, uu____20327) in
            (uu____20326, q) in
          FStar_Pervasives_Native.Some uu____20319
      | uu____20343 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____20365 = lookup_qname env1 lid in
      match uu____20365 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20370, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____20373;
              FStar_Syntax_Syntax.sigquals = uu____20374;
              FStar_Syntax_Syntax.sigmeta = uu____20375;
              FStar_Syntax_Syntax.sigattrs = uu____20376;
              FStar_Syntax_Syntax.sigopts = uu____20377;_},
            FStar_Pervasives_Native.None),
           uu____20378)
          ->
          let uu____20429 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____20429 (uvs, t)
      | uu____20434 ->
          let uu____20435 = name_not_found lid in
          let uu____20441 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____20435 uu____20441
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____20461 = lookup_qname env1 lid in
      match uu____20461 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20466, uvs, t, uu____20469, uu____20470, uu____20471);
              FStar_Syntax_Syntax.sigrng = uu____20472;
              FStar_Syntax_Syntax.sigquals = uu____20473;
              FStar_Syntax_Syntax.sigmeta = uu____20474;
              FStar_Syntax_Syntax.sigattrs = uu____20475;
              FStar_Syntax_Syntax.sigopts = uu____20476;_},
            FStar_Pervasives_Native.None),
           uu____20477)
          ->
          let uu____20534 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____20534 (uvs, t)
      | uu____20539 ->
          let uu____20540 = name_not_found lid in
          let uu____20546 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____20540 uu____20546
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1 ->
    fun lid ->
      let uu____20569 = lookup_qname env1 lid in
      match uu____20569 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20577, uu____20578, uu____20579, uu____20580,
                 uu____20581, dcs);
              FStar_Syntax_Syntax.sigrng = uu____20583;
              FStar_Syntax_Syntax.sigquals = uu____20584;
              FStar_Syntax_Syntax.sigmeta = uu____20585;
              FStar_Syntax_Syntax.sigattrs = uu____20586;
              FStar_Syntax_Syntax.sigopts = uu____20587;_},
            uu____20588),
           uu____20589)
          -> (true, dcs)
      | uu____20654 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu____20670 = lookup_qname env1 lid in
      match uu____20670 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20671, uu____20672, uu____20673, l, uu____20675,
                 uu____20676);
              FStar_Syntax_Syntax.sigrng = uu____20677;
              FStar_Syntax_Syntax.sigquals = uu____20678;
              FStar_Syntax_Syntax.sigmeta = uu____20679;
              FStar_Syntax_Syntax.sigattrs = uu____20680;
              FStar_Syntax_Syntax.sigopts = uu____20681;_},
            uu____20682),
           uu____20683)
          -> l
      | uu____20742 ->
          let uu____20743 =
            let uu____20745 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____20745 in
          failwith uu____20743
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
              (FStar_Util.Inr (se, FStar_Pervasives_Native.None),
               uu____20815)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu____20872)
                   when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        let uu____20896 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid in
                        if uu____20896
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20931 -> FStar_Pervasives_Native.None)
          | uu____20940 -> FStar_Pervasives_Native.None
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
        let uu____21002 = lookup_qname env1 lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____21002
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
        let uu____21035 = lookup_qname env1 lid in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____21035
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv ->
    fun qn ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____21059 =
        let uu____21061 = FStar_Ident.nsstr lid in uu____21061 = "Prims" in
      if uu____21059
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____21091, uu____21092) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se, uu____21141), uu____21142) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____21191 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____21209 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____21219 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____21236 ->
                  let uu____21243 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals in
                  FStar_Pervasives_Native.Some uu____21243
              | FStar_Syntax_Syntax.Sig_let ((uu____21244, lbs), uu____21246)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       let uu____21262 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid in
                       if uu____21262
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____21269 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____21285 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____21295 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____21302 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____21303 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21304 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____21317 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____21318 ->
                  FStar_Pervasives_Native.None))
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____21341 =
        let uu____21343 = FStar_Ident.nsstr lid in uu____21343 = "Prims" in
      if uu____21341
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21350 =
           let uu____21353 = FStar_Ident.string_of_lid lid in
           FStar_All.pipe_right uu____21353
             (FStar_Util.smap_try_find env1.fv_delta_depths) in
         FStar_All.pipe_right uu____21350
           (fun d_opt ->
              let uu____21365 = FStar_All.pipe_right d_opt FStar_Util.is_some in
              if uu____21365
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21375 =
                   let uu____21378 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   delta_depth_of_qninfo fv uu____21378 in
                 match uu____21375 with
                 | FStar_Pervasives_Native.None ->
                     let uu____21379 =
                       let uu____21381 = FStar_Syntax_Print.fv_to_string fv in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21381 in
                     failwith uu____21379
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21386 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ()) in
                       if uu____21386
                       then
                         let uu____21389 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____21391 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta in
                         let uu____21393 =
                           FStar_Syntax_Print.delta_depth_to_string d in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21389 uu____21391 uu____21393
                       else ());
                      (let uu____21399 = FStar_Ident.string_of_lid lid in
                       FStar_Util.smap_add env1.fv_delta_depths uu____21399 d);
                      d))))
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____21420), uu____21421) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21470 -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____21492), uu____21493) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21542 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____21564 = lookup_qname env1 lid in
      FStar_All.pipe_left attrs_of_qninfo uu____21564
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____21597 = lookup_attrs_of_lid env1 fv_lid in
        match uu____21597 with
        | FStar_Pervasives_Native.None -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21619 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm ->
                      let uu____21628 =
                        let uu____21629 = FStar_Syntax_Util.un_uinst tm in
                        uu____21629.FStar_Syntax_Syntax.n in
                      match uu____21628 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21634 -> false)) in
            (true, uu____21619)
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____21657 = fv_exists_and_has_attr env1 fv_lid attr_lid in
        FStar_Pervasives_Native.snd uu____21657
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
          let uu____21729 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____21729 in
        let uu____21730 = FStar_Util.smap_try_find tab s in
        match uu____21730 with
        | FStar_Pervasives_Native.None ->
            let uu____21733 = f () in
            (match uu____21733 with
             | (should_cache, res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1 ->
    fun fv ->
      let f uu____21771 =
        let uu____21772 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr in
        match uu____21772 with | (ex, erasable) -> (ex, erasable) in
      cache_in_fv_tab env1.erasable_types_tab fv f
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____21806 =
        let uu____21807 = FStar_Syntax_Util.unrefine t in
        uu____21807.FStar_Syntax_Syntax.n in
      match uu____21806 with
      | FStar_Syntax_Syntax.Tm_type uu____21811 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head, uu____21815) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu____21841) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21846, c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21868 -> false
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fv ->
      let f uu____21901 =
        let attrs =
          let uu____21907 = FStar_Syntax_Syntax.lid_of_fv fv in
          lookup_attrs_of_lid env1 uu____21907 in
        match attrs with
        | FStar_Pervasives_Native.None ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x ->
                   let uu____21947 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr in
                   FStar_Pervasives_Native.fst uu____21947) in
            (true, res) in
      cache_in_fv_tab env1.strict_args_tab fv f
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ftv ->
      let uu____21992 = lookup_qname env1 ftv in
      match uu____21992 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____21996) ->
          let uu____22041 =
            effect_signature FStar_Pervasives_Native.None se env1.range in
          (match uu____22041 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____22062, t), r) ->
               let uu____22077 =
                 let uu____22078 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____22078 t in
               FStar_Pervasives_Native.Some uu____22077)
      | uu____22079 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun ftv ->
      let uu____22091 = try_lookup_effect_lid env1 ftv in
      match uu____22091 with
      | FStar_Pervasives_Native.None ->
          let uu____22094 = name_not_found ftv in
          let uu____22100 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____22094 uu____22100
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
        let uu____22124 = lookup_qname env1 lid0 in
        match uu____22124 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs, binders, c, uu____22135);
                FStar_Syntax_Syntax.sigrng = uu____22136;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____22138;
                FStar_Syntax_Syntax.sigattrs = uu____22139;
                FStar_Syntax_Syntax.sigopts = uu____22140;_},
              FStar_Pervasives_Native.None),
             uu____22141)
            ->
            let lid1 =
              let uu____22197 =
                let uu____22198 = FStar_Ident.range_of_lid lid in
                let uu____22199 =
                  let uu____22200 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____22200 in
                FStar_Range.set_use_range uu____22198 uu____22199 in
              FStar_Ident.set_lid_range lid uu____22197 in
            let uu____22201 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_22207 ->
                      match uu___6_22207 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____22210 -> false)) in
            if uu____22201
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____22229 =
                      let uu____22231 =
                        let uu____22233 = get_range env1 in
                        FStar_Range.string_of_range uu____22233 in
                      let uu____22234 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____22236 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____22231 uu____22234 uu____22236 in
                    failwith uu____22229) in
               match (binders, univs) with
               | ([], uu____22257) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____22283, uu____22284::uu____22285::uu____22286) ->
                   let uu____22307 =
                     let uu____22309 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____22311 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____22309 uu____22311 in
                   failwith uu____22307
               | uu____22322 ->
                   let uu____22337 =
                     let uu____22342 =
                       let uu____22343 = FStar_Syntax_Util.arrow binders c in
                       (univs, uu____22343) in
                     inst_tscheme_with uu____22342 insts in
                   (match uu____22337 with
                    | (uu____22356, t) ->
                        let t1 =
                          let uu____22359 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____22359 t in
                        let uu____22360 =
                          let uu____22361 = FStar_Syntax_Subst.compress t1 in
                          uu____22361.FStar_Syntax_Syntax.n in
                        (match uu____22360 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22396 -> failwith "Impossible")))
        | uu____22404 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun l ->
      let rec find l1 =
        let uu____22428 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____22428 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22441, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____22448 = find l2 in
            (match uu____22448 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____22455 =
          let uu____22458 = FStar_Ident.string_of_lid l in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____22458 in
        match uu____22455 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____22461 = find l in
            (match uu____22461 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____22466 = FStar_Ident.string_of_lid l in
                   FStar_Util.smap_add env1.normalized_eff_names uu____22466
                     m);
                  m)) in
      let uu____22468 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____22468
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1 ->
    fun name ->
      fun r ->
        let sig_t =
          let uu____22489 =
            FStar_All.pipe_right name (lookup_effect_lid env1) in
          FStar_All.pipe_right uu____22489 FStar_Syntax_Subst.compress in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs, uu____22495) ->
            FStar_List.length bs
        | uu____22534 ->
            let uu____22535 =
              let uu____22541 =
                let uu____22543 = FStar_Ident.string_of_lid name in
                let uu____22545 = FStar_Syntax_Print.term_to_string sig_t in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22543 uu____22545 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22541) in
            FStar_Errors.raise_error uu____22535 r
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1 ->
    fun l ->
      let l1 = norm_eff_name env1 l in
      let uu____22564 = lookup_qname env1 l1 in
      match uu____22564 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22567;
              FStar_Syntax_Syntax.sigrng = uu____22568;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22570;
              FStar_Syntax_Syntax.sigattrs = uu____22571;
              FStar_Syntax_Syntax.sigopts = uu____22572;_},
            uu____22573),
           uu____22574)
          -> q
      | uu____22627 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      fun i ->
        let fail uu____22651 =
          let uu____22652 =
            let uu____22654 = FStar_Util.string_of_int i in
            let uu____22656 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22654 uu____22656 in
          failwith uu____22652 in
        let uu____22659 = lookup_datacon env1 lid in
        match uu____22659 with
        | (uu____22664, t) ->
            let uu____22666 =
              let uu____22667 = FStar_Syntax_Subst.compress t in
              uu____22667.FStar_Syntax_Syntax.n in
            (match uu____22666 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____22671) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22717 -> fail ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____22731 = lookup_qname env1 l in
      match uu____22731 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22733, uu____22734, uu____22735);
              FStar_Syntax_Syntax.sigrng = uu____22736;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22738;
              FStar_Syntax_Syntax.sigattrs = uu____22739;
              FStar_Syntax_Syntax.sigopts = uu____22740;_},
            uu____22741),
           uu____22742)
          ->
          FStar_Util.for_some
            (fun uu___7_22797 ->
               match uu___7_22797 with
               | FStar_Syntax_Syntax.Projector uu____22799 -> true
               | uu____22805 -> false) quals
      | uu____22807 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____22821 = lookup_qname env1 lid in
      match uu____22821 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22823, uu____22824, uu____22825, uu____22826,
                 uu____22827, uu____22828);
              FStar_Syntax_Syntax.sigrng = uu____22829;
              FStar_Syntax_Syntax.sigquals = uu____22830;
              FStar_Syntax_Syntax.sigmeta = uu____22831;
              FStar_Syntax_Syntax.sigattrs = uu____22832;
              FStar_Syntax_Syntax.sigopts = uu____22833;_},
            uu____22834),
           uu____22835)
          -> true
      | uu____22895 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____22909 = lookup_qname env1 lid in
      match uu____22909 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22911, uu____22912, uu____22913, uu____22914,
                 uu____22915, uu____22916);
              FStar_Syntax_Syntax.sigrng = uu____22917;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22919;
              FStar_Syntax_Syntax.sigattrs = uu____22920;
              FStar_Syntax_Syntax.sigopts = uu____22921;_},
            uu____22922),
           uu____22923)
          ->
          FStar_Util.for_some
            (fun uu___8_22986 ->
               match uu___8_22986 with
               | FStar_Syntax_Syntax.RecordType uu____22988 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22998 -> true
               | uu____23008 -> false) quals
      | uu____23010 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____23020, uu____23021);
            FStar_Syntax_Syntax.sigrng = uu____23022;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____23024;
            FStar_Syntax_Syntax.sigattrs = uu____23025;
            FStar_Syntax_Syntax.sigopts = uu____23026;_},
          uu____23027),
         uu____23028)
        ->
        FStar_Util.for_some
          (fun uu___9_23087 ->
             match uu___9_23087 with
             | FStar_Syntax_Syntax.Action uu____23089 -> true
             | uu____23091 -> false) quals
    | uu____23093 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____23107 = lookup_qname env1 lid in
      FStar_All.pipe_left qninfo_is_action uu____23107
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
      let uu____23124 =
        let uu____23125 = FStar_Syntax_Util.un_uinst head in
        uu____23125.FStar_Syntax_Syntax.n in
      match uu____23124 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____23131 ->
               true
           | uu____23134 -> false)
      | uu____23136 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____23150 = lookup_qname env1 l in
      match uu____23150 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____23153), uu____23154) ->
          FStar_Util.for_some
            (fun uu___10_23202 ->
               match uu___10_23202 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____23205 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____23207 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____23283 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____23301) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____23319 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____23327 ->
                 FStar_Pervasives_Native.Some true
             | uu____23346 -> FStar_Pervasives_Native.Some false) in
      let uu____23349 =
        let uu____23353 = lookup_qname env1 lid in
        FStar_Util.bind_opt uu____23353 mapper in
      match uu____23349 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu____23413 = lookup_qname env1 lid in
      match uu____23413 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23417, uu____23418, tps, uu____23420, uu____23421,
                 uu____23422);
              FStar_Syntax_Syntax.sigrng = uu____23423;
              FStar_Syntax_Syntax.sigquals = uu____23424;
              FStar_Syntax_Syntax.sigmeta = uu____23425;
              FStar_Syntax_Syntax.sigattrs = uu____23426;
              FStar_Syntax_Syntax.sigopts = uu____23427;_},
            uu____23428),
           uu____23429)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23497 -> FStar_Pervasives_Native.None
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
           (fun uu____23543 ->
              match uu____23543 with
              | (d, uu____23552) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1 ->
    fun l ->
      let uu____23568 = effect_decl_opt env1 l in
      match uu____23568 with
      | FStar_Pervasives_Native.None ->
          let uu____23583 = name_not_found l in
          let uu____23589 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____23583 uu____23589
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____23617 = FStar_All.pipe_right l (get_effect_decl env1) in
      FStar_All.pipe_right uu____23617 FStar_Syntax_Util.is_layered
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23624 ->
         fun c -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23638 ->
            fun uu____23639 -> fun e -> FStar_Util.return_all e))
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
        let uu____23673 = FStar_Ident.lid_equals l1 l2 in
        if uu____23673
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23692 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____23692
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23711 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23764 ->
                        match uu____23764 with
                        | (m1, m2, uu____23778, uu____23779, uu____23780) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____23711 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23805, uu____23806, m3, j1, j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____23854 = join_opt env1 l1 l2 in
        match uu____23854 with
        | FStar_Pervasives_Native.None ->
            let uu____23875 =
              let uu____23881 =
                let uu____23883 = FStar_Syntax_Print.lid_to_string l1 in
                let uu____23885 = FStar_Syntax_Print.lid_to_string l2 in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23883 uu____23885 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23881) in
            FStar_Errors.raise_error uu____23875 env1.range
        | FStar_Pervasives_Native.Some t -> t
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____23928 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____23928
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
  'uuuuuu23948 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23948) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls ->
    fun m ->
      let uu____23977 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____24003 ->
                match uu____24003 with
                | (d, uu____24010) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____23977 with
      | FStar_Pervasives_Native.None ->
          let uu____24021 =
            let uu____24023 = FStar_Ident.string_of_lid m in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____24023 in
          failwith uu____24021
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____24038 = inst_tscheme md.FStar_Syntax_Syntax.signature in
          (match uu____24038 with
           | (uu____24049, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____24067)::(wp, uu____24069)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____24125 -> failwith "Impossible"))
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
        | uu____24190 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun comp ->
      let c = comp_to_comp_typ env1 comp in
      let uu____24203 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____24203 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____24220 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____24220 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____24245 =
                     let uu____24251 =
                       let uu____24253 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____24261 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one) in
                       let uu____24272 =
                         let uu____24274 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____24274 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____24253 uu____24261 uu____24272 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____24251) in
                   FStar_Errors.raise_error uu____24245
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____24282 =
                     let uu____24293 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____24293 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____24330 ->
                        fun uu____24331 ->
                          match (uu____24330, uu____24331) with
                          | ((x, uu____24361), (t, uu____24363)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____24282 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1 in
                 let c2 =
                   let uu____24394 =
                     let uu___1615_24395 = comp_to_comp_typ env1 c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1615_24395.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1615_24395.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1615_24395.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1615_24395.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____24394
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env1 c2)))
let effect_repr_aux :
  'uuuuuu24407 .
    'uuuuuu24407 ->
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
            let uu____24448 =
              let uu____24455 = num_effect_indices env1 eff_name r in
              ((FStar_List.length args), uu____24455) in
            match uu____24448 with
            | (given, expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24479 = FStar_Ident.string_of_lid eff_name in
                     let uu____24481 = FStar_Util.string_of_int given in
                     let uu____24483 = FStar_Util.string_of_int expected in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24479 uu____24481 uu____24483 in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r) in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c) in
          let uu____24488 = effect_decl_opt env1 effect_name in
          match uu____24488 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, uu____24510) ->
              let uu____24521 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              (match uu____24521 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24539 =
                       let uu____24542 =
                         let uu____24543 =
                           let uu____24560 =
                             let uu____24571 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg in
                             uu____24571 ::
                               (c1.FStar_Syntax_Syntax.effect_args) in
                           (repr, uu____24560) in
                         FStar_Syntax_Syntax.Tm_app uu____24543 in
                       let uu____24608 = get_range env1 in
                       FStar_Syntax_Syntax.mk uu____24542 uu____24608 in
                     FStar_Pervasives_Native.Some uu____24539)))
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
           (fun uu___11_24672 ->
              match uu___11_24672 with
              | FStar_Syntax_Syntax.Reflectable uu____24674 -> true
              | uu____24676 -> false))
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
      | uu____24736 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____24751 =
        let uu____24752 = FStar_Syntax_Subst.compress t in
        uu____24752.FStar_Syntax_Syntax.n in
      match uu____24751 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24756, c) ->
          is_reifiable_comp env1 c
      | uu____24778 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu____24798 =
           let uu____24800 = is_reifiable_effect env1 l in
           Prims.op_Negation uu____24800 in
         if uu____24798
         then
           let uu____24803 =
             let uu____24809 =
               let uu____24811 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24811 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24809) in
           let uu____24815 = get_range env1 in
           FStar_Errors.raise_error uu____24803 uu____24815
         else ());
        (let uu____24818 = effect_repr_aux true env1 c u_c in
         match uu____24818 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env2 =
        let uu___1692_24854 = env1 in
        {
          solver = (uu___1692_24854.solver);
          range = (uu___1692_24854.range);
          curmodule = (uu___1692_24854.curmodule);
          gamma = (uu___1692_24854.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1692_24854.gamma_cache);
          modules = (uu___1692_24854.modules);
          expected_typ = (uu___1692_24854.expected_typ);
          sigtab = (uu___1692_24854.sigtab);
          attrtab = (uu___1692_24854.attrtab);
          instantiate_imp = (uu___1692_24854.instantiate_imp);
          effects = (uu___1692_24854.effects);
          generalize = (uu___1692_24854.generalize);
          letrecs = (uu___1692_24854.letrecs);
          top_level = (uu___1692_24854.top_level);
          check_uvars = (uu___1692_24854.check_uvars);
          use_eq = (uu___1692_24854.use_eq);
          use_eq_strict = (uu___1692_24854.use_eq_strict);
          is_iface = (uu___1692_24854.is_iface);
          admit = (uu___1692_24854.admit);
          lax = (uu___1692_24854.lax);
          lax_universes = (uu___1692_24854.lax_universes);
          phase1 = (uu___1692_24854.phase1);
          failhard = (uu___1692_24854.failhard);
          nosynth = (uu___1692_24854.nosynth);
          uvar_subtyping = (uu___1692_24854.uvar_subtyping);
          tc_term = (uu___1692_24854.tc_term);
          type_of = (uu___1692_24854.type_of);
          universe_of = (uu___1692_24854.universe_of);
          check_type_of = (uu___1692_24854.check_type_of);
          use_bv_sorts = (uu___1692_24854.use_bv_sorts);
          qtbl_name_and_index = (uu___1692_24854.qtbl_name_and_index);
          normalized_eff_names = (uu___1692_24854.normalized_eff_names);
          fv_delta_depths = (uu___1692_24854.fv_delta_depths);
          proof_ns = (uu___1692_24854.proof_ns);
          synth_hook = (uu___1692_24854.synth_hook);
          try_solve_implicits_hook =
            (uu___1692_24854.try_solve_implicits_hook);
          splice = (uu___1692_24854.splice);
          mpreprocess = (uu___1692_24854.mpreprocess);
          postprocess = (uu___1692_24854.postprocess);
          identifier_info = (uu___1692_24854.identifier_info);
          tc_hooks = (uu___1692_24854.tc_hooks);
          dsenv = (uu___1692_24854.dsenv);
          nbe = (uu___1692_24854.nbe);
          strict_args_tab = (uu___1692_24854.strict_args_tab);
          erasable_types_tab = (uu___1692_24854.erasable_types_tab);
          enable_defer_to_tac = (uu___1692_24854.enable_defer_to_tac)
        } in
      add_sigelt env2 s;
      (env2.tc_hooks).tc_push_in_gamma_hook env2 (FStar_Util.Inr sb);
      env2
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env1 ->
    fun uu____24873 ->
      match uu____24873 with
      | (ed, quals) ->
          let effects1 =
            let uu___1701_24887 = env1.effects in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1701_24887.order);
              joins = (uu___1701_24887.joins);
              polymonadic_binds = (uu___1701_24887.polymonadic_binds);
              polymonadic_subcomps = (uu___1701_24887.polymonadic_subcomps)
            } in
          let uu___1704_24896 = env1 in
          {
            solver = (uu___1704_24896.solver);
            range = (uu___1704_24896.range);
            curmodule = (uu___1704_24896.curmodule);
            gamma = (uu___1704_24896.gamma);
            gamma_sig = (uu___1704_24896.gamma_sig);
            gamma_cache = (uu___1704_24896.gamma_cache);
            modules = (uu___1704_24896.modules);
            expected_typ = (uu___1704_24896.expected_typ);
            sigtab = (uu___1704_24896.sigtab);
            attrtab = (uu___1704_24896.attrtab);
            instantiate_imp = (uu___1704_24896.instantiate_imp);
            effects = effects1;
            generalize = (uu___1704_24896.generalize);
            letrecs = (uu___1704_24896.letrecs);
            top_level = (uu___1704_24896.top_level);
            check_uvars = (uu___1704_24896.check_uvars);
            use_eq = (uu___1704_24896.use_eq);
            use_eq_strict = (uu___1704_24896.use_eq_strict);
            is_iface = (uu___1704_24896.is_iface);
            admit = (uu___1704_24896.admit);
            lax = (uu___1704_24896.lax);
            lax_universes = (uu___1704_24896.lax_universes);
            phase1 = (uu___1704_24896.phase1);
            failhard = (uu___1704_24896.failhard);
            nosynth = (uu___1704_24896.nosynth);
            uvar_subtyping = (uu___1704_24896.uvar_subtyping);
            tc_term = (uu___1704_24896.tc_term);
            type_of = (uu___1704_24896.type_of);
            universe_of = (uu___1704_24896.universe_of);
            check_type_of = (uu___1704_24896.check_type_of);
            use_bv_sorts = (uu___1704_24896.use_bv_sorts);
            qtbl_name_and_index = (uu___1704_24896.qtbl_name_and_index);
            normalized_eff_names = (uu___1704_24896.normalized_eff_names);
            fv_delta_depths = (uu___1704_24896.fv_delta_depths);
            proof_ns = (uu___1704_24896.proof_ns);
            synth_hook = (uu___1704_24896.synth_hook);
            try_solve_implicits_hook =
              (uu___1704_24896.try_solve_implicits_hook);
            splice = (uu___1704_24896.splice);
            mpreprocess = (uu___1704_24896.mpreprocess);
            postprocess = (uu___1704_24896.postprocess);
            identifier_info = (uu___1704_24896.identifier_info);
            tc_hooks = (uu___1704_24896.tc_hooks);
            dsenv = (uu___1704_24896.dsenv);
            nbe = (uu___1704_24896.nbe);
            strict_args_tab = (uu___1704_24896.strict_args_tab);
            erasable_types_tab = (uu___1704_24896.erasable_types_tab);
            enable_defer_to_tac = (uu___1704_24896.enable_defer_to_tac)
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
        let uu____24925 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24993 ->
                  match uu____24993 with
                  | (m1, n1, uu____25011, uu____25012) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____24925 with
        | FStar_Pervasives_Native.Some (uu____25037, uu____25038, p, t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____25083 -> FStar_Pervasives_Native.None
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun m ->
      fun n ->
        let uu____25128 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____25163 ->
                  match uu____25163 with
                  | (m1, n1, uu____25173) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____25128 with
        | FStar_Pervasives_Native.Some (uu____25176, uu____25177, ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____25185 -> FStar_Pervasives_Native.None
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1 ->
    fun src ->
      fun tgt ->
        fun st_mlift ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____25242 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2) in
                FStar_All.pipe_right uu____25242
                  (fun uu____25263 ->
                     match uu____25263 with
                     | (c1, g1) ->
                         let uu____25274 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2) in
                         FStar_All.pipe_right uu____25274
                           (fun uu____25295 ->
                              match uu____25295 with
                              | (c2, g2) ->
                                  let uu____25306 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2 in
                                  (c2, uu____25306))) in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun e ->
                              let uu____25428 = l1 u t e in
                              l2 u t uu____25428))
                | uu____25429 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let edge1 = { msource = src; mtarget = tgt; mlift = st_mlift } in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift } in
          let order = edge1 :: ((env1.effects).order) in
          let ms =
            FStar_All.pipe_right (env1.effects).decls
              (FStar_List.map
                 (fun uu____25497 ->
                    match uu____25497 with
                    | (e, uu____25505) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____25528 =
            match uu____25528 with
            | (i, j) ->
                let uu____25539 = FStar_Ident.lid_equals i j in
                if uu____25539
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____25546 ->
                       FStar_Pervasives_Native.Some uu____25546)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____25575 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i ->
                        let uu____25585 = FStar_Ident.lid_equals i k in
                        if uu____25585
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j ->
                                  let uu____25599 =
                                    FStar_Ident.lid_equals j k in
                                  if uu____25599
                                  then []
                                  else
                                    (let uu____25606 =
                                       let uu____25615 =
                                         find_edge order1 (i, k) in
                                       let uu____25618 =
                                         find_edge order1 (k, j) in
                                       (uu____25615, uu____25618) in
                                     match uu____25606 with
                                     | (FStar_Pervasives_Native.Some e1,
                                        FStar_Pervasives_Native.Some e2) ->
                                         let uu____25633 =
                                           compose_edges e1 e2 in
                                         [uu____25633]
                                     | uu____25634 -> []))))) in
              FStar_List.append order1 uu____25575 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1 ->
                 fun e2 ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          FStar_All.pipe_right order2
            (FStar_List.iter
               (fun edge2 ->
                  let uu____25664 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25667 =
                         lookup_effect_quals env1 edge2.mtarget in
                       FStar_All.pipe_right uu____25667
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)) in
                  if uu____25664
                  then
                    let uu____25674 =
                      let uu____25680 =
                        let uu____25682 =
                          FStar_Ident.string_of_lid edge2.mtarget in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25682 in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25680) in
                    let uu____25686 = get_range env1 in
                    FStar_Errors.raise_error uu____25674 uu____25686
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j ->
                             let join_opt1 =
                               let uu____25764 = FStar_Ident.lid_equals i j in
                               if uu____25764
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt ->
                                         fun k ->
                                           let uu____25816 =
                                             let uu____25825 =
                                               find_edge order2 (i, k) in
                                             let uu____25828 =
                                               find_edge order2 (j, k) in
                                             (uu____25825, uu____25828) in
                                           match uu____25816 with
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
                                                    (ub, uu____25870,
                                                     uu____25871)
                                                    ->
                                                    let uu____25878 =
                                                      let uu____25885 =
                                                        let uu____25887 =
                                                          find_edge order2
                                                            (k, ub) in
                                                        FStar_Util.is_some
                                                          uu____25887 in
                                                      let uu____25890 =
                                                        let uu____25892 =
                                                          find_edge order2
                                                            (ub, k) in
                                                        FStar_Util.is_some
                                                          uu____25892 in
                                                      (uu____25885,
                                                        uu____25890) in
                                                    (match uu____25878 with
                                                     | (true, true) ->
                                                         let uu____25909 =
                                                           FStar_Ident.lid_equals
                                                             k ub in
                                                         if uu____25909
                                                         then
                                                           (FStar_Errors.log_issue
                                                              FStar_Range.dummyRange
                                                              (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                "Looking multiple times at the same upper bound candidate");
                                                            bopt)
                                                         else
                                                           failwith
                                                             "Found a cycle in the lattice"
                                                     | (false, false) -> bopt
                                                     | (true, false) ->
                                                         FStar_Pervasives_Native.Some
                                                           (k, ik, jk)
                                                     | (false, true) -> bopt))
                                           | uu____25952 -> bopt)
                                      FStar_Pervasives_Native.None) in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None -> []
                             | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                 let uu____26004 =
                                   let uu____26006 =
                                     exists_polymonadic_bind env1 i j in
                                   FStar_All.pipe_right uu____26006
                                     FStar_Util.is_some in
                                 if uu____26004
                                 then
                                   let uu____26055 =
                                     let uu____26061 =
                                       let uu____26063 =
                                         FStar_Ident.string_of_lid src in
                                       let uu____26065 =
                                         FStar_Ident.string_of_lid tgt in
                                       let uu____26067 =
                                         FStar_Ident.string_of_lid i in
                                       let uu____26069 =
                                         FStar_Ident.string_of_lid j in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____26063 uu____26065 uu____26067
                                         uu____26069 in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____26061) in
                                   FStar_Errors.raise_error uu____26055
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))])))) in
           let effects1 =
             let uu___1838_26108 = env1.effects in
             {
               decls = (uu___1838_26108.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1838_26108.polymonadic_binds);
               polymonadic_subcomps = (uu___1838_26108.polymonadic_subcomps)
             } in
           let uu___1841_26109 = env1 in
           {
             solver = (uu___1841_26109.solver);
             range = (uu___1841_26109.range);
             curmodule = (uu___1841_26109.curmodule);
             gamma = (uu___1841_26109.gamma);
             gamma_sig = (uu___1841_26109.gamma_sig);
             gamma_cache = (uu___1841_26109.gamma_cache);
             modules = (uu___1841_26109.modules);
             expected_typ = (uu___1841_26109.expected_typ);
             sigtab = (uu___1841_26109.sigtab);
             attrtab = (uu___1841_26109.attrtab);
             instantiate_imp = (uu___1841_26109.instantiate_imp);
             effects = effects1;
             generalize = (uu___1841_26109.generalize);
             letrecs = (uu___1841_26109.letrecs);
             top_level = (uu___1841_26109.top_level);
             check_uvars = (uu___1841_26109.check_uvars);
             use_eq = (uu___1841_26109.use_eq);
             use_eq_strict = (uu___1841_26109.use_eq_strict);
             is_iface = (uu___1841_26109.is_iface);
             admit = (uu___1841_26109.admit);
             lax = (uu___1841_26109.lax);
             lax_universes = (uu___1841_26109.lax_universes);
             phase1 = (uu___1841_26109.phase1);
             failhard = (uu___1841_26109.failhard);
             nosynth = (uu___1841_26109.nosynth);
             uvar_subtyping = (uu___1841_26109.uvar_subtyping);
             tc_term = (uu___1841_26109.tc_term);
             type_of = (uu___1841_26109.type_of);
             universe_of = (uu___1841_26109.universe_of);
             check_type_of = (uu___1841_26109.check_type_of);
             use_bv_sorts = (uu___1841_26109.use_bv_sorts);
             qtbl_name_and_index = (uu___1841_26109.qtbl_name_and_index);
             normalized_eff_names = (uu___1841_26109.normalized_eff_names);
             fv_delta_depths = (uu___1841_26109.fv_delta_depths);
             proof_ns = (uu___1841_26109.proof_ns);
             synth_hook = (uu___1841_26109.synth_hook);
             try_solve_implicits_hook =
               (uu___1841_26109.try_solve_implicits_hook);
             splice = (uu___1841_26109.splice);
             mpreprocess = (uu___1841_26109.mpreprocess);
             postprocess = (uu___1841_26109.postprocess);
             identifier_info = (uu___1841_26109.identifier_info);
             tc_hooks = (uu___1841_26109.tc_hooks);
             dsenv = (uu___1841_26109.dsenv);
             nbe = (uu___1841_26109.nbe);
             strict_args_tab = (uu___1841_26109.strict_args_tab);
             erasable_types_tab = (uu___1841_26109.erasable_types_tab);
             enable_defer_to_tac = (uu___1841_26109.enable_defer_to_tac)
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
              let uu____26157 = FStar_Ident.string_of_lid m in
              let uu____26159 = FStar_Ident.string_of_lid n in
              let uu____26161 = FStar_Ident.string_of_lid p in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____26157 uu____26159 uu____26161
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice") in
            let uu____26170 =
              let uu____26172 = exists_polymonadic_bind env1 m n in
              FStar_All.pipe_right uu____26172 FStar_Util.is_some in
            if uu____26170
            then
              let uu____26209 =
                let uu____26215 = err_msg true in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26215) in
              FStar_Errors.raise_error uu____26209 env1.range
            else
              (let uu____26221 =
                 (let uu____26225 = join_opt env1 m n in
                  FStar_All.pipe_right uu____26225 FStar_Util.is_some) &&
                   (let uu____26250 = FStar_Ident.lid_equals m n in
                    Prims.op_Negation uu____26250) in
               if uu____26221
               then
                 let uu____26253 =
                   let uu____26259 = err_msg false in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26259) in
                 FStar_Errors.raise_error uu____26253 env1.range
               else
                 (let uu___1856_26265 = env1 in
                  {
                    solver = (uu___1856_26265.solver);
                    range = (uu___1856_26265.range);
                    curmodule = (uu___1856_26265.curmodule);
                    gamma = (uu___1856_26265.gamma);
                    gamma_sig = (uu___1856_26265.gamma_sig);
                    gamma_cache = (uu___1856_26265.gamma_cache);
                    modules = (uu___1856_26265.modules);
                    expected_typ = (uu___1856_26265.expected_typ);
                    sigtab = (uu___1856_26265.sigtab);
                    attrtab = (uu___1856_26265.attrtab);
                    instantiate_imp = (uu___1856_26265.instantiate_imp);
                    effects =
                      (let uu___1858_26267 = env1.effects in
                       {
                         decls = (uu___1858_26267.decls);
                         order = (uu___1858_26267.order);
                         joins = (uu___1858_26267.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1858_26267.polymonadic_subcomps)
                       });
                    generalize = (uu___1856_26265.generalize);
                    letrecs = (uu___1856_26265.letrecs);
                    top_level = (uu___1856_26265.top_level);
                    check_uvars = (uu___1856_26265.check_uvars);
                    use_eq = (uu___1856_26265.use_eq);
                    use_eq_strict = (uu___1856_26265.use_eq_strict);
                    is_iface = (uu___1856_26265.is_iface);
                    admit = (uu___1856_26265.admit);
                    lax = (uu___1856_26265.lax);
                    lax_universes = (uu___1856_26265.lax_universes);
                    phase1 = (uu___1856_26265.phase1);
                    failhard = (uu___1856_26265.failhard);
                    nosynth = (uu___1856_26265.nosynth);
                    uvar_subtyping = (uu___1856_26265.uvar_subtyping);
                    tc_term = (uu___1856_26265.tc_term);
                    type_of = (uu___1856_26265.type_of);
                    universe_of = (uu___1856_26265.universe_of);
                    check_type_of = (uu___1856_26265.check_type_of);
                    use_bv_sorts = (uu___1856_26265.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1856_26265.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1856_26265.normalized_eff_names);
                    fv_delta_depths = (uu___1856_26265.fv_delta_depths);
                    proof_ns = (uu___1856_26265.proof_ns);
                    synth_hook = (uu___1856_26265.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1856_26265.try_solve_implicits_hook);
                    splice = (uu___1856_26265.splice);
                    mpreprocess = (uu___1856_26265.mpreprocess);
                    postprocess = (uu___1856_26265.postprocess);
                    identifier_info = (uu___1856_26265.identifier_info);
                    tc_hooks = (uu___1856_26265.tc_hooks);
                    dsenv = (uu___1856_26265.dsenv);
                    nbe = (uu___1856_26265.nbe);
                    strict_args_tab = (uu___1856_26265.strict_args_tab);
                    erasable_types_tab = (uu___1856_26265.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1856_26265.enable_defer_to_tac)
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
            let uu____26358 = FStar_Ident.string_of_lid m in
            let uu____26360 = FStar_Ident.string_of_lid n in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu____26358 uu____26360
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice") in
          let uu____26369 =
            let uu____26371 = exists_polymonadic_subcomp env1 m n in
            FStar_All.pipe_right uu____26371 FStar_Util.is_some in
          if uu____26369
          then
            let uu____26378 =
              let uu____26384 = err_msg true in
              (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26384) in
            FStar_Errors.raise_error uu____26378 env1.range
          else
            (let uu____26390 =
               let uu____26392 = join_opt env1 m n in
               FStar_All.pipe_right uu____26392 FStar_Util.is_some in
             if uu____26390
             then
               let uu____26417 =
                 let uu____26423 = err_msg false in
                 (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26423) in
               FStar_Errors.raise_error uu____26417 env1.range
             else
               (let uu___1871_26429 = env1 in
                {
                  solver = (uu___1871_26429.solver);
                  range = (uu___1871_26429.range);
                  curmodule = (uu___1871_26429.curmodule);
                  gamma = (uu___1871_26429.gamma);
                  gamma_sig = (uu___1871_26429.gamma_sig);
                  gamma_cache = (uu___1871_26429.gamma_cache);
                  modules = (uu___1871_26429.modules);
                  expected_typ = (uu___1871_26429.expected_typ);
                  sigtab = (uu___1871_26429.sigtab);
                  attrtab = (uu___1871_26429.attrtab);
                  instantiate_imp = (uu___1871_26429.instantiate_imp);
                  effects =
                    (let uu___1873_26431 = env1.effects in
                     {
                       decls = (uu___1873_26431.decls);
                       order = (uu___1873_26431.order);
                       joins = (uu___1873_26431.joins);
                       polymonadic_binds =
                         (uu___1873_26431.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___1871_26429.generalize);
                  letrecs = (uu___1871_26429.letrecs);
                  top_level = (uu___1871_26429.top_level);
                  check_uvars = (uu___1871_26429.check_uvars);
                  use_eq = (uu___1871_26429.use_eq);
                  use_eq_strict = (uu___1871_26429.use_eq_strict);
                  is_iface = (uu___1871_26429.is_iface);
                  admit = (uu___1871_26429.admit);
                  lax = (uu___1871_26429.lax);
                  lax_universes = (uu___1871_26429.lax_universes);
                  phase1 = (uu___1871_26429.phase1);
                  failhard = (uu___1871_26429.failhard);
                  nosynth = (uu___1871_26429.nosynth);
                  uvar_subtyping = (uu___1871_26429.uvar_subtyping);
                  tc_term = (uu___1871_26429.tc_term);
                  type_of = (uu___1871_26429.type_of);
                  universe_of = (uu___1871_26429.universe_of);
                  check_type_of = (uu___1871_26429.check_type_of);
                  use_bv_sorts = (uu___1871_26429.use_bv_sorts);
                  qtbl_name_and_index = (uu___1871_26429.qtbl_name_and_index);
                  normalized_eff_names =
                    (uu___1871_26429.normalized_eff_names);
                  fv_delta_depths = (uu___1871_26429.fv_delta_depths);
                  proof_ns = (uu___1871_26429.proof_ns);
                  synth_hook = (uu___1871_26429.synth_hook);
                  try_solve_implicits_hook =
                    (uu___1871_26429.try_solve_implicits_hook);
                  splice = (uu___1871_26429.splice);
                  mpreprocess = (uu___1871_26429.mpreprocess);
                  postprocess = (uu___1871_26429.postprocess);
                  identifier_info = (uu___1871_26429.identifier_info);
                  tc_hooks = (uu___1871_26429.tc_hooks);
                  dsenv = (uu___1871_26429.dsenv);
                  nbe = (uu___1871_26429.nbe);
                  strict_args_tab = (uu___1871_26429.strict_args_tab);
                  erasable_types_tab = (uu___1871_26429.erasable_types_tab);
                  enable_defer_to_tac = (uu___1871_26429.enable_defer_to_tac)
                }))
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1 ->
    fun b ->
      let uu___1877_26449 = env1 in
      {
        solver = (uu___1877_26449.solver);
        range = (uu___1877_26449.range);
        curmodule = (uu___1877_26449.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1877_26449.gamma_sig);
        gamma_cache = (uu___1877_26449.gamma_cache);
        modules = (uu___1877_26449.modules);
        expected_typ = (uu___1877_26449.expected_typ);
        sigtab = (uu___1877_26449.sigtab);
        attrtab = (uu___1877_26449.attrtab);
        instantiate_imp = (uu___1877_26449.instantiate_imp);
        effects = (uu___1877_26449.effects);
        generalize = (uu___1877_26449.generalize);
        letrecs = (uu___1877_26449.letrecs);
        top_level = (uu___1877_26449.top_level);
        check_uvars = (uu___1877_26449.check_uvars);
        use_eq = (uu___1877_26449.use_eq);
        use_eq_strict = (uu___1877_26449.use_eq_strict);
        is_iface = (uu___1877_26449.is_iface);
        admit = (uu___1877_26449.admit);
        lax = (uu___1877_26449.lax);
        lax_universes = (uu___1877_26449.lax_universes);
        phase1 = (uu___1877_26449.phase1);
        failhard = (uu___1877_26449.failhard);
        nosynth = (uu___1877_26449.nosynth);
        uvar_subtyping = (uu___1877_26449.uvar_subtyping);
        tc_term = (uu___1877_26449.tc_term);
        type_of = (uu___1877_26449.type_of);
        universe_of = (uu___1877_26449.universe_of);
        check_type_of = (uu___1877_26449.check_type_of);
        use_bv_sorts = (uu___1877_26449.use_bv_sorts);
        qtbl_name_and_index = (uu___1877_26449.qtbl_name_and_index);
        normalized_eff_names = (uu___1877_26449.normalized_eff_names);
        fv_delta_depths = (uu___1877_26449.fv_delta_depths);
        proof_ns = (uu___1877_26449.proof_ns);
        synth_hook = (uu___1877_26449.synth_hook);
        try_solve_implicits_hook = (uu___1877_26449.try_solve_implicits_hook);
        splice = (uu___1877_26449.splice);
        mpreprocess = (uu___1877_26449.mpreprocess);
        postprocess = (uu___1877_26449.postprocess);
        identifier_info = (uu___1877_26449.identifier_info);
        tc_hooks = (uu___1877_26449.tc_hooks);
        dsenv = (uu___1877_26449.dsenv);
        nbe = (uu___1877_26449.nbe);
        strict_args_tab = (uu___1877_26449.strict_args_tab);
        erasable_types_tab = (uu___1877_26449.erasable_types_tab);
        enable_defer_to_tac = (uu___1877_26449.enable_defer_to_tac)
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
            (let uu___1890_26507 = env1 in
             {
               solver = (uu___1890_26507.solver);
               range = (uu___1890_26507.range);
               curmodule = (uu___1890_26507.curmodule);
               gamma = rest;
               gamma_sig = (uu___1890_26507.gamma_sig);
               gamma_cache = (uu___1890_26507.gamma_cache);
               modules = (uu___1890_26507.modules);
               expected_typ = (uu___1890_26507.expected_typ);
               sigtab = (uu___1890_26507.sigtab);
               attrtab = (uu___1890_26507.attrtab);
               instantiate_imp = (uu___1890_26507.instantiate_imp);
               effects = (uu___1890_26507.effects);
               generalize = (uu___1890_26507.generalize);
               letrecs = (uu___1890_26507.letrecs);
               top_level = (uu___1890_26507.top_level);
               check_uvars = (uu___1890_26507.check_uvars);
               use_eq = (uu___1890_26507.use_eq);
               use_eq_strict = (uu___1890_26507.use_eq_strict);
               is_iface = (uu___1890_26507.is_iface);
               admit = (uu___1890_26507.admit);
               lax = (uu___1890_26507.lax);
               lax_universes = (uu___1890_26507.lax_universes);
               phase1 = (uu___1890_26507.phase1);
               failhard = (uu___1890_26507.failhard);
               nosynth = (uu___1890_26507.nosynth);
               uvar_subtyping = (uu___1890_26507.uvar_subtyping);
               tc_term = (uu___1890_26507.tc_term);
               type_of = (uu___1890_26507.type_of);
               universe_of = (uu___1890_26507.universe_of);
               check_type_of = (uu___1890_26507.check_type_of);
               use_bv_sorts = (uu___1890_26507.use_bv_sorts);
               qtbl_name_and_index = (uu___1890_26507.qtbl_name_and_index);
               normalized_eff_names = (uu___1890_26507.normalized_eff_names);
               fv_delta_depths = (uu___1890_26507.fv_delta_depths);
               proof_ns = (uu___1890_26507.proof_ns);
               synth_hook = (uu___1890_26507.synth_hook);
               try_solve_implicits_hook =
                 (uu___1890_26507.try_solve_implicits_hook);
               splice = (uu___1890_26507.splice);
               mpreprocess = (uu___1890_26507.mpreprocess);
               postprocess = (uu___1890_26507.postprocess);
               identifier_info = (uu___1890_26507.identifier_info);
               tc_hooks = (uu___1890_26507.tc_hooks);
               dsenv = (uu___1890_26507.dsenv);
               nbe = (uu___1890_26507.nbe);
               strict_args_tab = (uu___1890_26507.strict_args_tab);
               erasable_types_tab = (uu___1890_26507.erasable_types_tab);
               enable_defer_to_tac = (uu___1890_26507.enable_defer_to_tac)
             }))
    | uu____26508 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1 ->
    fun bs ->
      FStar_List.fold_left
        (fun env2 ->
           fun uu____26537 ->
             match uu____26537 with | (x, uu____26545) -> push_bv env2 x)
        env1 bs
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.binding)
  =
  fun x ->
    fun t ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___1904_26580 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1904_26580.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1904_26580.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
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
        let uu____26653 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____26653 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env1 univ_vars in
            let uu____26681 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____26681)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1 ->
    fun t ->
      let uu___1925_26697 = env1 in
      {
        solver = (uu___1925_26697.solver);
        range = (uu___1925_26697.range);
        curmodule = (uu___1925_26697.curmodule);
        gamma = (uu___1925_26697.gamma);
        gamma_sig = (uu___1925_26697.gamma_sig);
        gamma_cache = (uu___1925_26697.gamma_cache);
        modules = (uu___1925_26697.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1925_26697.sigtab);
        attrtab = (uu___1925_26697.attrtab);
        instantiate_imp = (uu___1925_26697.instantiate_imp);
        effects = (uu___1925_26697.effects);
        generalize = (uu___1925_26697.generalize);
        letrecs = (uu___1925_26697.letrecs);
        top_level = (uu___1925_26697.top_level);
        check_uvars = (uu___1925_26697.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1925_26697.use_eq_strict);
        is_iface = (uu___1925_26697.is_iface);
        admit = (uu___1925_26697.admit);
        lax = (uu___1925_26697.lax);
        lax_universes = (uu___1925_26697.lax_universes);
        phase1 = (uu___1925_26697.phase1);
        failhard = (uu___1925_26697.failhard);
        nosynth = (uu___1925_26697.nosynth);
        uvar_subtyping = (uu___1925_26697.uvar_subtyping);
        tc_term = (uu___1925_26697.tc_term);
        type_of = (uu___1925_26697.type_of);
        universe_of = (uu___1925_26697.universe_of);
        check_type_of = (uu___1925_26697.check_type_of);
        use_bv_sorts = (uu___1925_26697.use_bv_sorts);
        qtbl_name_and_index = (uu___1925_26697.qtbl_name_and_index);
        normalized_eff_names = (uu___1925_26697.normalized_eff_names);
        fv_delta_depths = (uu___1925_26697.fv_delta_depths);
        proof_ns = (uu___1925_26697.proof_ns);
        synth_hook = (uu___1925_26697.synth_hook);
        try_solve_implicits_hook = (uu___1925_26697.try_solve_implicits_hook);
        splice = (uu___1925_26697.splice);
        mpreprocess = (uu___1925_26697.mpreprocess);
        postprocess = (uu___1925_26697.postprocess);
        identifier_info = (uu___1925_26697.identifier_info);
        tc_hooks = (uu___1925_26697.tc_hooks);
        dsenv = (uu___1925_26697.dsenv);
        nbe = (uu___1925_26697.nbe);
        strict_args_tab = (uu___1925_26697.strict_args_tab);
        erasable_types_tab = (uu___1925_26697.erasable_types_tab);
        enable_defer_to_tac = (uu___1925_26697.enable_defer_to_tac)
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
    let uu____26728 = expected_typ env_ in
    ((let uu___1932_26734 = env_ in
      {
        solver = (uu___1932_26734.solver);
        range = (uu___1932_26734.range);
        curmodule = (uu___1932_26734.curmodule);
        gamma = (uu___1932_26734.gamma);
        gamma_sig = (uu___1932_26734.gamma_sig);
        gamma_cache = (uu___1932_26734.gamma_cache);
        modules = (uu___1932_26734.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1932_26734.sigtab);
        attrtab = (uu___1932_26734.attrtab);
        instantiate_imp = (uu___1932_26734.instantiate_imp);
        effects = (uu___1932_26734.effects);
        generalize = (uu___1932_26734.generalize);
        letrecs = (uu___1932_26734.letrecs);
        top_level = (uu___1932_26734.top_level);
        check_uvars = (uu___1932_26734.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1932_26734.use_eq_strict);
        is_iface = (uu___1932_26734.is_iface);
        admit = (uu___1932_26734.admit);
        lax = (uu___1932_26734.lax);
        lax_universes = (uu___1932_26734.lax_universes);
        phase1 = (uu___1932_26734.phase1);
        failhard = (uu___1932_26734.failhard);
        nosynth = (uu___1932_26734.nosynth);
        uvar_subtyping = (uu___1932_26734.uvar_subtyping);
        tc_term = (uu___1932_26734.tc_term);
        type_of = (uu___1932_26734.type_of);
        universe_of = (uu___1932_26734.universe_of);
        check_type_of = (uu___1932_26734.check_type_of);
        use_bv_sorts = (uu___1932_26734.use_bv_sorts);
        qtbl_name_and_index = (uu___1932_26734.qtbl_name_and_index);
        normalized_eff_names = (uu___1932_26734.normalized_eff_names);
        fv_delta_depths = (uu___1932_26734.fv_delta_depths);
        proof_ns = (uu___1932_26734.proof_ns);
        synth_hook = (uu___1932_26734.synth_hook);
        try_solve_implicits_hook = (uu___1932_26734.try_solve_implicits_hook);
        splice = (uu___1932_26734.splice);
        mpreprocess = (uu___1932_26734.mpreprocess);
        postprocess = (uu___1932_26734.postprocess);
        identifier_info = (uu___1932_26734.identifier_info);
        tc_hooks = (uu___1932_26734.tc_hooks);
        dsenv = (uu___1932_26734.dsenv);
        nbe = (uu___1932_26734.nbe);
        strict_args_tab = (uu___1932_26734.strict_args_tab);
        erasable_types_tab = (uu___1932_26734.erasable_types_tab);
        enable_defer_to_tac = (uu___1932_26734.enable_defer_to_tac)
      }), uu____26728)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26746 =
      let uu____26747 = FStar_Ident.id_of_text "" in [uu____26747] in
    FStar_Ident.lid_of_ids uu____26746 in
  fun env1 ->
    fun m ->
      let sigs =
        let uu____26754 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____26754
        then
          let uu____26759 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu____26759 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env1 sigs;
      (let uu___1940_26787 = env1 in
       {
         solver = (uu___1940_26787.solver);
         range = (uu___1940_26787.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1940_26787.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1940_26787.expected_typ);
         sigtab = (uu___1940_26787.sigtab);
         attrtab = (uu___1940_26787.attrtab);
         instantiate_imp = (uu___1940_26787.instantiate_imp);
         effects = (uu___1940_26787.effects);
         generalize = (uu___1940_26787.generalize);
         letrecs = (uu___1940_26787.letrecs);
         top_level = (uu___1940_26787.top_level);
         check_uvars = (uu___1940_26787.check_uvars);
         use_eq = (uu___1940_26787.use_eq);
         use_eq_strict = (uu___1940_26787.use_eq_strict);
         is_iface = (uu___1940_26787.is_iface);
         admit = (uu___1940_26787.admit);
         lax = (uu___1940_26787.lax);
         lax_universes = (uu___1940_26787.lax_universes);
         phase1 = (uu___1940_26787.phase1);
         failhard = (uu___1940_26787.failhard);
         nosynth = (uu___1940_26787.nosynth);
         uvar_subtyping = (uu___1940_26787.uvar_subtyping);
         tc_term = (uu___1940_26787.tc_term);
         type_of = (uu___1940_26787.type_of);
         universe_of = (uu___1940_26787.universe_of);
         check_type_of = (uu___1940_26787.check_type_of);
         use_bv_sorts = (uu___1940_26787.use_bv_sorts);
         qtbl_name_and_index = (uu___1940_26787.qtbl_name_and_index);
         normalized_eff_names = (uu___1940_26787.normalized_eff_names);
         fv_delta_depths = (uu___1940_26787.fv_delta_depths);
         proof_ns = (uu___1940_26787.proof_ns);
         synth_hook = (uu___1940_26787.synth_hook);
         try_solve_implicits_hook =
           (uu___1940_26787.try_solve_implicits_hook);
         splice = (uu___1940_26787.splice);
         mpreprocess = (uu___1940_26787.mpreprocess);
         postprocess = (uu___1940_26787.postprocess);
         identifier_info = (uu___1940_26787.identifier_info);
         tc_hooks = (uu___1940_26787.tc_hooks);
         dsenv = (uu___1940_26787.dsenv);
         nbe = (uu___1940_26787.nbe);
         strict_args_tab = (uu___1940_26787.strict_args_tab);
         erasable_types_tab = (uu___1940_26787.erasable_types_tab);
         enable_defer_to_tac = (uu___1940_26787.enable_defer_to_tac)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1 ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26839)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26843, (uu____26844, t)))::tl
          ->
          let uu____26865 =
            let uu____26868 = FStar_Syntax_Free.uvars t in
            ext out uu____26868 in
          aux uu____26865 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26871;
            FStar_Syntax_Syntax.index = uu____26872;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26880 =
            let uu____26883 = FStar_Syntax_Free.uvars t in
            ext out uu____26883 in
          aux uu____26880 tl in
    aux no_uvs env1.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1 ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26941)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26945, (uu____26946, t)))::tl
          ->
          let uu____26967 =
            let uu____26970 = FStar_Syntax_Free.univs t in
            ext out uu____26970 in
          aux uu____26967 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26973;
            FStar_Syntax_Syntax.index = uu____26974;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26982 =
            let uu____26985 = FStar_Syntax_Free.univs t in
            ext out uu____26985 in
          aux uu____26982 tl in
    aux no_univs env1.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env1 ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu____27047 = FStar_Util.set_add uname out in
          aux uu____27047 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____27050, (uu____27051, t)))::tl
          ->
          let uu____27072 =
            let uu____27075 = FStar_Syntax_Free.univnames t in
            ext out uu____27075 in
          aux uu____27072 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____27078;
            FStar_Syntax_Syntax.index = uu____27079;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____27087 =
            let uu____27090 = FStar_Syntax_Free.univnames t in
            ext out uu____27090 in
          aux uu____27087 tl in
    aux no_univ_names env1.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_27111 ->
            match uu___12_27111 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____27115 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____27128 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____27139 =
      let uu____27148 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____27148
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____27139 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1 -> bound_vars_of_bindings env1.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1 -> binders_of_bindings env1.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu____27196 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_27209 ->
              match uu___13_27209 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____27212 = FStar_Syntax_Print.bv_to_string x in
                  Prims.op_Hat "Binding_var " uu____27212
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____27216 = FStar_Ident.string_of_id u in
                  Prims.op_Hat "Binding_univ " uu____27216
              | FStar_Syntax_Syntax.Binding_lid (l, uu____27220) ->
                  let uu____27237 = FStar_Ident.string_of_lid l in
                  Prims.op_Hat "Binding_lid " uu____27237)) in
    FStar_All.pipe_right uu____27196 (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_27251 ->
    match uu___14_27251 with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____27257 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.op_Hat "Unfold " uu____27257
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____27280 ->
         fun v ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1 ->
    fun path ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([], uu____27335) -> true
        | (x::xs1, y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____27368, uu____27369) -> false in
      let uu____27383 =
        FStar_List.tryFind
          (fun uu____27405 ->
             match uu____27405 with | (p, uu____27416) -> str_i_prefix p path)
          env1.proof_ns in
      match uu____27383 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____27435, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____27465 = FStar_Ident.path_of_lid lid in
      should_enc_path env1 uu____27465
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___2083_27487 = e in
        {
          solver = (uu___2083_27487.solver);
          range = (uu___2083_27487.range);
          curmodule = (uu___2083_27487.curmodule);
          gamma = (uu___2083_27487.gamma);
          gamma_sig = (uu___2083_27487.gamma_sig);
          gamma_cache = (uu___2083_27487.gamma_cache);
          modules = (uu___2083_27487.modules);
          expected_typ = (uu___2083_27487.expected_typ);
          sigtab = (uu___2083_27487.sigtab);
          attrtab = (uu___2083_27487.attrtab);
          instantiate_imp = (uu___2083_27487.instantiate_imp);
          effects = (uu___2083_27487.effects);
          generalize = (uu___2083_27487.generalize);
          letrecs = (uu___2083_27487.letrecs);
          top_level = (uu___2083_27487.top_level);
          check_uvars = (uu___2083_27487.check_uvars);
          use_eq = (uu___2083_27487.use_eq);
          use_eq_strict = (uu___2083_27487.use_eq_strict);
          is_iface = (uu___2083_27487.is_iface);
          admit = (uu___2083_27487.admit);
          lax = (uu___2083_27487.lax);
          lax_universes = (uu___2083_27487.lax_universes);
          phase1 = (uu___2083_27487.phase1);
          failhard = (uu___2083_27487.failhard);
          nosynth = (uu___2083_27487.nosynth);
          uvar_subtyping = (uu___2083_27487.uvar_subtyping);
          tc_term = (uu___2083_27487.tc_term);
          type_of = (uu___2083_27487.type_of);
          universe_of = (uu___2083_27487.universe_of);
          check_type_of = (uu___2083_27487.check_type_of);
          use_bv_sorts = (uu___2083_27487.use_bv_sorts);
          qtbl_name_and_index = (uu___2083_27487.qtbl_name_and_index);
          normalized_eff_names = (uu___2083_27487.normalized_eff_names);
          fv_delta_depths = (uu___2083_27487.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2083_27487.synth_hook);
          try_solve_implicits_hook =
            (uu___2083_27487.try_solve_implicits_hook);
          splice = (uu___2083_27487.splice);
          mpreprocess = (uu___2083_27487.mpreprocess);
          postprocess = (uu___2083_27487.postprocess);
          identifier_info = (uu___2083_27487.identifier_info);
          tc_hooks = (uu___2083_27487.tc_hooks);
          dsenv = (uu___2083_27487.dsenv);
          nbe = (uu___2083_27487.nbe);
          strict_args_tab = (uu___2083_27487.strict_args_tab);
          erasable_types_tab = (uu___2083_27487.erasable_types_tab);
          enable_defer_to_tac = (uu___2083_27487.enable_defer_to_tac)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___2092_27535 = e in
      {
        solver = (uu___2092_27535.solver);
        range = (uu___2092_27535.range);
        curmodule = (uu___2092_27535.curmodule);
        gamma = (uu___2092_27535.gamma);
        gamma_sig = (uu___2092_27535.gamma_sig);
        gamma_cache = (uu___2092_27535.gamma_cache);
        modules = (uu___2092_27535.modules);
        expected_typ = (uu___2092_27535.expected_typ);
        sigtab = (uu___2092_27535.sigtab);
        attrtab = (uu___2092_27535.attrtab);
        instantiate_imp = (uu___2092_27535.instantiate_imp);
        effects = (uu___2092_27535.effects);
        generalize = (uu___2092_27535.generalize);
        letrecs = (uu___2092_27535.letrecs);
        top_level = (uu___2092_27535.top_level);
        check_uvars = (uu___2092_27535.check_uvars);
        use_eq = (uu___2092_27535.use_eq);
        use_eq_strict = (uu___2092_27535.use_eq_strict);
        is_iface = (uu___2092_27535.is_iface);
        admit = (uu___2092_27535.admit);
        lax = (uu___2092_27535.lax);
        lax_universes = (uu___2092_27535.lax_universes);
        phase1 = (uu___2092_27535.phase1);
        failhard = (uu___2092_27535.failhard);
        nosynth = (uu___2092_27535.nosynth);
        uvar_subtyping = (uu___2092_27535.uvar_subtyping);
        tc_term = (uu___2092_27535.tc_term);
        type_of = (uu___2092_27535.type_of);
        universe_of = (uu___2092_27535.universe_of);
        check_type_of = (uu___2092_27535.check_type_of);
        use_bv_sorts = (uu___2092_27535.use_bv_sorts);
        qtbl_name_and_index = (uu___2092_27535.qtbl_name_and_index);
        normalized_eff_names = (uu___2092_27535.normalized_eff_names);
        fv_delta_depths = (uu___2092_27535.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2092_27535.synth_hook);
        try_solve_implicits_hook = (uu___2092_27535.try_solve_implicits_hook);
        splice = (uu___2092_27535.splice);
        mpreprocess = (uu___2092_27535.mpreprocess);
        postprocess = (uu___2092_27535.postprocess);
        identifier_info = (uu___2092_27535.identifier_info);
        tc_hooks = (uu___2092_27535.tc_hooks);
        dsenv = (uu___2092_27535.dsenv);
        nbe = (uu___2092_27535.nbe);
        strict_args_tab = (uu___2092_27535.strict_args_tab);
        erasable_types_tab = (uu___2092_27535.erasable_types_tab);
        enable_defer_to_tac = (uu___2092_27535.enable_defer_to_tac)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____27551 = FStar_Syntax_Free.names t in
      let uu____27554 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____27551 uu____27554
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____27577 = unbound_vars e t in
      FStar_Util.set_is_empty uu____27577
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____27587 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____27587
let (string_of_proof_ns : env -> Prims.string) =
  fun env1 ->
    let aux uu____27608 =
      match uu____27608 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27628 = FStar_Ident.text_of_path p in
             Prims.op_Hat (if b then "+" else "-") uu____27628) in
    let uu____27636 =
      let uu____27640 = FStar_List.map aux env1.proof_ns in
      FStar_All.pipe_right uu____27640 FStar_List.rev in
    FStar_All.pipe_right uu____27636 (FStar_String.concat " ")
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
        FStar_TypeChecker_Common.deferred_to_tac = uu____27696;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([], []);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27714 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu____27714 with
                   | FStar_Pervasives_Native.Some uu____27718 -> true
                   | FStar_Pervasives_Native.None -> false)))
    | uu____27721 -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial;
        FStar_TypeChecker_Common.deferred_to_tac = uu____27731;
        FStar_TypeChecker_Common.deferred = uu____27732;
        FStar_TypeChecker_Common.univ_ineqs = uu____27733;
        FStar_TypeChecker_Common.implicits = uu____27734;_} -> true
    | uu____27744 -> false
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
          let uu___2138_27766 = g in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2138_27766.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2138_27766.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2138_27766.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2138_27766.FStar_TypeChecker_Common.implicits)
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
          let uu____27805 = FStar_Options.defensive () in
          if uu____27805
          then
            let s = FStar_Syntax_Free.names t in
            let uu____27811 =
              let uu____27813 =
                let uu____27815 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27815 in
              Prims.op_Negation uu____27813 in
            (if uu____27811
             then
               let uu____27822 =
                 let uu____27828 =
                   let uu____27830 = FStar_Syntax_Print.term_to_string t in
                   let uu____27832 =
                     let uu____27834 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____27834
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27830 uu____27832 in
                 (FStar_Errors.Warning_Defensive, uu____27828) in
               FStar_Errors.log_issue rng uu____27822
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
          let uu____27874 =
            let uu____27876 = FStar_Options.defensive () in
            Prims.op_Negation uu____27876 in
          if uu____27874
          then ()
          else
            (let uu____27881 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____27881 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____27907 =
            let uu____27909 = FStar_Options.defensive () in
            Prims.op_Negation uu____27909 in
          if uu____27907
          then ()
          else
            (let uu____27914 = bound_vars e in
             def_check_closed_in rng msg uu____27914 t)
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
          let uu___2175_27953 = g in
          let uu____27954 =
            let uu____27955 =
              let uu____27956 =
                let uu____27957 =
                  let uu____27974 =
                    let uu____27985 = FStar_Syntax_Syntax.as_arg e in
                    [uu____27985] in
                  (f, uu____27974) in
                FStar_Syntax_Syntax.Tm_app uu____27957 in
              FStar_Syntax_Syntax.mk uu____27956 f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun uu____28022 ->
                 FStar_TypeChecker_Common.NonTrivial uu____28022) uu____27955 in
          {
            FStar_TypeChecker_Common.guard_f = uu____27954;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2175_27953.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2175_27953.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2175_27953.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2175_27953.FStar_TypeChecker_Common.implicits)
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
          let uu___2182_28040 = g in
          let uu____28041 =
            let uu____28042 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____28042 in
          {
            FStar_TypeChecker_Common.guard_f = uu____28041;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2182_28040.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2182_28040.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2182_28040.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2182_28040.FStar_TypeChecker_Common.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___2187_28059 = g in
          let uu____28060 =
            let uu____28061 = map FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu____28061 in
          {
            FStar_TypeChecker_Common.guard_f = uu____28060;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2187_28059.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2187_28059.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2187_28059.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2187_28059.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2191_28063 = g in
          let uu____28064 =
            let uu____28065 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____28065 in
          {
            FStar_TypeChecker_Common.guard_f = uu____28064;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2191_28063.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2191_28063.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2191_28063.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2191_28063.FStar_TypeChecker_Common.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____28072 ->
        failwith "impossible"
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
                     fun f1 ->
                       let uu____28149 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____28149
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___2214_28156 = g in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2214_28156.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2214_28156.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2214_28156.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2214_28156.FStar_TypeChecker_Common.implicits)
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
               let uu____28190 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____28190
               then f1
               else
                 (let u =
                    env1.universe_of env1
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env1 ->
    fun binders ->
      fun g ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2229_28217 = g in
            let uu____28218 =
              let uu____28219 = close_forall env1 binders f in
              FStar_TypeChecker_Common.NonTrivial uu____28219 in
            {
              FStar_TypeChecker_Common.guard_f = uu____28218;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2229_28217.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2229_28217.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2229_28217.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2229_28217.FStar_TypeChecker_Common.implicits)
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
              let uu____28269 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
              match uu____28269 with
              | FStar_Pervasives_Native.Some
                  (uu____28294::(tm, uu____28296)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos in
                  (t, [], trivial_guard)
              | uu____28360 ->
                  let binders = all_binders env1 in
                  let gamma = env1.gamma in
                  let ctx_uvar =
                    let uu____28378 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____28378;
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
                    (let uu____28412 =
                       debug env1 (FStar_Options.Other "ImplicitTrace") in
                     if uu____28412
                     then
                       let uu____28416 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____28416
                     else ());
                    (let g =
                       let uu___2253_28422 = trivial_guard in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2253_28422.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2253_28422.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2253_28422.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2253_28422.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____28476 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28535 ->
                      fun b ->
                        match uu____28535 with
                        | (substs1, uvars, g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                            let ctx_uvar_meta_t =
                              match FStar_Pervasives_Native.snd b with
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                  t)) ->
                                  let uu____28587 =
                                    let uu____28588 =
                                      let uu____28595 = FStar_Dyn.mkdyn env1 in
                                      (uu____28595, t) in
                                    FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                      uu____28588 in
                                  FStar_Pervasives_Native.Some uu____28587
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr t)
                              | uu____28601 -> FStar_Pervasives_Native.None in
                            let uu____28604 =
                              let uu____28617 = reason b in
                              new_implicit_var_aux uu____28617 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                ctx_uvar_meta_t in
                            (match uu____28604 with
                             | (t, l_ctx_uvars, g_t) ->
                                 ((let uu____28645 =
                                     FStar_All.pipe_left (debug env1)
                                       (FStar_Options.Other
                                          "LayeredEffectsEqns") in
                                   if uu____28645
                                   then
                                     FStar_List.iter
                                       (fun uu____28658 ->
                                          match uu____28658 with
                                          | (ctx_uvar, uu____28664) ->
                                              let uu____28665 =
                                                FStar_Syntax_Print.ctx_uvar_to_string_no_reason
                                                  ctx_uvar in
                                              FStar_Util.print1
                                                "Layered Effect uvar : %s\n"
                                                uu____28665) l_ctx_uvars
                                   else ());
                                  (let uu____28670 =
                                     let uu____28673 =
                                       let uu____28676 =
                                         let uu____28677 =
                                           let uu____28684 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           (uu____28684, t) in
                                         FStar_Syntax_Syntax.NT uu____28677 in
                                       [uu____28676] in
                                     FStar_List.append substs1 uu____28673 in
                                   let uu____28695 = conj_guard g g_t in
                                   (uu____28670,
                                     (FStar_List.append uvars [t]),
                                     uu____28695)))))
                   (substs, [], trivial_guard)) in
            FStar_All.pipe_right uu____28476
              (fun uu____28724 ->
                 match uu____28724 with
                 | (uu____28741, uvars, g) -> (uvars, g))
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
                let uu____28782 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid in
                FStar_All.pipe_right uu____28782 FStar_Util.must in
              let uu____28799 = inst_tscheme_with post_ts [u] in
              match uu____28799 with
              | (uu____28804, post) ->
                  let uu____28806 =
                    let uu____28807 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                    [uu____28807] in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____28806 r in
            let uu____28840 =
              let uu____28841 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg in
              [uu____28841] in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____28840 r
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28877 -> ());
    push = (fun uu____28879 -> ());
    pop = (fun uu____28882 -> ());
    snapshot =
      (fun uu____28885 ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28904 -> fun uu____28905 -> ());
    encode_sig = (fun uu____28920 -> fun uu____28921 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____28927 =
             let uu____28934 = FStar_Options.peek () in (e, g, uu____28934) in
           [uu____28927]);
    solve = (fun uu____28950 -> fun uu____28951 -> fun uu____28952 -> ());
    finish = (fun uu____28959 -> ());
    refresh = (fun uu____28961 -> ())
  }
let (get_letrec_arity :
  env ->
    FStar_Syntax_Syntax.lbname -> Prims.int FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lbname ->
      let compare_either f1 f2 e1 e2 =
        match (e1, e2) with
        | (FStar_Util.Inl v1, FStar_Util.Inl v2) -> f1 v1 v2
        | (FStar_Util.Inr v1, FStar_Util.Inr v2) -> f2 v1 v2
        | uu____29070 -> false in
      let uu____29084 =
        FStar_Util.find_opt
          (fun uu____29118 ->
             match uu____29118 with
             | (lbname', uu____29134, uu____29135, uu____29136) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
      match uu____29084 with
      | FStar_Pervasives_Native.Some
          (uu____29150, arity, uu____29152, uu____29153) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None