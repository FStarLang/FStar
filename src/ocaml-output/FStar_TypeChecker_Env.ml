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
  fun projectee -> match projectee with | Beta -> true | uu____104 -> false
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____110 -> false
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____116 -> false
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____122 -> false
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Exclude _0 -> true | uu____129 -> false
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee -> match projectee with | Exclude _0 -> _0
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____141 -> false
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____147 -> false
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____153 -> false
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding -> true | uu____159 -> false
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Inlining -> true | uu____165 -> false
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee ->
    match projectee with | DoNotUnfoldPureLets -> true | uu____171 -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu____178 -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____193 -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____214 -> false
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____235 -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldTac -> true | uu____253 -> false
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PureSubtermsWithinComputations -> true
    | uu____259 -> false
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Simplify -> true | uu____265 -> false
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | EraseUniverses -> true | uu____271 -> false
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowUnboundUniverses -> true | uu____277 -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____283 -> false
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CompressUvars -> true | uu____289 -> false
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee ->
    match projectee with | NoFullNorm -> true | uu____295 -> false
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckNoUvars -> true | uu____301 -> false
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu____307 -> false
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Unascribe -> true | uu____313 -> false
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____319 -> false
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ForExtraction -> true | uu____325 -> false
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
      | uu____360 -> false
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | NoDelta -> true | uu____381 -> false
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | InliningDelta -> true | uu____387 -> false
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding_only -> true | uu____393 -> false
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Unfold _0 -> true | uu____400 -> false
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
           (fun uu___0_13123 ->
              match uu___0_13123 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13126 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst uu____13126 in
                  let uu____13127 =
                    let uu____13128 = FStar_Syntax_Subst.compress y in
                    uu____13128.FStar_Syntax_Syntax.n in
                  (match uu____13127 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13132 =
                         let uu___330_13133 = y1 in
                         let uu____13134 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___330_13133.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___330_13133.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13134
                         } in
                       FStar_Syntax_Syntax.Binding_var uu____13132
                   | uu____13137 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst ->
    fun env1 ->
      let uu___336_13149 = env1 in
      let uu____13150 = rename_gamma subst env1.gamma in
      {
        solver = (uu___336_13149.solver);
        range = (uu___336_13149.range);
        curmodule = (uu___336_13149.curmodule);
        gamma = uu____13150;
        gamma_sig = (uu___336_13149.gamma_sig);
        gamma_cache = (uu___336_13149.gamma_cache);
        modules = (uu___336_13149.modules);
        expected_typ = (uu___336_13149.expected_typ);
        sigtab = (uu___336_13149.sigtab);
        attrtab = (uu___336_13149.attrtab);
        instantiate_imp = (uu___336_13149.instantiate_imp);
        effects = (uu___336_13149.effects);
        generalize = (uu___336_13149.generalize);
        letrecs = (uu___336_13149.letrecs);
        top_level = (uu___336_13149.top_level);
        check_uvars = (uu___336_13149.check_uvars);
        use_eq = (uu___336_13149.use_eq);
        use_eq_strict = (uu___336_13149.use_eq_strict);
        is_iface = (uu___336_13149.is_iface);
        admit = (uu___336_13149.admit);
        lax = (uu___336_13149.lax);
        lax_universes = (uu___336_13149.lax_universes);
        phase1 = (uu___336_13149.phase1);
        failhard = (uu___336_13149.failhard);
        nosynth = (uu___336_13149.nosynth);
        uvar_subtyping = (uu___336_13149.uvar_subtyping);
        tc_term = (uu___336_13149.tc_term);
        type_of = (uu___336_13149.type_of);
        universe_of = (uu___336_13149.universe_of);
        check_type_of = (uu___336_13149.check_type_of);
        use_bv_sorts = (uu___336_13149.use_bv_sorts);
        qtbl_name_and_index = (uu___336_13149.qtbl_name_and_index);
        normalized_eff_names = (uu___336_13149.normalized_eff_names);
        fv_delta_depths = (uu___336_13149.fv_delta_depths);
        proof_ns = (uu___336_13149.proof_ns);
        synth_hook = (uu___336_13149.synth_hook);
        try_solve_implicits_hook = (uu___336_13149.try_solve_implicits_hook);
        splice = (uu___336_13149.splice);
        mpreprocess = (uu___336_13149.mpreprocess);
        postprocess = (uu___336_13149.postprocess);
        identifier_info = (uu___336_13149.identifier_info);
        tc_hooks = (uu___336_13149.tc_hooks);
        dsenv = (uu___336_13149.dsenv);
        nbe = (uu___336_13149.nbe);
        strict_args_tab = (uu___336_13149.strict_args_tab);
        erasable_types_tab = (uu___336_13149.erasable_types_tab);
        enable_defer_to_tac = (uu___336_13149.enable_defer_to_tac)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13157 -> fun uu____13158 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env1 -> env1.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___343_13178 = env1 in
      {
        solver = (uu___343_13178.solver);
        range = (uu___343_13178.range);
        curmodule = (uu___343_13178.curmodule);
        gamma = (uu___343_13178.gamma);
        gamma_sig = (uu___343_13178.gamma_sig);
        gamma_cache = (uu___343_13178.gamma_cache);
        modules = (uu___343_13178.modules);
        expected_typ = (uu___343_13178.expected_typ);
        sigtab = (uu___343_13178.sigtab);
        attrtab = (uu___343_13178.attrtab);
        instantiate_imp = (uu___343_13178.instantiate_imp);
        effects = (uu___343_13178.effects);
        generalize = (uu___343_13178.generalize);
        letrecs = (uu___343_13178.letrecs);
        top_level = (uu___343_13178.top_level);
        check_uvars = (uu___343_13178.check_uvars);
        use_eq = (uu___343_13178.use_eq);
        use_eq_strict = (uu___343_13178.use_eq_strict);
        is_iface = (uu___343_13178.is_iface);
        admit = (uu___343_13178.admit);
        lax = (uu___343_13178.lax);
        lax_universes = (uu___343_13178.lax_universes);
        phase1 = (uu___343_13178.phase1);
        failhard = (uu___343_13178.failhard);
        nosynth = (uu___343_13178.nosynth);
        uvar_subtyping = (uu___343_13178.uvar_subtyping);
        tc_term = (uu___343_13178.tc_term);
        type_of = (uu___343_13178.type_of);
        universe_of = (uu___343_13178.universe_of);
        check_type_of = (uu___343_13178.check_type_of);
        use_bv_sorts = (uu___343_13178.use_bv_sorts);
        qtbl_name_and_index = (uu___343_13178.qtbl_name_and_index);
        normalized_eff_names = (uu___343_13178.normalized_eff_names);
        fv_delta_depths = (uu___343_13178.fv_delta_depths);
        proof_ns = (uu___343_13178.proof_ns);
        synth_hook = (uu___343_13178.synth_hook);
        try_solve_implicits_hook = (uu___343_13178.try_solve_implicits_hook);
        splice = (uu___343_13178.splice);
        mpreprocess = (uu___343_13178.mpreprocess);
        postprocess = (uu___343_13178.postprocess);
        identifier_info = (uu___343_13178.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___343_13178.dsenv);
        nbe = (uu___343_13178.nbe);
        strict_args_tab = (uu___343_13178.strict_args_tab);
        erasable_types_tab = (uu___343_13178.erasable_types_tab);
        enable_defer_to_tac = (uu___343_13178.enable_defer_to_tac)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___347_13189 = e in
      let uu____13190 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
      {
        solver = (uu___347_13189.solver);
        range = (uu___347_13189.range);
        curmodule = (uu___347_13189.curmodule);
        gamma = (uu___347_13189.gamma);
        gamma_sig = (uu___347_13189.gamma_sig);
        gamma_cache = (uu___347_13189.gamma_cache);
        modules = (uu___347_13189.modules);
        expected_typ = (uu___347_13189.expected_typ);
        sigtab = (uu___347_13189.sigtab);
        attrtab = (uu___347_13189.attrtab);
        instantiate_imp = (uu___347_13189.instantiate_imp);
        effects = (uu___347_13189.effects);
        generalize = (uu___347_13189.generalize);
        letrecs = (uu___347_13189.letrecs);
        top_level = (uu___347_13189.top_level);
        check_uvars = (uu___347_13189.check_uvars);
        use_eq = (uu___347_13189.use_eq);
        use_eq_strict = (uu___347_13189.use_eq_strict);
        is_iface = (uu___347_13189.is_iface);
        admit = (uu___347_13189.admit);
        lax = (uu___347_13189.lax);
        lax_universes = (uu___347_13189.lax_universes);
        phase1 = (uu___347_13189.phase1);
        failhard = (uu___347_13189.failhard);
        nosynth = (uu___347_13189.nosynth);
        uvar_subtyping = (uu___347_13189.uvar_subtyping);
        tc_term = (uu___347_13189.tc_term);
        type_of = (uu___347_13189.type_of);
        universe_of = (uu___347_13189.universe_of);
        check_type_of = (uu___347_13189.check_type_of);
        use_bv_sorts = (uu___347_13189.use_bv_sorts);
        qtbl_name_and_index = (uu___347_13189.qtbl_name_and_index);
        normalized_eff_names = (uu___347_13189.normalized_eff_names);
        fv_delta_depths = (uu___347_13189.fv_delta_depths);
        proof_ns = (uu___347_13189.proof_ns);
        synth_hook = (uu___347_13189.synth_hook);
        try_solve_implicits_hook = (uu___347_13189.try_solve_implicits_hook);
        splice = (uu___347_13189.splice);
        mpreprocess = (uu___347_13189.mpreprocess);
        postprocess = (uu___347_13189.postprocess);
        identifier_info = (uu___347_13189.identifier_info);
        tc_hooks = (uu___347_13189.tc_hooks);
        dsenv = uu____13190;
        nbe = (uu___347_13189.nbe);
        strict_args_tab = (uu___347_13189.strict_args_tab);
        erasable_types_tab = (uu___347_13189.erasable_types_tab);
        enable_defer_to_tac = (uu___347_13189.enable_defer_to_tac)
      }
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e -> FStar_Syntax_DsEnv.dep_graph e.dsenv
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1 ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____13204 = FStar_Ident.string_of_lid env1.curmodule in
       FStar_Options.should_verify uu____13204)
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d ->
    fun q ->
      match (d, q) with
      | (NoDelta, uu____13215) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____13216,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____13217, FStar_Syntax_Syntax.Visible_default) -> true
      | (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu____13218 -> false
let (default_table_size : Prims.int) = (Prims.of_int (200))
let new_sigtab : 'uuuuuu13227 . unit -> 'uuuuuu13227 FStar_Util.smap =
  fun uu____13234 -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'uuuuuu13239 . unit -> 'uuuuuu13239 FStar_Util.smap =
  fun uu____13246 -> FStar_Util.smap_create (Prims.of_int (100))
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
                  let uu____13380 = new_gamma_cache () in
                  let uu____13383 = new_sigtab () in
                  let uu____13386 = new_sigtab () in
                  let uu____13393 =
                    let uu____13406 =
                      FStar_Util.smap_create (Prims.of_int (10)) in
                    (uu____13406, FStar_Pervasives_Native.None) in
                  let uu____13421 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu____13424 =
                    FStar_Util.smap_create (Prims.of_int (50)) in
                  let uu____13427 = FStar_Options.using_facts_from () in
                  let uu____13428 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty in
                  let uu____13431 = FStar_Syntax_DsEnv.empty_env deps in
                  let uu____13432 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu____13443 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13380;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13383;
                    attrtab = uu____13386;
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
                    qtbl_name_and_index = uu____13393;
                    normalized_eff_names = uu____13421;
                    fv_delta_depths = uu____13424;
                    proof_ns = uu____13427;
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
                    identifier_info = uu____13428;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13431;
                    nbe;
                    strict_args_tab = uu____13432;
                    erasable_types_tab = uu____13443;
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
  fun uu____13610 ->
    let uu____13611 = FStar_ST.op_Bang query_indices in
    match uu____13611 with
    | [] -> failwith "Empty query indices!"
    | uu____13648 ->
        let uu____13657 =
          let uu____13666 =
            let uu____13673 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____13673 in
          let uu____13710 = FStar_ST.op_Bang query_indices in uu____13666 ::
            uu____13710 in
        FStar_ST.op_Colon_Equals query_indices uu____13657
let (pop_query_indices : unit -> unit) =
  fun uu____13773 ->
    let uu____13774 = FStar_ST.op_Bang query_indices in
    match uu____13774 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13863 ->
    FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13893 ->
    match uu____13893 with
    | (l, n) ->
        let uu____13900 = FStar_ST.op_Bang query_indices in
        (match uu____13900 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____13985 -> failwith "Empty query indices")
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14004 ->
    let uu____14005 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____14005
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env1 ->
    (let uu____14054 =
       let uu____14057 = FStar_ST.op_Bang stack in env1 :: uu____14057 in
     FStar_ST.op_Colon_Equals stack uu____14054);
    (let uu___421_14080 = env1 in
     let uu____14081 = FStar_Util.smap_copy (gamma_cache env1) in
     let uu____14084 = FStar_Util.smap_copy (sigtab env1) in
     let uu____14087 = FStar_Util.smap_copy (attrtab env1) in
     let uu____14094 =
       let uu____14107 =
         let uu____14110 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu____14110 in
       let uu____14135 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu____14107, uu____14135) in
     let uu____14176 = FStar_Util.smap_copy env1.normalized_eff_names in
     let uu____14179 = FStar_Util.smap_copy env1.fv_delta_depths in
     let uu____14182 =
       let uu____14185 = FStar_ST.op_Bang env1.identifier_info in
       FStar_Util.mk_ref uu____14185 in
     let uu____14192 = FStar_Util.smap_copy env1.strict_args_tab in
     let uu____14203 = FStar_Util.smap_copy env1.erasable_types_tab in
     {
       solver = (uu___421_14080.solver);
       range = (uu___421_14080.range);
       curmodule = (uu___421_14080.curmodule);
       gamma = (uu___421_14080.gamma);
       gamma_sig = (uu___421_14080.gamma_sig);
       gamma_cache = uu____14081;
       modules = (uu___421_14080.modules);
       expected_typ = (uu___421_14080.expected_typ);
       sigtab = uu____14084;
       attrtab = uu____14087;
       instantiate_imp = (uu___421_14080.instantiate_imp);
       effects = (uu___421_14080.effects);
       generalize = (uu___421_14080.generalize);
       letrecs = (uu___421_14080.letrecs);
       top_level = (uu___421_14080.top_level);
       check_uvars = (uu___421_14080.check_uvars);
       use_eq = (uu___421_14080.use_eq);
       use_eq_strict = (uu___421_14080.use_eq_strict);
       is_iface = (uu___421_14080.is_iface);
       admit = (uu___421_14080.admit);
       lax = (uu___421_14080.lax);
       lax_universes = (uu___421_14080.lax_universes);
       phase1 = (uu___421_14080.phase1);
       failhard = (uu___421_14080.failhard);
       nosynth = (uu___421_14080.nosynth);
       uvar_subtyping = (uu___421_14080.uvar_subtyping);
       tc_term = (uu___421_14080.tc_term);
       type_of = (uu___421_14080.type_of);
       universe_of = (uu___421_14080.universe_of);
       check_type_of = (uu___421_14080.check_type_of);
       use_bv_sorts = (uu___421_14080.use_bv_sorts);
       qtbl_name_and_index = uu____14094;
       normalized_eff_names = uu____14176;
       fv_delta_depths = uu____14179;
       proof_ns = (uu___421_14080.proof_ns);
       synth_hook = (uu___421_14080.synth_hook);
       try_solve_implicits_hook = (uu___421_14080.try_solve_implicits_hook);
       splice = (uu___421_14080.splice);
       mpreprocess = (uu___421_14080.mpreprocess);
       postprocess = (uu___421_14080.postprocess);
       identifier_info = uu____14182;
       tc_hooks = (uu___421_14080.tc_hooks);
       dsenv = (uu___421_14080.dsenv);
       nbe = (uu___421_14080.nbe);
       strict_args_tab = uu____14192;
       erasable_types_tab = uu____14203;
       enable_defer_to_tac = (uu___421_14080.enable_defer_to_tac)
     })
let (pop_stack : unit -> env) =
  fun uu____14210 ->
    let uu____14211 = FStar_ST.op_Bang stack in
    match uu____14211 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____14239 -> failwith "Impossible: Too many pops"
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push_stack stack env1
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop_stack stack depth
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1 ->
    fun msg ->
      FStar_Util.atomically
        (fun uu____14311 ->
           let uu____14312 = snapshot_stack env1 in
           match uu____14312 with
           | (stack_depth, env2) ->
               let uu____14337 = snapshot_query_indices () in
               (match uu____14337 with
                | (query_indices_depth, ()) ->
                    let uu____14361 = (env2.solver).snapshot msg in
                    (match uu____14361 with
                     | (solver_depth, ()) ->
                         let uu____14403 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv in
                         (match uu____14403 with
                          | (dsenv_depth, dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___446_14449 = env2 in
                                 {
                                   solver = (uu___446_14449.solver);
                                   range = (uu___446_14449.range);
                                   curmodule = (uu___446_14449.curmodule);
                                   gamma = (uu___446_14449.gamma);
                                   gamma_sig = (uu___446_14449.gamma_sig);
                                   gamma_cache = (uu___446_14449.gamma_cache);
                                   modules = (uu___446_14449.modules);
                                   expected_typ =
                                     (uu___446_14449.expected_typ);
                                   sigtab = (uu___446_14449.sigtab);
                                   attrtab = (uu___446_14449.attrtab);
                                   instantiate_imp =
                                     (uu___446_14449.instantiate_imp);
                                   effects = (uu___446_14449.effects);
                                   generalize = (uu___446_14449.generalize);
                                   letrecs = (uu___446_14449.letrecs);
                                   top_level = (uu___446_14449.top_level);
                                   check_uvars = (uu___446_14449.check_uvars);
                                   use_eq = (uu___446_14449.use_eq);
                                   use_eq_strict =
                                     (uu___446_14449.use_eq_strict);
                                   is_iface = (uu___446_14449.is_iface);
                                   admit = (uu___446_14449.admit);
                                   lax = (uu___446_14449.lax);
                                   lax_universes =
                                     (uu___446_14449.lax_universes);
                                   phase1 = (uu___446_14449.phase1);
                                   failhard = (uu___446_14449.failhard);
                                   nosynth = (uu___446_14449.nosynth);
                                   uvar_subtyping =
                                     (uu___446_14449.uvar_subtyping);
                                   tc_term = (uu___446_14449.tc_term);
                                   type_of = (uu___446_14449.type_of);
                                   universe_of = (uu___446_14449.universe_of);
                                   check_type_of =
                                     (uu___446_14449.check_type_of);
                                   use_bv_sorts =
                                     (uu___446_14449.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___446_14449.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___446_14449.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___446_14449.fv_delta_depths);
                                   proof_ns = (uu___446_14449.proof_ns);
                                   synth_hook = (uu___446_14449.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___446_14449.try_solve_implicits_hook);
                                   splice = (uu___446_14449.splice);
                                   mpreprocess = (uu___446_14449.mpreprocess);
                                   postprocess = (uu___446_14449.postprocess);
                                   identifier_info =
                                     (uu___446_14449.identifier_info);
                                   tc_hooks = (uu___446_14449.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___446_14449.nbe);
                                   strict_args_tab =
                                     (uu___446_14449.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___446_14449.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___446_14449.enable_defer_to_tac)
                                 }))))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
          (fun uu____14480 ->
             let uu____14481 =
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
             match uu____14481 with
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
                             ((let uu____14607 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1 in
                               FStar_Common.runtime_assert uu____14607
                                 "Inconsistent stack state");
                              tcenv))))))
let (push : env -> Prims.string -> env) =
  fun env1 ->
    fun msg ->
      let uu____14618 = snapshot env1 msg in
      FStar_Pervasives_Native.snd uu____14618
let (pop : env -> Prims.string -> env) =
  fun env1 ->
    fun msg -> rollback env1.solver msg FStar_Pervasives_Native.None
let (incr_query_index : env -> env) =
  fun env1 ->
    let qix = peek_query_indices () in
    match env1.qtbl_name_and_index with
    | (uu____14645, FStar_Pervasives_Native.None) -> env1
    | (tbl, FStar_Pervasives_Native.Some (l, n)) ->
        let uu____14677 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14703 ->
                  match uu____14703 with
                  | (m, uu____14709) -> FStar_Ident.lid_equals l m)) in
        (match uu____14677 with
         | FStar_Pervasives_Native.None ->
             let next = n + Prims.int_one in
             (add_query_index (l, next);
              (let uu____14717 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu____14717 next);
              (let uu___491_14718 = env1 in
               {
                 solver = (uu___491_14718.solver);
                 range = (uu___491_14718.range);
                 curmodule = (uu___491_14718.curmodule);
                 gamma = (uu___491_14718.gamma);
                 gamma_sig = (uu___491_14718.gamma_sig);
                 gamma_cache = (uu___491_14718.gamma_cache);
                 modules = (uu___491_14718.modules);
                 expected_typ = (uu___491_14718.expected_typ);
                 sigtab = (uu___491_14718.sigtab);
                 attrtab = (uu___491_14718.attrtab);
                 instantiate_imp = (uu___491_14718.instantiate_imp);
                 effects = (uu___491_14718.effects);
                 generalize = (uu___491_14718.generalize);
                 letrecs = (uu___491_14718.letrecs);
                 top_level = (uu___491_14718.top_level);
                 check_uvars = (uu___491_14718.check_uvars);
                 use_eq = (uu___491_14718.use_eq);
                 use_eq_strict = (uu___491_14718.use_eq_strict);
                 is_iface = (uu___491_14718.is_iface);
                 admit = (uu___491_14718.admit);
                 lax = (uu___491_14718.lax);
                 lax_universes = (uu___491_14718.lax_universes);
                 phase1 = (uu___491_14718.phase1);
                 failhard = (uu___491_14718.failhard);
                 nosynth = (uu___491_14718.nosynth);
                 uvar_subtyping = (uu___491_14718.uvar_subtyping);
                 tc_term = (uu___491_14718.tc_term);
                 type_of = (uu___491_14718.type_of);
                 universe_of = (uu___491_14718.universe_of);
                 check_type_of = (uu___491_14718.check_type_of);
                 use_bv_sorts = (uu___491_14718.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___491_14718.normalized_eff_names);
                 fv_delta_depths = (uu___491_14718.fv_delta_depths);
                 proof_ns = (uu___491_14718.proof_ns);
                 synth_hook = (uu___491_14718.synth_hook);
                 try_solve_implicits_hook =
                   (uu___491_14718.try_solve_implicits_hook);
                 splice = (uu___491_14718.splice);
                 mpreprocess = (uu___491_14718.mpreprocess);
                 postprocess = (uu___491_14718.postprocess);
                 identifier_info = (uu___491_14718.identifier_info);
                 tc_hooks = (uu___491_14718.tc_hooks);
                 dsenv = (uu___491_14718.dsenv);
                 nbe = (uu___491_14718.nbe);
                 strict_args_tab = (uu___491_14718.strict_args_tab);
                 erasable_types_tab = (uu___491_14718.erasable_types_tab);
                 enable_defer_to_tac = (uu___491_14718.enable_defer_to_tac)
               }))
         | FStar_Pervasives_Native.Some (uu____14731, m) ->
             let next = m + Prims.int_one in
             (add_query_index (l, next);
              (let uu____14740 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu____14740 next);
              (let uu___500_14741 = env1 in
               {
                 solver = (uu___500_14741.solver);
                 range = (uu___500_14741.range);
                 curmodule = (uu___500_14741.curmodule);
                 gamma = (uu___500_14741.gamma);
                 gamma_sig = (uu___500_14741.gamma_sig);
                 gamma_cache = (uu___500_14741.gamma_cache);
                 modules = (uu___500_14741.modules);
                 expected_typ = (uu___500_14741.expected_typ);
                 sigtab = (uu___500_14741.sigtab);
                 attrtab = (uu___500_14741.attrtab);
                 instantiate_imp = (uu___500_14741.instantiate_imp);
                 effects = (uu___500_14741.effects);
                 generalize = (uu___500_14741.generalize);
                 letrecs = (uu___500_14741.letrecs);
                 top_level = (uu___500_14741.top_level);
                 check_uvars = (uu___500_14741.check_uvars);
                 use_eq = (uu___500_14741.use_eq);
                 use_eq_strict = (uu___500_14741.use_eq_strict);
                 is_iface = (uu___500_14741.is_iface);
                 admit = (uu___500_14741.admit);
                 lax = (uu___500_14741.lax);
                 lax_universes = (uu___500_14741.lax_universes);
                 phase1 = (uu___500_14741.phase1);
                 failhard = (uu___500_14741.failhard);
                 nosynth = (uu___500_14741.nosynth);
                 uvar_subtyping = (uu___500_14741.uvar_subtyping);
                 tc_term = (uu___500_14741.tc_term);
                 type_of = (uu___500_14741.type_of);
                 universe_of = (uu___500_14741.universe_of);
                 check_type_of = (uu___500_14741.check_type_of);
                 use_bv_sorts = (uu___500_14741.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___500_14741.normalized_eff_names);
                 fv_delta_depths = (uu___500_14741.fv_delta_depths);
                 proof_ns = (uu___500_14741.proof_ns);
                 synth_hook = (uu___500_14741.synth_hook);
                 try_solve_implicits_hook =
                   (uu___500_14741.try_solve_implicits_hook);
                 splice = (uu___500_14741.splice);
                 mpreprocess = (uu___500_14741.mpreprocess);
                 postprocess = (uu___500_14741.postprocess);
                 identifier_info = (uu___500_14741.identifier_info);
                 tc_hooks = (uu___500_14741.tc_hooks);
                 dsenv = (uu___500_14741.dsenv);
                 nbe = (uu___500_14741.nbe);
                 strict_args_tab = (uu___500_14741.strict_args_tab);
                 erasable_types_tab = (uu___500_14741.erasable_types_tab);
                 enable_defer_to_tac = (uu___500_14741.enable_defer_to_tac)
               })))
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____14764 = FStar_Ident.string_of_lid env1.curmodule in
      FStar_Options.debug_at_level uu____14764 l
let (set_range : env -> FStar_Range.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___507_14776 = e in
         {
           solver = (uu___507_14776.solver);
           range = r;
           curmodule = (uu___507_14776.curmodule);
           gamma = (uu___507_14776.gamma);
           gamma_sig = (uu___507_14776.gamma_sig);
           gamma_cache = (uu___507_14776.gamma_cache);
           modules = (uu___507_14776.modules);
           expected_typ = (uu___507_14776.expected_typ);
           sigtab = (uu___507_14776.sigtab);
           attrtab = (uu___507_14776.attrtab);
           instantiate_imp = (uu___507_14776.instantiate_imp);
           effects = (uu___507_14776.effects);
           generalize = (uu___507_14776.generalize);
           letrecs = (uu___507_14776.letrecs);
           top_level = (uu___507_14776.top_level);
           check_uvars = (uu___507_14776.check_uvars);
           use_eq = (uu___507_14776.use_eq);
           use_eq_strict = (uu___507_14776.use_eq_strict);
           is_iface = (uu___507_14776.is_iface);
           admit = (uu___507_14776.admit);
           lax = (uu___507_14776.lax);
           lax_universes = (uu___507_14776.lax_universes);
           phase1 = (uu___507_14776.phase1);
           failhard = (uu___507_14776.failhard);
           nosynth = (uu___507_14776.nosynth);
           uvar_subtyping = (uu___507_14776.uvar_subtyping);
           tc_term = (uu___507_14776.tc_term);
           type_of = (uu___507_14776.type_of);
           universe_of = (uu___507_14776.universe_of);
           check_type_of = (uu___507_14776.check_type_of);
           use_bv_sorts = (uu___507_14776.use_bv_sorts);
           qtbl_name_and_index = (uu___507_14776.qtbl_name_and_index);
           normalized_eff_names = (uu___507_14776.normalized_eff_names);
           fv_delta_depths = (uu___507_14776.fv_delta_depths);
           proof_ns = (uu___507_14776.proof_ns);
           synth_hook = (uu___507_14776.synth_hook);
           try_solve_implicits_hook =
             (uu___507_14776.try_solve_implicits_hook);
           splice = (uu___507_14776.splice);
           mpreprocess = (uu___507_14776.mpreprocess);
           postprocess = (uu___507_14776.postprocess);
           identifier_info = (uu___507_14776.identifier_info);
           tc_hooks = (uu___507_14776.tc_hooks);
           dsenv = (uu___507_14776.dsenv);
           nbe = (uu___507_14776.nbe);
           strict_args_tab = (uu___507_14776.strict_args_tab);
           erasable_types_tab = (uu___507_14776.erasable_types_tab);
           enable_defer_to_tac = (uu___507_14776.enable_defer_to_tac)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1 ->
    fun enabled ->
      let uu____14792 =
        let uu____14793 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____14793 enabled in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____14792
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun bv ->
      fun ty ->
        let uu____14821 =
          let uu____14822 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14822 bv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____14821
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun fv ->
      fun ty ->
        let uu____14850 =
          let uu____14851 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14851 fv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____14850
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1 ->
    fun ty_map ->
      let uu____14879 =
        let uu____14880 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____14880 ty_map in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____14879
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1 -> env1.modules
let (current_module : env -> FStar_Ident.lident) = fun env1 -> env1.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun lid ->
      let uu___524_14915 = env1 in
      {
        solver = (uu___524_14915.solver);
        range = (uu___524_14915.range);
        curmodule = lid;
        gamma = (uu___524_14915.gamma);
        gamma_sig = (uu___524_14915.gamma_sig);
        gamma_cache = (uu___524_14915.gamma_cache);
        modules = (uu___524_14915.modules);
        expected_typ = (uu___524_14915.expected_typ);
        sigtab = (uu___524_14915.sigtab);
        attrtab = (uu___524_14915.attrtab);
        instantiate_imp = (uu___524_14915.instantiate_imp);
        effects = (uu___524_14915.effects);
        generalize = (uu___524_14915.generalize);
        letrecs = (uu___524_14915.letrecs);
        top_level = (uu___524_14915.top_level);
        check_uvars = (uu___524_14915.check_uvars);
        use_eq = (uu___524_14915.use_eq);
        use_eq_strict = (uu___524_14915.use_eq_strict);
        is_iface = (uu___524_14915.is_iface);
        admit = (uu___524_14915.admit);
        lax = (uu___524_14915.lax);
        lax_universes = (uu___524_14915.lax_universes);
        phase1 = (uu___524_14915.phase1);
        failhard = (uu___524_14915.failhard);
        nosynth = (uu___524_14915.nosynth);
        uvar_subtyping = (uu___524_14915.uvar_subtyping);
        tc_term = (uu___524_14915.tc_term);
        type_of = (uu___524_14915.type_of);
        universe_of = (uu___524_14915.universe_of);
        check_type_of = (uu___524_14915.check_type_of);
        use_bv_sorts = (uu___524_14915.use_bv_sorts);
        qtbl_name_and_index = (uu___524_14915.qtbl_name_and_index);
        normalized_eff_names = (uu___524_14915.normalized_eff_names);
        fv_delta_depths = (uu___524_14915.fv_delta_depths);
        proof_ns = (uu___524_14915.proof_ns);
        synth_hook = (uu___524_14915.synth_hook);
        try_solve_implicits_hook = (uu___524_14915.try_solve_implicits_hook);
        splice = (uu___524_14915.splice);
        mpreprocess = (uu___524_14915.mpreprocess);
        postprocess = (uu___524_14915.postprocess);
        identifier_info = (uu___524_14915.identifier_info);
        tc_hooks = (uu___524_14915.tc_hooks);
        dsenv = (uu___524_14915.dsenv);
        nbe = (uu___524_14915.nbe);
        strict_args_tab = (uu___524_14915.strict_args_tab);
        erasable_types_tab = (uu___524_14915.erasable_types_tab);
        enable_defer_to_tac = (uu___524_14915.enable_defer_to_tac)
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
      let uu____14942 = FStar_Ident.string_of_lid lid in
      FStar_Util.smap_try_find (sigtab env1) uu____14942
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu____14952 =
      let uu____14953 = FStar_Ident.string_of_lid l in
      FStar_Util.format1 "Name \"%s\" not found" uu____14953 in
    (FStar_Errors.Fatal_NameNotFound, uu____14952)
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v ->
    let uu____14963 =
      let uu____14964 = FStar_Syntax_Print.bv_to_string v in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14964 in
    (FStar_Errors.Fatal_VariableNotFound, uu____14963)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14969 ->
    let uu____14970 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
    FStar_Syntax_Syntax.U_unif uu____14970
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
      | ((formals, t), uu____15066) ->
          let vs = mk_univ_subst formals us in
          let uu____15090 = FStar_Syntax_Subst.subst vs t in
          (us, uu____15090)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15106 ->
    match uu___1_15106 with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15132 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r ->
    fun t ->
      let uu____15151 = inst_tscheme t in
      match uu____15151 with
      | (us, t1) ->
          let uu____15162 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____15162)
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
          let uu____15180 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu____15181 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15180 uu____15181 in
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
        fun uu____15202 ->
          match uu____15202 with
          | (us, t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15215 =
                    let uu____15216 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us) in
                    let uu____15217 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts) in
                    let uu____15218 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname in
                    let uu____15219 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15216 uu____15217 uu____15218 uu____15219 in
                  failwith uu____15215)
               else ();
               (let uu____15221 = inst_tscheme_with (us, t) insts in
                FStar_Pervasives_Native.snd uu____15221))
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu____15235 -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____15241 -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____15247 -> false
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1 ->
    fun l ->
      let cur = current_module env1 in
      let uu____15259 =
        let uu____15260 = FStar_Ident.nsstr l in
        let uu____15261 = FStar_Ident.string_of_lid cur in
        uu____15260 = uu____15261 in
      if uu____15259
      then Yes
      else
        (let uu____15263 =
           let uu____15264 = FStar_Ident.nsstr l in
           let uu____15265 = FStar_Ident.string_of_lid cur in
           FStar_Util.starts_with uu____15264 uu____15265 in
         if uu____15263
         then
           let lns =
             let uu____15269 = FStar_Ident.ns_of_lid l in
             let uu____15272 =
               let uu____15275 = FStar_Ident.ident_of_lid l in [uu____15275] in
             FStar_List.append uu____15269 uu____15272 in
           let cur1 =
             let uu____15279 = FStar_Ident.ns_of_lid cur in
             let uu____15282 =
               let uu____15285 = FStar_Ident.ident_of_lid cur in
               [uu____15285] in
             FStar_List.append uu____15279 uu____15282 in
           let rec aux c l1 =
             match (c, l1) with
             | ([], uu____15309) -> Maybe
             | (uu____15316, []) -> No
             | (hd::tl, hd'::tl') when
                 let uu____15335 = FStar_Ident.string_of_id hd in
                 let uu____15336 = FStar_Ident.string_of_id hd' in
                 uu____15335 = uu____15336 -> aux tl tl'
             | uu____15337 -> No in
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
        (let uu____15387 = FStar_Ident.string_of_lid lid in
         FStar_Util.smap_add (gamma_cache env1) uu____15387 t);
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____15429 =
            let uu____15432 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (gamma_cache env1) uu____15432 in
          match uu____15429 with
          | FStar_Pervasives_Native.None ->
              let uu____15453 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_15506 ->
                     match uu___2_15506 with
                     | FStar_Syntax_Syntax.Binding_lid (l, (us_names, t))
                         when FStar_Ident.lid_equals lid l ->
                         let us =
                           FStar_List.map
                             (fun uu____15547 ->
                                FStar_Syntax_Syntax.U_name uu____15547)
                             us_names in
                         let uu____15548 =
                           let uu____15571 = FStar_Ident.range_of_lid l in
                           ((FStar_Util.Inl (us, t)), uu____15571) in
                         FStar_Pervasives_Native.Some uu____15548
                     | uu____15630 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu____15453
                (fun uu____15676 ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_15686 ->
                        match uu___3_15686 with
                        | (uu____15689,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               (ses, uu____15691);
                             FStar_Syntax_Syntax.sigrng = uu____15692;
                             FStar_Syntax_Syntax.sigquals = uu____15693;
                             FStar_Syntax_Syntax.sigmeta = uu____15694;
                             FStar_Syntax_Syntax.sigattrs = uu____15695;
                             FStar_Syntax_Syntax.sigopts = uu____15696;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu____15718 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu____15718
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
                                  uu____15766 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15773 -> cache t in
                            let uu____15774 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
                            (match uu____15774 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15780 =
                                   let uu____15781 =
                                     FStar_Ident.range_of_lid l in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15781) in
                                 maybe_cache uu____15780)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15849 = find_in_sigtab env1 lid in
         match uu____15849 with
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
      let uu____15929 = lookup_qname env1 lid in
      match uu____15929 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15950, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1 ->
    fun attr ->
      let uu____16061 = FStar_Util.smap_try_find (attrtab env1) attr in
      match uu____16061 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      let add_one env2 se1 attr =
        let uu____16103 =
          let uu____16106 = lookup_attr env2 attr in se1 :: uu____16106 in
        FStar_Util.smap_add (attrtab env2) attr uu____16103 in
      FStar_List.iter
        (fun attr ->
           let uu____16116 =
             let uu____16117 = FStar_Syntax_Subst.compress attr in
             uu____16117.FStar_Syntax_Syntax.n in
           match uu____16116 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16121 =
                 let uu____16122 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_Ident.string_of_lid uu____16122 in
               add_one env1 se uu____16121
           | uu____16123 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____16145) ->
          add_sigelts env1 ses
      | uu____16154 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l ->
                let uu____16162 = FStar_Ident.string_of_lid l in
                FStar_Util.smap_add (sigtab env1) uu____16162 se) lids;
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
        (fun uu___4_16194 ->
           match uu___4_16194 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____16204 =
                 let uu____16211 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname in
                 ((id.FStar_Syntax_Syntax.sort), uu____16211) in
               FStar_Pervasives_Native.Some uu____16204
           | uu____16220 -> FStar_Pervasives_Native.None)
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16281, lb::[]), uu____16283) ->
            let uu____16290 =
              let uu____16299 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____16308 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____16299, uu____16308) in
            FStar_Pervasives_Native.Some uu____16290
        | FStar_Syntax_Syntax.Sig_let ((uu____16321, lbs), uu____16323) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16353 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16365 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____16365
                     then
                       let uu____16376 =
                         let uu____16385 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____16394 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____16385, uu____16394) in
                       FStar_Pervasives_Native.Some uu____16376
                     else FStar_Pervasives_Native.None)
        | uu____16416 -> FStar_Pervasives_Native.None
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
                    let uu____16506 =
                      let uu____16507 =
                        let uu____16508 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname in
                        let uu____16509 =
                          let uu____16510 =
                            let uu____16511 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature)) in
                            let uu____16516 =
                              let uu____16517 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us) in
                              Prims.op_Hat ", got " uu____16517 in
                            Prims.op_Hat uu____16511 uu____16516 in
                          Prims.op_Hat ", expected " uu____16510 in
                        Prims.op_Hat uu____16508 uu____16509 in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16507 in
                    failwith uu____16506
                  else ());
             (let uu____16519 =
                let uu____16528 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature in
                (uu____16528, (se.FStar_Syntax_Syntax.sigrng)) in
              FStar_Pervasives_Native.Some uu____16519))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid, us, binders, uu____16548, uu____16549) ->
            let uu____16554 =
              let uu____16563 =
                let uu____16568 =
                  let uu____16569 =
                    let uu____16572 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                    FStar_Syntax_Util.arrow binders uu____16572 in
                  (us, uu____16569) in
                inst_ts us_opt uu____16568 in
              (uu____16563, (se.FStar_Syntax_Syntax.sigrng)) in
            FStar_Pervasives_Native.Some uu____16554
        | uu____16591 -> FStar_Pervasives_Native.None
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
        let mapper uu____16679 =
          match uu____16679 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16775, uvs, t, uu____16778, uu____16779,
                         uu____16780);
                      FStar_Syntax_Syntax.sigrng = uu____16781;
                      FStar_Syntax_Syntax.sigquals = uu____16782;
                      FStar_Syntax_Syntax.sigmeta = uu____16783;
                      FStar_Syntax_Syntax.sigattrs = uu____16784;
                      FStar_Syntax_Syntax.sigopts = uu____16785;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____16808 =
                     let uu____16817 = inst_tscheme1 (uvs, t) in
                     (uu____16817, rng) in
                   FStar_Pervasives_Native.Some uu____16808
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____16841;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16843;
                      FStar_Syntax_Syntax.sigattrs = uu____16844;
                      FStar_Syntax_Syntax.sigopts = uu____16845;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____16864 =
                     let uu____16865 = in_cur_mod env1 l in uu____16865 = Yes in
                   if uu____16864
                   then
                     let uu____16876 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface in
                     (if uu____16876
                      then
                        let uu____16889 =
                          let uu____16898 = inst_tscheme1 (uvs, t) in
                          (uu____16898, rng) in
                        FStar_Pervasives_Native.Some uu____16889
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16929 =
                        let uu____16938 = inst_tscheme1 (uvs, t) in
                        (uu____16938, rng) in
                      FStar_Pervasives_Native.Some uu____16929)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____16963, uu____16964);
                      FStar_Syntax_Syntax.sigrng = uu____16965;
                      FStar_Syntax_Syntax.sigquals = uu____16966;
                      FStar_Syntax_Syntax.sigmeta = uu____16967;
                      FStar_Syntax_Syntax.sigattrs = uu____16968;
                      FStar_Syntax_Syntax.sigopts = uu____16969;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17012 =
                          let uu____17021 = inst_tscheme1 (uvs, k) in
                          (uu____17021, rng) in
                        FStar_Pervasives_Native.Some uu____17012
                    | uu____17042 ->
                        let uu____17043 =
                          let uu____17052 =
                            let uu____17057 =
                              let uu____17058 =
                                let uu____17061 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____17061 in
                              (uvs, uu____17058) in
                            inst_tscheme1 uu____17057 in
                          (uu____17052, rng) in
                        FStar_Pervasives_Native.Some uu____17043)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____17084, uu____17085);
                      FStar_Syntax_Syntax.sigrng = uu____17086;
                      FStar_Syntax_Syntax.sigquals = uu____17087;
                      FStar_Syntax_Syntax.sigmeta = uu____17088;
                      FStar_Syntax_Syntax.sigattrs = uu____17089;
                      FStar_Syntax_Syntax.sigopts = uu____17090;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17134 =
                          let uu____17143 = inst_tscheme_with (uvs, k) us in
                          (uu____17143, rng) in
                        FStar_Pervasives_Native.Some uu____17134
                    | uu____17164 ->
                        let uu____17165 =
                          let uu____17174 =
                            let uu____17179 =
                              let uu____17180 =
                                let uu____17183 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____17183 in
                              (uvs, uu____17180) in
                            inst_tscheme_with uu____17179 us in
                          (uu____17174, rng) in
                        FStar_Pervasives_Native.Some uu____17165)
               | FStar_Util.Inr se ->
                   let uu____17219 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17240;
                          FStar_Syntax_Syntax.sigrng = uu____17241;
                          FStar_Syntax_Syntax.sigquals = uu____17242;
                          FStar_Syntax_Syntax.sigmeta = uu____17243;
                          FStar_Syntax_Syntax.sigattrs = uu____17244;
                          FStar_Syntax_Syntax.sigopts = uu____17245;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17262 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range in
                   FStar_All.pipe_right uu____17219
                     (FStar_Util.map_option
                        (fun uu____17310 ->
                           match uu____17310 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____17341 =
          let uu____17352 = lookup_qname env1 lid in
          FStar_Util.bind_opt uu____17352 mapper in
        match uu____17341 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____17426 =
              let uu____17437 =
                let uu____17444 =
                  let uu___863_17447 = t in
                  let uu____17448 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___863_17447.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17448;
                    FStar_Syntax_Syntax.vars =
                      (uu___863_17447.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____17444) in
              (uu____17437, r) in
            FStar_Pervasives_Native.Some uu____17426
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____17495 = lookup_qname env1 l in
      match uu____17495 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____17514 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1 ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____17566 = try_lookup_bv env1 bv in
      match uu____17566 with
      | FStar_Pervasives_Native.None ->
          let uu____17581 = variable_not_found bv in
          FStar_Errors.raise_error uu____17581 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____17596 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____17597 =
            let uu____17598 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____17598 in
          (uu____17596, uu____17597)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____17619 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
      match uu____17619 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____17685 = FStar_Range.use_range use_range in
            FStar_Range.set_use_range r uu____17685 in
          let uu____17686 =
            let uu____17695 =
              let uu____17700 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____17700) in
            (uu____17695, r1) in
          FStar_Pervasives_Native.Some uu____17686
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
        let uu____17734 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l in
        match uu____17734 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17767, t), r) ->
            let use_range = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____17792 = FStar_Range.use_range use_range in
              FStar_Range.set_use_range r uu____17792 in
            let uu____17793 =
              let uu____17798 = FStar_Syntax_Subst.set_use_range use_range t in
              (uu____17798, r1) in
            FStar_Pervasives_Native.Some uu____17793
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1 ->
    fun l ->
      let uu____17821 = try_lookup_lid env1 l in
      match uu____17821 with
      | FStar_Pervasives_Native.None ->
          let uu____17848 = name_not_found l in
          let uu____17853 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____17848 uu____17853
      | FStar_Pervasives_Native.Some v -> v
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1 ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17895 ->
              match uu___5_17895 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____17897 = FStar_Ident.string_of_id x in
                  let uu____17898 = FStar_Ident.string_of_id y in
                  uu____17897 = uu____17898
              | uu____17899 -> false) env1.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____17918 = lookup_qname env1 lid in
      match uu____17918 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17927, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____17930;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17932;
              FStar_Syntax_Syntax.sigattrs = uu____17933;
              FStar_Syntax_Syntax.sigopts = uu____17934;_},
            FStar_Pervasives_Native.None),
           uu____17935)
          ->
          let uu____17986 =
            let uu____17993 =
              let uu____17994 =
                let uu____17997 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____17997 t in
              (uvs, uu____17994) in
            (uu____17993, q) in
          FStar_Pervasives_Native.Some uu____17986
      | uu____18010 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____18031 = lookup_qname env1 lid in
      match uu____18031 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18036, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____18039;
              FStar_Syntax_Syntax.sigquals = uu____18040;
              FStar_Syntax_Syntax.sigmeta = uu____18041;
              FStar_Syntax_Syntax.sigattrs = uu____18042;
              FStar_Syntax_Syntax.sigopts = uu____18043;_},
            FStar_Pervasives_Native.None),
           uu____18044)
          ->
          let uu____18095 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____18095 (uvs, t)
      | uu____18100 ->
          let uu____18101 = name_not_found lid in
          let uu____18106 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____18101 uu____18106
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____18125 = lookup_qname env1 lid in
      match uu____18125 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18130, uvs, t, uu____18133, uu____18134, uu____18135);
              FStar_Syntax_Syntax.sigrng = uu____18136;
              FStar_Syntax_Syntax.sigquals = uu____18137;
              FStar_Syntax_Syntax.sigmeta = uu____18138;
              FStar_Syntax_Syntax.sigattrs = uu____18139;
              FStar_Syntax_Syntax.sigopts = uu____18140;_},
            FStar_Pervasives_Native.None),
           uu____18141)
          ->
          let uu____18196 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____18196 (uvs, t)
      | uu____18201 ->
          let uu____18202 = name_not_found lid in
          let uu____18207 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____18202 uu____18207
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1 ->
    fun lid ->
      let uu____18228 = lookup_qname env1 lid in
      match uu____18228 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18235, uu____18236, uu____18237, uu____18238,
                 uu____18239, dcs);
              FStar_Syntax_Syntax.sigrng = uu____18241;
              FStar_Syntax_Syntax.sigquals = uu____18242;
              FStar_Syntax_Syntax.sigmeta = uu____18243;
              FStar_Syntax_Syntax.sigattrs = uu____18244;
              FStar_Syntax_Syntax.sigopts = uu____18245;_},
            uu____18246),
           uu____18247)
          -> (true, dcs)
      | uu____18310 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu____18323 = lookup_qname env1 lid in
      match uu____18323 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18324, uu____18325, uu____18326, l, uu____18328,
                 uu____18329);
              FStar_Syntax_Syntax.sigrng = uu____18330;
              FStar_Syntax_Syntax.sigquals = uu____18331;
              FStar_Syntax_Syntax.sigmeta = uu____18332;
              FStar_Syntax_Syntax.sigattrs = uu____18333;
              FStar_Syntax_Syntax.sigopts = uu____18334;_},
            uu____18335),
           uu____18336)
          -> l
      | uu____18393 ->
          let uu____18394 =
            let uu____18395 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____18395 in
          failwith uu____18394
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
               uu____18457)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu____18514)
                   when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        let uu____18536 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid in
                        if uu____18536
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18568 -> FStar_Pervasives_Native.None)
          | uu____18577 -> FStar_Pervasives_Native.None
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
        let uu____18636 = lookup_qname env1 lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18636
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
        let uu____18668 = lookup_qname env1 lid in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18668
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv ->
    fun qn ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____18690 =
        let uu____18691 = FStar_Ident.nsstr lid in uu____18691 = "Prims" in
      if uu____18690
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____18715, uu____18716) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se, uu____18764), uu____18765) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18814 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18831 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18840 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18855 ->
                  let uu____18862 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals in
                  FStar_Pervasives_Native.Some uu____18862
              | FStar_Syntax_Syntax.Sig_let ((uu____18863, lbs), uu____18865)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       let uu____18879 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid in
                       if uu____18879
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____18883 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____18896 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____18905 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18912 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18913 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18914 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18927 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____18928 ->
                  FStar_Pervasives_Native.None))
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____18950 =
        let uu____18951 = FStar_Ident.nsstr lid in uu____18951 = "Prims" in
      if uu____18950
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18953 =
           let uu____18956 = FStar_Ident.string_of_lid lid in
           FStar_All.pipe_right uu____18956
             (FStar_Util.smap_try_find env1.fv_delta_depths) in
         FStar_All.pipe_right uu____18953
           (fun d_opt ->
              let uu____18966 = FStar_All.pipe_right d_opt FStar_Util.is_some in
              if uu____18966
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18972 =
                   let uu____18975 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   delta_depth_of_qninfo fv uu____18975 in
                 match uu____18972 with
                 | FStar_Pervasives_Native.None ->
                     let uu____18976 =
                       let uu____18977 = FStar_Syntax_Print.fv_to_string fv in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18977 in
                     failwith uu____18976
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18980 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ()) in
                       if uu____18980
                       then
                         let uu____18981 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____18982 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta in
                         let uu____18983 =
                           FStar_Syntax_Print.delta_depth_to_string d in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18981 uu____18982 uu____18983
                       else ());
                      (let uu____18986 = FStar_Ident.string_of_lid lid in
                       FStar_Util.smap_add env1.fv_delta_depths uu____18986 d);
                      d))))
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____19005), uu____19006) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19055 -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____19076), uu____19077) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19126 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____19147 = lookup_qname env1 lid in
      FStar_All.pipe_left attrs_of_qninfo uu____19147
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____19175 = lookup_attrs_of_lid env1 fv_lid in
        match uu____19175 with
        | FStar_Pervasives_Native.None -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19191 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm ->
                      let uu____19198 =
                        let uu____19199 = FStar_Syntax_Util.un_uinst tm in
                        uu____19199.FStar_Syntax_Syntax.n in
                      match uu____19198 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19203 -> false)) in
            (true, uu____19191)
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____19219 = fv_exists_and_has_attr env1 fv_lid attr_lid in
        FStar_Pervasives_Native.snd uu____19219
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
          let uu____19281 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____19281 in
        let uu____19282 = FStar_Util.smap_try_find tab s in
        match uu____19282 with
        | FStar_Pervasives_Native.None ->
            let uu____19285 = f () in
            (match uu____19285 with
             | (should_cache, res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1 ->
    fun fv ->
      let f uu____19314 =
        let uu____19315 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr in
        match uu____19315 with | (ex, erasable) -> (ex, erasable) in
      cache_in_fv_tab env1.erasable_types_tab fv f
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____19336 =
        let uu____19337 = FStar_Syntax_Util.unrefine t in
        uu____19337.FStar_Syntax_Syntax.n in
      match uu____19336 with
      | FStar_Syntax_Syntax.Tm_type uu____19340 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head, uu____19343) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu____19369) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____19374, c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____19396 -> false
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fv ->
      let f uu____19424 =
        let attrs =
          let uu____19430 = FStar_Syntax_Syntax.lid_of_fv fv in
          lookup_attrs_of_lid env1 uu____19430 in
        match attrs with
        | FStar_Pervasives_Native.None ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x ->
                   let uu____19462 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr in
                   FStar_Pervasives_Native.fst uu____19462) in
            (true, res) in
      cache_in_fv_tab env1.strict_args_tab fv f
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ftv ->
      let uu____19497 = lookup_qname env1 ftv in
      match uu____19497 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____19501) ->
          let uu____19546 =
            effect_signature FStar_Pervasives_Native.None se env1.range in
          (match uu____19546 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19567, t), r) ->
               let uu____19582 =
                 let uu____19583 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____19583 t in
               FStar_Pervasives_Native.Some uu____19582)
      | uu____19584 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun ftv ->
      let uu____19595 = try_lookup_effect_lid env1 ftv in
      match uu____19595 with
      | FStar_Pervasives_Native.None ->
          let uu____19598 = name_not_found ftv in
          let uu____19603 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____19598 uu____19603
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
        let uu____19626 = lookup_qname env1 lid0 in
        match uu____19626 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs, binders, c, uu____19637);
                FStar_Syntax_Syntax.sigrng = uu____19638;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19640;
                FStar_Syntax_Syntax.sigattrs = uu____19641;
                FStar_Syntax_Syntax.sigopts = uu____19642;_},
              FStar_Pervasives_Native.None),
             uu____19643)
            ->
            let lid1 =
              let uu____19699 =
                let uu____19700 = FStar_Ident.range_of_lid lid in
                let uu____19701 =
                  let uu____19702 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____19702 in
                FStar_Range.set_use_range uu____19700 uu____19701 in
              FStar_Ident.set_lid_range lid uu____19699 in
            let uu____19703 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19707 ->
                      match uu___6_19707 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____19708 -> false)) in
            if uu____19703
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____19722 =
                      let uu____19723 =
                        let uu____19724 = get_range env1 in
                        FStar_Range.string_of_range uu____19724 in
                      let uu____19725 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____19726 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19723 uu____19725 uu____19726 in
                    failwith uu____19722) in
               match (binders, univs) with
               | ([], uu____19743) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19768, uu____19769::uu____19770::uu____19771) ->
                   let uu____19792 =
                     let uu____19793 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____19794 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19793 uu____19794 in
                   failwith uu____19792
               | uu____19801 ->
                   let uu____19816 =
                     let uu____19821 =
                       let uu____19822 = FStar_Syntax_Util.arrow binders c in
                       (univs, uu____19822) in
                     inst_tscheme_with uu____19821 insts in
                   (match uu____19816 with
                    | (uu____19835, t) ->
                        let t1 =
                          let uu____19838 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____19838 t in
                        let uu____19839 =
                          let uu____19840 = FStar_Syntax_Subst.compress t1 in
                          uu____19840.FStar_Syntax_Syntax.n in
                        (match uu____19839 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19875 -> failwith "Impossible")))
        | uu____19882 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun l ->
      let rec find l1 =
        let uu____19905 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____19905 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19918, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____19925 = find l2 in
            (match uu____19925 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____19932 =
          let uu____19935 = FStar_Ident.string_of_lid l in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____19935 in
        match uu____19932 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____19937 = find l in
            (match uu____19937 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____19942 = FStar_Ident.string_of_lid l in
                   FStar_Util.smap_add env1.normalized_eff_names uu____19942
                     m);
                  m)) in
      let uu____19943 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____19943
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1 ->
    fun name ->
      fun r ->
        let sig_t =
          let uu____19962 =
            FStar_All.pipe_right name (lookup_effect_lid env1) in
          FStar_All.pipe_right uu____19962 FStar_Syntax_Subst.compress in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs, uu____19967) ->
            FStar_List.length bs
        | uu____20006 ->
            let uu____20007 =
              let uu____20012 =
                let uu____20013 = FStar_Ident.string_of_lid name in
                let uu____20014 = FStar_Syntax_Print.term_to_string sig_t in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20013 uu____20014 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20012) in
            FStar_Errors.raise_error uu____20007 r
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1 ->
    fun l ->
      let l1 = norm_eff_name env1 l in
      let uu____20028 = lookup_qname env1 l1 in
      match uu____20028 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20031;
              FStar_Syntax_Syntax.sigrng = uu____20032;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20034;
              FStar_Syntax_Syntax.sigattrs = uu____20035;
              FStar_Syntax_Syntax.sigopts = uu____20036;_},
            uu____20037),
           uu____20038)
          -> q
      | uu____20091 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      fun i ->
        let fail uu____20112 =
          let uu____20113 =
            let uu____20114 = FStar_Util.string_of_int i in
            let uu____20115 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20114 uu____20115 in
          failwith uu____20113 in
        let uu____20116 = lookup_datacon env1 lid in
        match uu____20116 with
        | (uu____20121, t) ->
            let uu____20123 =
              let uu____20124 = FStar_Syntax_Subst.compress t in
              uu____20124.FStar_Syntax_Syntax.n in
            (match uu____20123 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____20128) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____20171 -> fail ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____20182 = lookup_qname env1 l in
      match uu____20182 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20183, uu____20184, uu____20185);
              FStar_Syntax_Syntax.sigrng = uu____20186;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20188;
              FStar_Syntax_Syntax.sigattrs = uu____20189;
              FStar_Syntax_Syntax.sigopts = uu____20190;_},
            uu____20191),
           uu____20192)
          ->
          FStar_Util.for_some
            (fun uu___7_20247 ->
               match uu___7_20247 with
               | FStar_Syntax_Syntax.Projector uu____20248 -> true
               | uu____20253 -> false) quals
      | uu____20254 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____20265 = lookup_qname env1 lid in
      match uu____20265 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20266, uu____20267, uu____20268, uu____20269,
                 uu____20270, uu____20271);
              FStar_Syntax_Syntax.sigrng = uu____20272;
              FStar_Syntax_Syntax.sigquals = uu____20273;
              FStar_Syntax_Syntax.sigmeta = uu____20274;
              FStar_Syntax_Syntax.sigattrs = uu____20275;
              FStar_Syntax_Syntax.sigopts = uu____20276;_},
            uu____20277),
           uu____20278)
          -> true
      | uu____20335 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____20346 = lookup_qname env1 lid in
      match uu____20346 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20347, uu____20348, uu____20349, uu____20350,
                 uu____20351, uu____20352);
              FStar_Syntax_Syntax.sigrng = uu____20353;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20355;
              FStar_Syntax_Syntax.sigattrs = uu____20356;
              FStar_Syntax_Syntax.sigopts = uu____20357;_},
            uu____20358),
           uu____20359)
          ->
          FStar_Util.for_some
            (fun uu___8_20422 ->
               match uu___8_20422 with
               | FStar_Syntax_Syntax.RecordType uu____20423 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20432 -> true
               | uu____20441 -> false) quals
      | uu____20442 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20448, uu____20449);
            FStar_Syntax_Syntax.sigrng = uu____20450;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20452;
            FStar_Syntax_Syntax.sigattrs = uu____20453;
            FStar_Syntax_Syntax.sigopts = uu____20454;_},
          uu____20455),
         uu____20456)
        ->
        FStar_Util.for_some
          (fun uu___9_20515 ->
             match uu___9_20515 with
             | FStar_Syntax_Syntax.Action uu____20516 -> true
             | uu____20517 -> false) quals
    | uu____20518 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____20529 = lookup_qname env1 lid in
      FStar_All.pipe_left qninfo_is_action uu____20529
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
      let uu____20543 =
        let uu____20544 = FStar_Syntax_Util.un_uinst head in
        uu____20544.FStar_Syntax_Syntax.n in
      match uu____20543 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20548 ->
               true
           | uu____20549 -> false)
      | uu____20550 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____20561 = lookup_qname env1 l in
      match uu____20561 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____20563), uu____20564) ->
          FStar_Util.for_some
            (fun uu___10_20612 ->
               match uu___10_20612 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____20613 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20614 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20685 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____20701) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20718 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20725 ->
                 FStar_Pervasives_Native.Some true
             | uu____20742 -> FStar_Pervasives_Native.Some false) in
      let uu____20743 =
        let uu____20746 = lookup_qname env1 lid in
        FStar_Util.bind_opt uu____20746 mapper in
      match uu____20743 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu____20798 = lookup_qname env1 lid in
      match uu____20798 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20801, uu____20802, tps, uu____20804, uu____20805,
                 uu____20806);
              FStar_Syntax_Syntax.sigrng = uu____20807;
              FStar_Syntax_Syntax.sigquals = uu____20808;
              FStar_Syntax_Syntax.sigmeta = uu____20809;
              FStar_Syntax_Syntax.sigattrs = uu____20810;
              FStar_Syntax_Syntax.sigopts = uu____20811;_},
            uu____20812),
           uu____20813)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20880 -> FStar_Pervasives_Native.None
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
           (fun uu____20924 ->
              match uu____20924 with
              | (d, uu____20932) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1 ->
    fun l ->
      let uu____20947 = effect_decl_opt env1 l in
      match uu____20947 with
      | FStar_Pervasives_Native.None ->
          let uu____20962 = name_not_found l in
          let uu____20967 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____20962 uu____20967
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____20993 = FStar_All.pipe_right l (get_effect_decl env1) in
      FStar_All.pipe_right uu____20993 FStar_Syntax_Util.is_layered
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____20998 ->
         fun c -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21012 ->
            fun uu____21013 -> fun e -> FStar_Util.return_all e))
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
        let uu____21046 = FStar_Ident.lid_equals l1 l2 in
        if uu____21046
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____21062 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____21062
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____21078 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21131 ->
                        match uu____21131 with
                        | (m1, m2, uu____21144, uu____21145, uu____21146) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____21078 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____21171, uu____21172, m3, j1, j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____21219 = join_opt env1 l1 l2 in
        match uu____21219 with
        | FStar_Pervasives_Native.None ->
            let uu____21240 =
              let uu____21245 =
                let uu____21246 = FStar_Syntax_Print.lid_to_string l1 in
                let uu____21247 = FStar_Syntax_Print.lid_to_string l2 in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____21246 uu____21247 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21245) in
            FStar_Errors.raise_error uu____21240 env1.range
        | FStar_Pervasives_Native.Some t -> t
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____21286 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____21286
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
  'uuuuuu21302 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu21302) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls ->
    fun m ->
      let uu____21331 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21357 ->
                match uu____21357 with
                | (d, uu____21363) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____21331 with
      | FStar_Pervasives_Native.None ->
          let uu____21374 =
            let uu____21375 = FStar_Ident.string_of_lid m in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____21375 in
          failwith uu____21374
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____21388 = inst_tscheme md.FStar_Syntax_Syntax.signature in
          (match uu____21388 with
           | (uu____21399, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____21417)::(wp, uu____21419)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21475 -> failwith "Impossible"))
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
        | uu____21537 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun comp ->
      let c = comp_to_comp_typ env1 comp in
      let uu____21549 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____21549 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____21566 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____21566 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21588 =
                     let uu____21593 =
                       let uu____21594 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____21601 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one) in
                       let uu____21610 =
                         let uu____21611 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____21611 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21594 uu____21601 uu____21610 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21593) in
                   FStar_Errors.raise_error uu____21588
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____21616 =
                     let uu____21627 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____21627 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____21664 ->
                        fun uu____21665 ->
                          match (uu____21664, uu____21665) with
                          | ((x, uu____21695), (t, uu____21697)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21616 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1 in
                 let c2 =
                   let uu____21728 =
                     let uu___1617_21729 = comp_to_comp_typ env1 c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1617_21729.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1617_21729.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1617_21729.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1617_21729.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____21728
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env1 c2)))
let effect_repr_aux :
  'uuuuuu21740 .
    'uuuuuu21740 ->
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
            let uu____21781 =
              let uu____21786 = num_effect_indices env1 eff_name r in
              ((FStar_List.length args), uu____21786) in
            match uu____21781 with
            | (given, expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____21799 = FStar_Ident.string_of_lid eff_name in
                     let uu____21800 = FStar_Util.string_of_int given in
                     let uu____21801 = FStar_Util.string_of_int expected in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____21799 uu____21800 uu____21801 in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r) in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c) in
          let uu____21803 = effect_decl_opt env1 effect_name in
          match uu____21803 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, uu____21825) ->
              let uu____21836 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              (match uu____21836 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____21854 =
                       let uu____21857 =
                         let uu____21858 =
                           let uu____21875 =
                             let uu____21886 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg in
                             uu____21886 ::
                               (c1.FStar_Syntax_Syntax.effect_args) in
                           (repr, uu____21875) in
                         FStar_Syntax_Syntax.Tm_app uu____21858 in
                       let uu____21923 = get_range env1 in
                       FStar_Syntax_Syntax.mk uu____21857 uu____21923 in
                     FStar_Pervasives_Native.Some uu____21854)))
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
           (fun uu___11_21977 ->
              match uu___11_21977 with
              | FStar_Syntax_Syntax.Reflectable uu____21978 -> true
              | uu____21979 -> false))
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
      | uu____22026 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____22037 =
        let uu____22038 = FStar_Syntax_Subst.compress t in
        uu____22038.FStar_Syntax_Syntax.n in
      match uu____22037 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22041, c) ->
          is_reifiable_comp env1 c
      | uu____22063 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu____22081 =
           let uu____22082 = is_reifiable_effect env1 l in
           Prims.op_Negation uu____22082 in
         if uu____22081
         then
           let uu____22083 =
             let uu____22088 =
               let uu____22089 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22089 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22088) in
           let uu____22090 = get_range env1 in
           FStar_Errors.raise_error uu____22083 uu____22090
         else ());
        (let uu____22092 = effect_repr_aux true env1 c u_c in
         match uu____22092 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env2 =
        let uu___1694_22124 = env1 in
        {
          solver = (uu___1694_22124.solver);
          range = (uu___1694_22124.range);
          curmodule = (uu___1694_22124.curmodule);
          gamma = (uu___1694_22124.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1694_22124.gamma_cache);
          modules = (uu___1694_22124.modules);
          expected_typ = (uu___1694_22124.expected_typ);
          sigtab = (uu___1694_22124.sigtab);
          attrtab = (uu___1694_22124.attrtab);
          instantiate_imp = (uu___1694_22124.instantiate_imp);
          effects = (uu___1694_22124.effects);
          generalize = (uu___1694_22124.generalize);
          letrecs = (uu___1694_22124.letrecs);
          top_level = (uu___1694_22124.top_level);
          check_uvars = (uu___1694_22124.check_uvars);
          use_eq = (uu___1694_22124.use_eq);
          use_eq_strict = (uu___1694_22124.use_eq_strict);
          is_iface = (uu___1694_22124.is_iface);
          admit = (uu___1694_22124.admit);
          lax = (uu___1694_22124.lax);
          lax_universes = (uu___1694_22124.lax_universes);
          phase1 = (uu___1694_22124.phase1);
          failhard = (uu___1694_22124.failhard);
          nosynth = (uu___1694_22124.nosynth);
          uvar_subtyping = (uu___1694_22124.uvar_subtyping);
          tc_term = (uu___1694_22124.tc_term);
          type_of = (uu___1694_22124.type_of);
          universe_of = (uu___1694_22124.universe_of);
          check_type_of = (uu___1694_22124.check_type_of);
          use_bv_sorts = (uu___1694_22124.use_bv_sorts);
          qtbl_name_and_index = (uu___1694_22124.qtbl_name_and_index);
          normalized_eff_names = (uu___1694_22124.normalized_eff_names);
          fv_delta_depths = (uu___1694_22124.fv_delta_depths);
          proof_ns = (uu___1694_22124.proof_ns);
          synth_hook = (uu___1694_22124.synth_hook);
          try_solve_implicits_hook =
            (uu___1694_22124.try_solve_implicits_hook);
          splice = (uu___1694_22124.splice);
          mpreprocess = (uu___1694_22124.mpreprocess);
          postprocess = (uu___1694_22124.postprocess);
          identifier_info = (uu___1694_22124.identifier_info);
          tc_hooks = (uu___1694_22124.tc_hooks);
          dsenv = (uu___1694_22124.dsenv);
          nbe = (uu___1694_22124.nbe);
          strict_args_tab = (uu___1694_22124.strict_args_tab);
          erasable_types_tab = (uu___1694_22124.erasable_types_tab);
          enable_defer_to_tac = (uu___1694_22124.enable_defer_to_tac)
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
    fun uu____22142 ->
      match uu____22142 with
      | (ed, quals) ->
          let effects1 =
            let uu___1703_22156 = env1.effects in
            {
              decls = (FStar_List.append (env1.effects).decls [(ed, quals)]);
              order = (uu___1703_22156.order);
              joins = (uu___1703_22156.joins);
              polymonadic_binds = (uu___1703_22156.polymonadic_binds);
              polymonadic_subcomps = (uu___1703_22156.polymonadic_subcomps)
            } in
          let uu___1706_22177 = env1 in
          {
            solver = (uu___1706_22177.solver);
            range = (uu___1706_22177.range);
            curmodule = (uu___1706_22177.curmodule);
            gamma = (uu___1706_22177.gamma);
            gamma_sig = (uu___1706_22177.gamma_sig);
            gamma_cache = (uu___1706_22177.gamma_cache);
            modules = (uu___1706_22177.modules);
            expected_typ = (uu___1706_22177.expected_typ);
            sigtab = (uu___1706_22177.sigtab);
            attrtab = (uu___1706_22177.attrtab);
            instantiate_imp = (uu___1706_22177.instantiate_imp);
            effects = effects1;
            generalize = (uu___1706_22177.generalize);
            letrecs = (uu___1706_22177.letrecs);
            top_level = (uu___1706_22177.top_level);
            check_uvars = (uu___1706_22177.check_uvars);
            use_eq = (uu___1706_22177.use_eq);
            use_eq_strict = (uu___1706_22177.use_eq_strict);
            is_iface = (uu___1706_22177.is_iface);
            admit = (uu___1706_22177.admit);
            lax = (uu___1706_22177.lax);
            lax_universes = (uu___1706_22177.lax_universes);
            phase1 = (uu___1706_22177.phase1);
            failhard = (uu___1706_22177.failhard);
            nosynth = (uu___1706_22177.nosynth);
            uvar_subtyping = (uu___1706_22177.uvar_subtyping);
            tc_term = (uu___1706_22177.tc_term);
            type_of = (uu___1706_22177.type_of);
            universe_of = (uu___1706_22177.universe_of);
            check_type_of = (uu___1706_22177.check_type_of);
            use_bv_sorts = (uu___1706_22177.use_bv_sorts);
            qtbl_name_and_index = (uu___1706_22177.qtbl_name_and_index);
            normalized_eff_names = (uu___1706_22177.normalized_eff_names);
            fv_delta_depths = (uu___1706_22177.fv_delta_depths);
            proof_ns = (uu___1706_22177.proof_ns);
            synth_hook = (uu___1706_22177.synth_hook);
            try_solve_implicits_hook =
              (uu___1706_22177.try_solve_implicits_hook);
            splice = (uu___1706_22177.splice);
            mpreprocess = (uu___1706_22177.mpreprocess);
            postprocess = (uu___1706_22177.postprocess);
            identifier_info = (uu___1706_22177.identifier_info);
            tc_hooks = (uu___1706_22177.tc_hooks);
            dsenv = (uu___1706_22177.dsenv);
            nbe = (uu___1706_22177.nbe);
            strict_args_tab = (uu___1706_22177.strict_args_tab);
            erasable_types_tab = (uu___1706_22177.erasable_types_tab);
            enable_defer_to_tac = (uu___1706_22177.enable_defer_to_tac)
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
        let uu____22205 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____22273 ->
                  match uu____22273 with
                  | (m1, n1, uu____22290, uu____22291) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____22205 with
        | FStar_Pervasives_Native.Some (uu____22316, uu____22317, p, t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____22362 -> FStar_Pervasives_Native.None
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun m ->
      fun n ->
        let uu____22406 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____22441 ->
                  match uu____22441 with
                  | (m1, n1, uu____22450) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____22406 with
        | FStar_Pervasives_Native.Some (uu____22453, uu____22454, ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____22462 -> FStar_Pervasives_Native.None
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1 ->
    fun src ->
      fun tgt ->
        fun st_mlift ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____22518 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2) in
                FStar_All.pipe_right uu____22518
                  (fun uu____22539 ->
                     match uu____22539 with
                     | (c1, g1) ->
                         let uu____22550 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2) in
                         FStar_All.pipe_right uu____22550
                           (fun uu____22571 ->
                              match uu____22571 with
                              | (c2, g2) ->
                                  let uu____22582 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2 in
                                  (c2, uu____22582))) in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun e ->
                              let uu____22704 = l1 u t e in
                              l2 u t uu____22704))
                | uu____22705 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let edge1 = { msource = src; mtarget = tgt; mlift = st_mlift } in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift } in
          let find_edge order uu____22766 =
            match uu____22766 with
            | (i, j) ->
                let uu____22777 = FStar_Ident.lid_equals i j in
                if uu____22777
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____22782 ->
                       FStar_Pervasives_Native.Some uu____22782)
                else
                  FStar_All.pipe_right order
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let ms =
            FStar_All.pipe_right (env1.effects).decls
              (FStar_List.map
                 (fun uu____22812 ->
                    match uu____22812 with
                    | (e, uu____22820) -> e.FStar_Syntax_Syntax.mname)) in
          let all_i_src =
            FStar_All.pipe_right ms
              (FStar_List.fold_left
                 (fun edges ->
                    fun i ->
                      let uu____22842 =
                        find_edge (env1.effects).order (i, (edge1.msource)) in
                      match uu____22842 with
                      | FStar_Pervasives_Native.Some e -> e :: edges
                      | FStar_Pervasives_Native.None -> edges) []) in
          let all_tgt_j =
            FStar_All.pipe_right ms
              (FStar_List.fold_left
                 (fun edges ->
                    fun j ->
                      let uu____22865 =
                        find_edge (env1.effects).order ((edge1.mtarget), j) in
                      match uu____22865 with
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
                          (let uu____22897 = FStar_Ident.lid_equals src1 tgt1 in
                           if uu____22897
                           then
                             let uu____22898 =
                               let uu____22903 =
                                 let uu____22904 =
                                   FStar_Ident.string_of_lid edge1.msource in
                                 let uu____22905 =
                                   FStar_Ident.string_of_lid edge1.mtarget in
                                 let uu____22906 =
                                   FStar_Ident.string_of_lid src1 in
                                 FStar_Util.format3
                                   "Adding an edge %s~>%s induces a cycle %s"
                                   uu____22904 uu____22905 uu____22906 in
                               (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                 uu____22903) in
                             FStar_Errors.raise_error uu____22898 env1.range
                           else ());
                          (let uu____22908 =
                             let uu____22909 =
                               find_edge (env1.effects).order (src1, tgt1) in
                             FStar_All.pipe_right uu____22909
                               FStar_Util.is_some in
                           if uu____22908
                           then edges1
                           else
                             (let uu____22917 =
                                (let uu____22920 =
                                   exists_polymonadic_subcomp env1 src1 tgt1 in
                                 FStar_All.pipe_right uu____22920
                                   FStar_Util.is_some)
                                  ||
                                  (let uu____22926 =
                                     exists_polymonadic_subcomp env1 tgt1
                                       src1 in
                                   FStar_All.pipe_right uu____22926
                                     FStar_Util.is_some) in
                              if uu____22917
                              then
                                let uu____22933 =
                                  let uu____22938 =
                                    let uu____22939 =
                                      FStar_Ident.string_of_lid edge1.msource in
                                    let uu____22940 =
                                      FStar_Ident.string_of_lid edge1.mtarget in
                                    let uu____22941 =
                                      FStar_Ident.string_of_lid src1 in
                                    let uu____22942 =
                                      FStar_Ident.string_of_lid tgt1 in
                                    FStar_Util.format4
                                      "Adding an edge %s~>%s induces an edge %s~>%s that conflicts with an existing polymonadic subcomp between them"
                                      uu____22939 uu____22940 uu____22941
                                      uu____22942 in
                                  (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                    uu____22938) in
                                FStar_Errors.raise_error uu____22933
                                  env1.range
                              else
                                (let uu____22946 =
                                   let uu____22947 =
                                     compose_edges i_src edge1 in
                                   compose_edges uu____22947 tgt_j in
                                 uu____22946 :: edges1)))) edges all_tgt_j)
              [] all_i_src in
          let order = FStar_List.append new_edges (env1.effects).order in
          FStar_All.pipe_right order
            (FStar_List.iter
               (fun edge2 ->
                  let uu____22959 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____22961 =
                         lookup_effect_quals env1 edge2.mtarget in
                       FStar_All.pipe_right uu____22961
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)) in
                  if uu____22959
                  then
                    let uu____22966 =
                      let uu____22971 =
                        let uu____22972 =
                          FStar_Ident.string_of_lid edge2.mtarget in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____22972 in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____22971) in
                    let uu____22973 = get_range env1 in
                    FStar_Errors.raise_error uu____22966 uu____22973
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j ->
                             let k_opt =
                               let uu____23050 = FStar_Ident.lid_equals i j in
                               if uu____23050
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt ->
                                         fun k ->
                                           let uu____23099 =
                                             let uu____23108 =
                                               find_edge order (i, k) in
                                             let uu____23111 =
                                               find_edge order (j, k) in
                                             (uu____23108, uu____23111) in
                                           match uu____23099 with
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
                                                    (ub, uu____23153,
                                                     uu____23154)
                                                    ->
                                                    let uu____23161 =
                                                      let uu____23166 =
                                                        let uu____23167 =
                                                          find_edge order
                                                            (k, ub) in
                                                        FStar_Util.is_some
                                                          uu____23167 in
                                                      let uu____23170 =
                                                        let uu____23171 =
                                                          find_edge order
                                                            (ub, k) in
                                                        FStar_Util.is_some
                                                          uu____23171 in
                                                      (uu____23166,
                                                        uu____23170) in
                                                    (match uu____23161 with
                                                     | (true, true) ->
                                                         let uu____23182 =
                                                           FStar_Ident.lid_equals
                                                             k ub in
                                                         if uu____23182
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
                                                         let uu____23201 =
                                                           let uu____23206 =
                                                             let uu____23207
                                                               =
                                                               FStar_Ident.string_of_lid
                                                                 i in
                                                             let uu____23208
                                                               =
                                                               FStar_Ident.string_of_lid
                                                                 j in
                                                             let uu____23209
                                                               =
                                                               FStar_Ident.string_of_lid
                                                                 k in
                                                             let uu____23210
                                                               =
                                                               FStar_Ident.string_of_lid
                                                                 ub in
                                                             FStar_Util.format4
                                                               "Uncomparable upper bounds! i=%s, j=%s, k=%s, ub=%s\n"
                                                               uu____23207
                                                               uu____23208
                                                               uu____23209
                                                               uu____23210 in
                                                           (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                                             uu____23206) in
                                                         FStar_Errors.raise_error
                                                           uu____23201
                                                           env1.range
                                                     | (true, false) ->
                                                         FStar_Pervasives_Native.Some
                                                           (k, ik, jk)
                                                     | (false, true) -> bopt))
                                           | uu____23225 -> bopt)
                                      FStar_Pervasives_Native.None) in
                             match k_opt with
                             | FStar_Pervasives_Native.None -> []
                             | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                 let uu____23277 =
                                   (let uu____23280 =
                                      exists_polymonadic_bind env1 i j in
                                    FStar_All.pipe_right uu____23280
                                      FStar_Util.is_some)
                                     ||
                                     (let uu____23316 =
                                        exists_polymonadic_bind env1 j i in
                                      FStar_All.pipe_right uu____23316
                                        FStar_Util.is_some) in
                                 if uu____23277
                                 then
                                   let uu____23363 =
                                     let uu____23368 =
                                       let uu____23369 =
                                         FStar_Ident.string_of_lid src in
                                       let uu____23370 =
                                         FStar_Ident.string_of_lid tgt in
                                       let uu____23371 =
                                         FStar_Ident.string_of_lid i in
                                       let uu____23372 =
                                         FStar_Ident.string_of_lid j in
                                       let uu____23373 =
                                         FStar_Ident.string_of_lid k in
                                       FStar_Util.format5
                                         "Updating effect lattice with a lift between %s and %s induces a least upper bound %s of %s and %s, and this conflicts with a polymonadic bind between them"
                                         uu____23369 uu____23370 uu____23371
                                         uu____23372 uu____23373 in
                                     (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                       uu____23368) in
                                   FStar_Errors.raise_error uu____23363
                                     env1.range
                                 else
                                   (let j_opt = join_opt env1 i j in
                                    let uu____23396 =
                                      (FStar_All.pipe_right j_opt
                                         FStar_Util.is_some)
                                        &&
                                        (let uu____23412 =
                                           let uu____23413 =
                                             let uu____23414 =
                                               FStar_All.pipe_right j_opt
                                                 FStar_Util.must in
                                             FStar_All.pipe_right uu____23414
                                               (fun uu____23451 ->
                                                  match uu____23451 with
                                                  | (l, uu____23459,
                                                     uu____23460) -> l) in
                                           FStar_Ident.lid_equals k
                                             uu____23413 in
                                         Prims.op_Negation uu____23412) in
                                    if uu____23396
                                    then
                                      let uu____23473 =
                                        let uu____23478 =
                                          let uu____23479 =
                                            FStar_Ident.string_of_lid src in
                                          let uu____23480 =
                                            FStar_Ident.string_of_lid tgt in
                                          let uu____23481 =
                                            FStar_Ident.string_of_lid i in
                                          let uu____23482 =
                                            FStar_Ident.string_of_lid j in
                                          let uu____23483 =
                                            FStar_Ident.string_of_lid k in
                                          let uu____23484 =
                                            let uu____23485 =
                                              let uu____23486 =
                                                FStar_All.pipe_right j_opt
                                                  FStar_Util.must in
                                              FStar_All.pipe_right
                                                uu____23486
                                                (fun uu____23523 ->
                                                   match uu____23523 with
                                                   | (l, uu____23531,
                                                      uu____23532) -> l) in
                                            FStar_All.pipe_right uu____23485
                                              FStar_Ident.string_of_lid in
                                          FStar_Util.format6
                                            "Updating effect lattice with %s ~> %s makes the least upper bound of %s and %s as %s, whereas earlier it was %s"
                                            uu____23479 uu____23480
                                            uu____23481 uu____23482
                                            uu____23483 uu____23484 in
                                        (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                                          uu____23478) in
                                      FStar_Errors.raise_error uu____23473
                                        env1.range
                                    else [(i, j, k, (e1.mlift), (e2.mlift))]))))) in
           let effects1 =
             let uu___1856_23567 = env1.effects in
             {
               decls = (uu___1856_23567.decls);
               order;
               joins;
               polymonadic_binds = (uu___1856_23567.polymonadic_binds);
               polymonadic_subcomps = (uu___1856_23567.polymonadic_subcomps)
             } in
           let uu___1859_23568 = env1 in
           {
             solver = (uu___1859_23568.solver);
             range = (uu___1859_23568.range);
             curmodule = (uu___1859_23568.curmodule);
             gamma = (uu___1859_23568.gamma);
             gamma_sig = (uu___1859_23568.gamma_sig);
             gamma_cache = (uu___1859_23568.gamma_cache);
             modules = (uu___1859_23568.modules);
             expected_typ = (uu___1859_23568.expected_typ);
             sigtab = (uu___1859_23568.sigtab);
             attrtab = (uu___1859_23568.attrtab);
             instantiate_imp = (uu___1859_23568.instantiate_imp);
             effects = effects1;
             generalize = (uu___1859_23568.generalize);
             letrecs = (uu___1859_23568.letrecs);
             top_level = (uu___1859_23568.top_level);
             check_uvars = (uu___1859_23568.check_uvars);
             use_eq = (uu___1859_23568.use_eq);
             use_eq_strict = (uu___1859_23568.use_eq_strict);
             is_iface = (uu___1859_23568.is_iface);
             admit = (uu___1859_23568.admit);
             lax = (uu___1859_23568.lax);
             lax_universes = (uu___1859_23568.lax_universes);
             phase1 = (uu___1859_23568.phase1);
             failhard = (uu___1859_23568.failhard);
             nosynth = (uu___1859_23568.nosynth);
             uvar_subtyping = (uu___1859_23568.uvar_subtyping);
             tc_term = (uu___1859_23568.tc_term);
             type_of = (uu___1859_23568.type_of);
             universe_of = (uu___1859_23568.universe_of);
             check_type_of = (uu___1859_23568.check_type_of);
             use_bv_sorts = (uu___1859_23568.use_bv_sorts);
             qtbl_name_and_index = (uu___1859_23568.qtbl_name_and_index);
             normalized_eff_names = (uu___1859_23568.normalized_eff_names);
             fv_delta_depths = (uu___1859_23568.fv_delta_depths);
             proof_ns = (uu___1859_23568.proof_ns);
             synth_hook = (uu___1859_23568.synth_hook);
             try_solve_implicits_hook =
               (uu___1859_23568.try_solve_implicits_hook);
             splice = (uu___1859_23568.splice);
             mpreprocess = (uu___1859_23568.mpreprocess);
             postprocess = (uu___1859_23568.postprocess);
             identifier_info = (uu___1859_23568.identifier_info);
             tc_hooks = (uu___1859_23568.tc_hooks);
             dsenv = (uu___1859_23568.dsenv);
             nbe = (uu___1859_23568.nbe);
             strict_args_tab = (uu___1859_23568.strict_args_tab);
             erasable_types_tab = (uu___1859_23568.erasable_types_tab);
             enable_defer_to_tac = (uu___1859_23568.enable_defer_to_tac)
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
              let uu____23612 = FStar_Ident.string_of_lid m in
              let uu____23613 = FStar_Ident.string_of_lid n in
              let uu____23614 = FStar_Ident.string_of_lid p in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____23612 uu____23613 uu____23614
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice") in
            let uu____23616 =
              let uu____23617 = exists_polymonadic_bind env1 m n in
              FStar_All.pipe_right uu____23617 FStar_Util.is_some in
            if uu____23616
            then
              let uu____23652 =
                let uu____23657 = err_msg true in
                (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu____23657) in
              FStar_Errors.raise_error uu____23652 env1.range
            else
              (let uu____23659 =
                 (let uu____23662 = join_opt env1 m n in
                  FStar_All.pipe_right uu____23662 FStar_Util.is_some) &&
                   (let uu____23686 = FStar_Ident.lid_equals m n in
                    Prims.op_Negation uu____23686) in
               if uu____23659
               then
                 let uu____23687 =
                   let uu____23692 = err_msg false in
                   (FStar_Errors.Fatal_Effects_Ordering_Coherence,
                     uu____23692) in
                 FStar_Errors.raise_error uu____23687 env1.range
               else
                 (let uu___1874_23694 = env1 in
                  {
                    solver = (uu___1874_23694.solver);
                    range = (uu___1874_23694.range);
                    curmodule = (uu___1874_23694.curmodule);
                    gamma = (uu___1874_23694.gamma);
                    gamma_sig = (uu___1874_23694.gamma_sig);
                    gamma_cache = (uu___1874_23694.gamma_cache);
                    modules = (uu___1874_23694.modules);
                    expected_typ = (uu___1874_23694.expected_typ);
                    sigtab = (uu___1874_23694.sigtab);
                    attrtab = (uu___1874_23694.attrtab);
                    instantiate_imp = (uu___1874_23694.instantiate_imp);
                    effects =
                      (let uu___1876_23696 = env1.effects in
                       {
                         decls = (uu___1876_23696.decls);
                         order = (uu___1876_23696.order);
                         joins = (uu___1876_23696.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1876_23696.polymonadic_subcomps)
                       });
                    generalize = (uu___1874_23694.generalize);
                    letrecs = (uu___1874_23694.letrecs);
                    top_level = (uu___1874_23694.top_level);
                    check_uvars = (uu___1874_23694.check_uvars);
                    use_eq = (uu___1874_23694.use_eq);
                    use_eq_strict = (uu___1874_23694.use_eq_strict);
                    is_iface = (uu___1874_23694.is_iface);
                    admit = (uu___1874_23694.admit);
                    lax = (uu___1874_23694.lax);
                    lax_universes = (uu___1874_23694.lax_universes);
                    phase1 = (uu___1874_23694.phase1);
                    failhard = (uu___1874_23694.failhard);
                    nosynth = (uu___1874_23694.nosynth);
                    uvar_subtyping = (uu___1874_23694.uvar_subtyping);
                    tc_term = (uu___1874_23694.tc_term);
                    type_of = (uu___1874_23694.type_of);
                    universe_of = (uu___1874_23694.universe_of);
                    check_type_of = (uu___1874_23694.check_type_of);
                    use_bv_sorts = (uu___1874_23694.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1874_23694.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1874_23694.normalized_eff_names);
                    fv_delta_depths = (uu___1874_23694.fv_delta_depths);
                    proof_ns = (uu___1874_23694.proof_ns);
                    synth_hook = (uu___1874_23694.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1874_23694.try_solve_implicits_hook);
                    splice = (uu___1874_23694.splice);
                    mpreprocess = (uu___1874_23694.mpreprocess);
                    postprocess = (uu___1874_23694.postprocess);
                    identifier_info = (uu___1874_23694.identifier_info);
                    tc_hooks = (uu___1874_23694.tc_hooks);
                    dsenv = (uu___1874_23694.dsenv);
                    nbe = (uu___1874_23694.nbe);
                    strict_args_tab = (uu___1874_23694.strict_args_tab);
                    erasable_types_tab = (uu___1874_23694.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1874_23694.enable_defer_to_tac)
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
            let uu____23783 = FStar_Ident.string_of_lid m in
            let uu____23784 = FStar_Ident.string_of_lid n in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu____23783 uu____23784
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice") in
          let uu____23786 =
            (let uu____23789 = exists_polymonadic_subcomp env1 m n in
             FStar_All.pipe_right uu____23789 FStar_Util.is_some) ||
              (let uu____23795 = exists_polymonadic_subcomp env1 n m in
               FStar_All.pipe_right uu____23795 FStar_Util.is_some) in
          if uu____23786
          then
            let uu____23800 =
              let uu____23805 = err_msg true in
              (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu____23805) in
            FStar_Errors.raise_error uu____23800 env1.range
          else
            (let uu____23807 =
               (let uu____23810 = monad_leq env1 m n in
                FStar_All.pipe_right uu____23810 FStar_Util.is_some) ||
                 (let uu____23816 = monad_leq env1 n m in
                  FStar_All.pipe_right uu____23816 FStar_Util.is_some) in
             if uu____23807
             then
               let uu____23821 =
                 let uu____23826 = err_msg false in
                 (FStar_Errors.Fatal_Effects_Ordering_Coherence, uu____23826) in
               FStar_Errors.raise_error uu____23821 env1.range
             else
               (let uu___1889_23828 = env1 in
                {
                  solver = (uu___1889_23828.solver);
                  range = (uu___1889_23828.range);
                  curmodule = (uu___1889_23828.curmodule);
                  gamma = (uu___1889_23828.gamma);
                  gamma_sig = (uu___1889_23828.gamma_sig);
                  gamma_cache = (uu___1889_23828.gamma_cache);
                  modules = (uu___1889_23828.modules);
                  expected_typ = (uu___1889_23828.expected_typ);
                  sigtab = (uu___1889_23828.sigtab);
                  attrtab = (uu___1889_23828.attrtab);
                  instantiate_imp = (uu___1889_23828.instantiate_imp);
                  effects =
                    (let uu___1891_23830 = env1.effects in
                     {
                       decls = (uu___1891_23830.decls);
                       order = (uu___1891_23830.order);
                       joins = (uu___1891_23830.joins);
                       polymonadic_binds =
                         (uu___1891_23830.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___1889_23828.generalize);
                  letrecs = (uu___1889_23828.letrecs);
                  top_level = (uu___1889_23828.top_level);
                  check_uvars = (uu___1889_23828.check_uvars);
                  use_eq = (uu___1889_23828.use_eq);
                  use_eq_strict = (uu___1889_23828.use_eq_strict);
                  is_iface = (uu___1889_23828.is_iface);
                  admit = (uu___1889_23828.admit);
                  lax = (uu___1889_23828.lax);
                  lax_universes = (uu___1889_23828.lax_universes);
                  phase1 = (uu___1889_23828.phase1);
                  failhard = (uu___1889_23828.failhard);
                  nosynth = (uu___1889_23828.nosynth);
                  uvar_subtyping = (uu___1889_23828.uvar_subtyping);
                  tc_term = (uu___1889_23828.tc_term);
                  type_of = (uu___1889_23828.type_of);
                  universe_of = (uu___1889_23828.universe_of);
                  check_type_of = (uu___1889_23828.check_type_of);
                  use_bv_sorts = (uu___1889_23828.use_bv_sorts);
                  qtbl_name_and_index = (uu___1889_23828.qtbl_name_and_index);
                  normalized_eff_names =
                    (uu___1889_23828.normalized_eff_names);
                  fv_delta_depths = (uu___1889_23828.fv_delta_depths);
                  proof_ns = (uu___1889_23828.proof_ns);
                  synth_hook = (uu___1889_23828.synth_hook);
                  try_solve_implicits_hook =
                    (uu___1889_23828.try_solve_implicits_hook);
                  splice = (uu___1889_23828.splice);
                  mpreprocess = (uu___1889_23828.mpreprocess);
                  postprocess = (uu___1889_23828.postprocess);
                  identifier_info = (uu___1889_23828.identifier_info);
                  tc_hooks = (uu___1889_23828.tc_hooks);
                  dsenv = (uu___1889_23828.dsenv);
                  nbe = (uu___1889_23828.nbe);
                  strict_args_tab = (uu___1889_23828.strict_args_tab);
                  erasable_types_tab = (uu___1889_23828.erasable_types_tab);
                  enable_defer_to_tac = (uu___1889_23828.enable_defer_to_tac)
                }))
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1 ->
    fun b ->
      let uu___1895_23847 = env1 in
      {
        solver = (uu___1895_23847.solver);
        range = (uu___1895_23847.range);
        curmodule = (uu___1895_23847.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1895_23847.gamma_sig);
        gamma_cache = (uu___1895_23847.gamma_cache);
        modules = (uu___1895_23847.modules);
        expected_typ = (uu___1895_23847.expected_typ);
        sigtab = (uu___1895_23847.sigtab);
        attrtab = (uu___1895_23847.attrtab);
        instantiate_imp = (uu___1895_23847.instantiate_imp);
        effects = (uu___1895_23847.effects);
        generalize = (uu___1895_23847.generalize);
        letrecs = (uu___1895_23847.letrecs);
        top_level = (uu___1895_23847.top_level);
        check_uvars = (uu___1895_23847.check_uvars);
        use_eq = (uu___1895_23847.use_eq);
        use_eq_strict = (uu___1895_23847.use_eq_strict);
        is_iface = (uu___1895_23847.is_iface);
        admit = (uu___1895_23847.admit);
        lax = (uu___1895_23847.lax);
        lax_universes = (uu___1895_23847.lax_universes);
        phase1 = (uu___1895_23847.phase1);
        failhard = (uu___1895_23847.failhard);
        nosynth = (uu___1895_23847.nosynth);
        uvar_subtyping = (uu___1895_23847.uvar_subtyping);
        tc_term = (uu___1895_23847.tc_term);
        type_of = (uu___1895_23847.type_of);
        universe_of = (uu___1895_23847.universe_of);
        check_type_of = (uu___1895_23847.check_type_of);
        use_bv_sorts = (uu___1895_23847.use_bv_sorts);
        qtbl_name_and_index = (uu___1895_23847.qtbl_name_and_index);
        normalized_eff_names = (uu___1895_23847.normalized_eff_names);
        fv_delta_depths = (uu___1895_23847.fv_delta_depths);
        proof_ns = (uu___1895_23847.proof_ns);
        synth_hook = (uu___1895_23847.synth_hook);
        try_solve_implicits_hook = (uu___1895_23847.try_solve_implicits_hook);
        splice = (uu___1895_23847.splice);
        mpreprocess = (uu___1895_23847.mpreprocess);
        postprocess = (uu___1895_23847.postprocess);
        identifier_info = (uu___1895_23847.identifier_info);
        tc_hooks = (uu___1895_23847.tc_hooks);
        dsenv = (uu___1895_23847.dsenv);
        nbe = (uu___1895_23847.nbe);
        strict_args_tab = (uu___1895_23847.strict_args_tab);
        erasable_types_tab = (uu___1895_23847.erasable_types_tab);
        enable_defer_to_tac = (uu___1895_23847.enable_defer_to_tac)
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
            (let uu___1908_23902 = env1 in
             {
               solver = (uu___1908_23902.solver);
               range = (uu___1908_23902.range);
               curmodule = (uu___1908_23902.curmodule);
               gamma = rest;
               gamma_sig = (uu___1908_23902.gamma_sig);
               gamma_cache = (uu___1908_23902.gamma_cache);
               modules = (uu___1908_23902.modules);
               expected_typ = (uu___1908_23902.expected_typ);
               sigtab = (uu___1908_23902.sigtab);
               attrtab = (uu___1908_23902.attrtab);
               instantiate_imp = (uu___1908_23902.instantiate_imp);
               effects = (uu___1908_23902.effects);
               generalize = (uu___1908_23902.generalize);
               letrecs = (uu___1908_23902.letrecs);
               top_level = (uu___1908_23902.top_level);
               check_uvars = (uu___1908_23902.check_uvars);
               use_eq = (uu___1908_23902.use_eq);
               use_eq_strict = (uu___1908_23902.use_eq_strict);
               is_iface = (uu___1908_23902.is_iface);
               admit = (uu___1908_23902.admit);
               lax = (uu___1908_23902.lax);
               lax_universes = (uu___1908_23902.lax_universes);
               phase1 = (uu___1908_23902.phase1);
               failhard = (uu___1908_23902.failhard);
               nosynth = (uu___1908_23902.nosynth);
               uvar_subtyping = (uu___1908_23902.uvar_subtyping);
               tc_term = (uu___1908_23902.tc_term);
               type_of = (uu___1908_23902.type_of);
               universe_of = (uu___1908_23902.universe_of);
               check_type_of = (uu___1908_23902.check_type_of);
               use_bv_sorts = (uu___1908_23902.use_bv_sorts);
               qtbl_name_and_index = (uu___1908_23902.qtbl_name_and_index);
               normalized_eff_names = (uu___1908_23902.normalized_eff_names);
               fv_delta_depths = (uu___1908_23902.fv_delta_depths);
               proof_ns = (uu___1908_23902.proof_ns);
               synth_hook = (uu___1908_23902.synth_hook);
               try_solve_implicits_hook =
                 (uu___1908_23902.try_solve_implicits_hook);
               splice = (uu___1908_23902.splice);
               mpreprocess = (uu___1908_23902.mpreprocess);
               postprocess = (uu___1908_23902.postprocess);
               identifier_info = (uu___1908_23902.identifier_info);
               tc_hooks = (uu___1908_23902.tc_hooks);
               dsenv = (uu___1908_23902.dsenv);
               nbe = (uu___1908_23902.nbe);
               strict_args_tab = (uu___1908_23902.strict_args_tab);
               erasable_types_tab = (uu___1908_23902.erasable_types_tab);
               enable_defer_to_tac = (uu___1908_23902.enable_defer_to_tac)
             }))
    | uu____23903 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1 ->
    fun bs ->
      FStar_List.fold_left
        (fun env2 ->
           fun uu____23931 ->
             match uu____23931 with | (x, uu____23939) -> push_bv env2 x)
        env1 bs
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.binding)
  =
  fun x ->
    fun t ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___1922_23969 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1922_23969.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1922_23969.FStar_Syntax_Syntax.index);
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
        let uu____24035 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____24035 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env1 univ_vars in
            let uu____24063 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____24063)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1 ->
    fun t ->
      let uu___1943_24078 = env1 in
      {
        solver = (uu___1943_24078.solver);
        range = (uu___1943_24078.range);
        curmodule = (uu___1943_24078.curmodule);
        gamma = (uu___1943_24078.gamma);
        gamma_sig = (uu___1943_24078.gamma_sig);
        gamma_cache = (uu___1943_24078.gamma_cache);
        modules = (uu___1943_24078.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1943_24078.sigtab);
        attrtab = (uu___1943_24078.attrtab);
        instantiate_imp = (uu___1943_24078.instantiate_imp);
        effects = (uu___1943_24078.effects);
        generalize = (uu___1943_24078.generalize);
        letrecs = (uu___1943_24078.letrecs);
        top_level = (uu___1943_24078.top_level);
        check_uvars = (uu___1943_24078.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1943_24078.use_eq_strict);
        is_iface = (uu___1943_24078.is_iface);
        admit = (uu___1943_24078.admit);
        lax = (uu___1943_24078.lax);
        lax_universes = (uu___1943_24078.lax_universes);
        phase1 = (uu___1943_24078.phase1);
        failhard = (uu___1943_24078.failhard);
        nosynth = (uu___1943_24078.nosynth);
        uvar_subtyping = (uu___1943_24078.uvar_subtyping);
        tc_term = (uu___1943_24078.tc_term);
        type_of = (uu___1943_24078.type_of);
        universe_of = (uu___1943_24078.universe_of);
        check_type_of = (uu___1943_24078.check_type_of);
        use_bv_sorts = (uu___1943_24078.use_bv_sorts);
        qtbl_name_and_index = (uu___1943_24078.qtbl_name_and_index);
        normalized_eff_names = (uu___1943_24078.normalized_eff_names);
        fv_delta_depths = (uu___1943_24078.fv_delta_depths);
        proof_ns = (uu___1943_24078.proof_ns);
        synth_hook = (uu___1943_24078.synth_hook);
        try_solve_implicits_hook = (uu___1943_24078.try_solve_implicits_hook);
        splice = (uu___1943_24078.splice);
        mpreprocess = (uu___1943_24078.mpreprocess);
        postprocess = (uu___1943_24078.postprocess);
        identifier_info = (uu___1943_24078.identifier_info);
        tc_hooks = (uu___1943_24078.tc_hooks);
        dsenv = (uu___1943_24078.dsenv);
        nbe = (uu___1943_24078.nbe);
        strict_args_tab = (uu___1943_24078.strict_args_tab);
        erasable_types_tab = (uu___1943_24078.erasable_types_tab);
        enable_defer_to_tac = (uu___1943_24078.enable_defer_to_tac)
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
    let uu____24106 = expected_typ env_ in
    ((let uu___1950_24112 = env_ in
      {
        solver = (uu___1950_24112.solver);
        range = (uu___1950_24112.range);
        curmodule = (uu___1950_24112.curmodule);
        gamma = (uu___1950_24112.gamma);
        gamma_sig = (uu___1950_24112.gamma_sig);
        gamma_cache = (uu___1950_24112.gamma_cache);
        modules = (uu___1950_24112.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1950_24112.sigtab);
        attrtab = (uu___1950_24112.attrtab);
        instantiate_imp = (uu___1950_24112.instantiate_imp);
        effects = (uu___1950_24112.effects);
        generalize = (uu___1950_24112.generalize);
        letrecs = (uu___1950_24112.letrecs);
        top_level = (uu___1950_24112.top_level);
        check_uvars = (uu___1950_24112.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1950_24112.use_eq_strict);
        is_iface = (uu___1950_24112.is_iface);
        admit = (uu___1950_24112.admit);
        lax = (uu___1950_24112.lax);
        lax_universes = (uu___1950_24112.lax_universes);
        phase1 = (uu___1950_24112.phase1);
        failhard = (uu___1950_24112.failhard);
        nosynth = (uu___1950_24112.nosynth);
        uvar_subtyping = (uu___1950_24112.uvar_subtyping);
        tc_term = (uu___1950_24112.tc_term);
        type_of = (uu___1950_24112.type_of);
        universe_of = (uu___1950_24112.universe_of);
        check_type_of = (uu___1950_24112.check_type_of);
        use_bv_sorts = (uu___1950_24112.use_bv_sorts);
        qtbl_name_and_index = (uu___1950_24112.qtbl_name_and_index);
        normalized_eff_names = (uu___1950_24112.normalized_eff_names);
        fv_delta_depths = (uu___1950_24112.fv_delta_depths);
        proof_ns = (uu___1950_24112.proof_ns);
        synth_hook = (uu___1950_24112.synth_hook);
        try_solve_implicits_hook = (uu___1950_24112.try_solve_implicits_hook);
        splice = (uu___1950_24112.splice);
        mpreprocess = (uu___1950_24112.mpreprocess);
        postprocess = (uu___1950_24112.postprocess);
        identifier_info = (uu___1950_24112.identifier_info);
        tc_hooks = (uu___1950_24112.tc_hooks);
        dsenv = (uu___1950_24112.dsenv);
        nbe = (uu___1950_24112.nbe);
        strict_args_tab = (uu___1950_24112.strict_args_tab);
        erasable_types_tab = (uu___1950_24112.erasable_types_tab);
        enable_defer_to_tac = (uu___1950_24112.enable_defer_to_tac)
      }), uu____24106)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24122 =
      let uu____24123 = FStar_Ident.id_of_text "" in [uu____24123] in
    FStar_Ident.lid_of_ids uu____24122 in
  fun env1 ->
    fun m ->
      let sigs =
        let uu____24129 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____24129
        then
          let uu____24132 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu____24132 FStar_List.rev
        else m.FStar_Syntax_Syntax.declarations in
      add_sigelts env1 sigs;
      (let uu___1958_24159 = env1 in
       {
         solver = (uu___1958_24159.solver);
         range = (uu___1958_24159.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1958_24159.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1958_24159.expected_typ);
         sigtab = (uu___1958_24159.sigtab);
         attrtab = (uu___1958_24159.attrtab);
         instantiate_imp = (uu___1958_24159.instantiate_imp);
         effects = (uu___1958_24159.effects);
         generalize = (uu___1958_24159.generalize);
         letrecs = (uu___1958_24159.letrecs);
         top_level = (uu___1958_24159.top_level);
         check_uvars = (uu___1958_24159.check_uvars);
         use_eq = (uu___1958_24159.use_eq);
         use_eq_strict = (uu___1958_24159.use_eq_strict);
         is_iface = (uu___1958_24159.is_iface);
         admit = (uu___1958_24159.admit);
         lax = (uu___1958_24159.lax);
         lax_universes = (uu___1958_24159.lax_universes);
         phase1 = (uu___1958_24159.phase1);
         failhard = (uu___1958_24159.failhard);
         nosynth = (uu___1958_24159.nosynth);
         uvar_subtyping = (uu___1958_24159.uvar_subtyping);
         tc_term = (uu___1958_24159.tc_term);
         type_of = (uu___1958_24159.type_of);
         universe_of = (uu___1958_24159.universe_of);
         check_type_of = (uu___1958_24159.check_type_of);
         use_bv_sorts = (uu___1958_24159.use_bv_sorts);
         qtbl_name_and_index = (uu___1958_24159.qtbl_name_and_index);
         normalized_eff_names = (uu___1958_24159.normalized_eff_names);
         fv_delta_depths = (uu___1958_24159.fv_delta_depths);
         proof_ns = (uu___1958_24159.proof_ns);
         synth_hook = (uu___1958_24159.synth_hook);
         try_solve_implicits_hook =
           (uu___1958_24159.try_solve_implicits_hook);
         splice = (uu___1958_24159.splice);
         mpreprocess = (uu___1958_24159.mpreprocess);
         postprocess = (uu___1958_24159.postprocess);
         identifier_info = (uu___1958_24159.identifier_info);
         tc_hooks = (uu___1958_24159.tc_hooks);
         dsenv = (uu___1958_24159.dsenv);
         nbe = (uu___1958_24159.nbe);
         strict_args_tab = (uu___1958_24159.strict_args_tab);
         erasable_types_tab = (uu___1958_24159.erasable_types_tab);
         enable_defer_to_tac = (uu___1958_24159.enable_defer_to_tac)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1 ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24210)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____24214, (uu____24215, t)))::tl
          ->
          let uu____24230 =
            let uu____24233 = FStar_Syntax_Free.uvars t in
            ext out uu____24233 in
          aux uu____24230 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24236;
            FStar_Syntax_Syntax.index = uu____24237;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____24244 =
            let uu____24247 = FStar_Syntax_Free.uvars t in
            ext out uu____24247 in
          aux uu____24244 tl in
    aux no_uvs env1.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1 ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24304)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____24308, (uu____24309, t)))::tl
          ->
          let uu____24324 =
            let uu____24327 = FStar_Syntax_Free.univs t in
            ext out uu____24327 in
          aux uu____24324 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24330;
            FStar_Syntax_Syntax.index = uu____24331;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____24338 =
            let uu____24341 = FStar_Syntax_Free.univs t in
            ext out uu____24341 in
          aux uu____24338 tl in
    aux no_univs env1.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env1 ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu____24402 = FStar_Util.set_add uname out in
          aux uu____24402 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____24405, (uu____24406, t)))::tl
          ->
          let uu____24421 =
            let uu____24424 = FStar_Syntax_Free.univnames t in
            ext out uu____24424 in
          aux uu____24421 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24427;
            FStar_Syntax_Syntax.index = uu____24428;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____24435 =
            let uu____24438 = FStar_Syntax_Free.univnames t in
            ext out uu____24438 in
          aux uu____24435 tl in
    aux no_univ_names env1.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24458 ->
            match uu___12_24458 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24462 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24473 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____24483 =
      let uu____24492 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____24492
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____24483 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1 -> bound_vars_of_bindings env1.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1 -> binders_of_bindings env1.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu____24536 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24546 ->
              match uu___13_24546 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24548 = FStar_Syntax_Print.bv_to_string x in
                  Prims.op_Hat "Binding_var " uu____24548
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____24550 = FStar_Ident.string_of_id u in
                  Prims.op_Hat "Binding_univ " uu____24550
              | FStar_Syntax_Syntax.Binding_lid (l, uu____24552) ->
                  let uu____24565 = FStar_Ident.string_of_lid l in
                  Prims.op_Hat "Binding_lid " uu____24565)) in
    FStar_All.pipe_right uu____24536 (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24572 ->
    match uu___14_24572 with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24574 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.op_Hat "Unfold " uu____24574
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____24594 ->
         fun v ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1 ->
    fun path ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([], uu____24636) -> true
        | (x::xs1, y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24655, uu____24656) -> false in
      let uu____24665 =
        FStar_List.tryFind
          (fun uu____24683 ->
             match uu____24683 with | (p, uu____24691) -> str_i_prefix p path)
          env1.proof_ns in
      match uu____24665 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____24702, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____24724 = FStar_Ident.path_of_lid lid in
      should_enc_path env1 uu____24724
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___2101_24742 = e in
        {
          solver = (uu___2101_24742.solver);
          range = (uu___2101_24742.range);
          curmodule = (uu___2101_24742.curmodule);
          gamma = (uu___2101_24742.gamma);
          gamma_sig = (uu___2101_24742.gamma_sig);
          gamma_cache = (uu___2101_24742.gamma_cache);
          modules = (uu___2101_24742.modules);
          expected_typ = (uu___2101_24742.expected_typ);
          sigtab = (uu___2101_24742.sigtab);
          attrtab = (uu___2101_24742.attrtab);
          instantiate_imp = (uu___2101_24742.instantiate_imp);
          effects = (uu___2101_24742.effects);
          generalize = (uu___2101_24742.generalize);
          letrecs = (uu___2101_24742.letrecs);
          top_level = (uu___2101_24742.top_level);
          check_uvars = (uu___2101_24742.check_uvars);
          use_eq = (uu___2101_24742.use_eq);
          use_eq_strict = (uu___2101_24742.use_eq_strict);
          is_iface = (uu___2101_24742.is_iface);
          admit = (uu___2101_24742.admit);
          lax = (uu___2101_24742.lax);
          lax_universes = (uu___2101_24742.lax_universes);
          phase1 = (uu___2101_24742.phase1);
          failhard = (uu___2101_24742.failhard);
          nosynth = (uu___2101_24742.nosynth);
          uvar_subtyping = (uu___2101_24742.uvar_subtyping);
          tc_term = (uu___2101_24742.tc_term);
          type_of = (uu___2101_24742.type_of);
          universe_of = (uu___2101_24742.universe_of);
          check_type_of = (uu___2101_24742.check_type_of);
          use_bv_sorts = (uu___2101_24742.use_bv_sorts);
          qtbl_name_and_index = (uu___2101_24742.qtbl_name_and_index);
          normalized_eff_names = (uu___2101_24742.normalized_eff_names);
          fv_delta_depths = (uu___2101_24742.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2101_24742.synth_hook);
          try_solve_implicits_hook =
            (uu___2101_24742.try_solve_implicits_hook);
          splice = (uu___2101_24742.splice);
          mpreprocess = (uu___2101_24742.mpreprocess);
          postprocess = (uu___2101_24742.postprocess);
          identifier_info = (uu___2101_24742.identifier_info);
          tc_hooks = (uu___2101_24742.tc_hooks);
          dsenv = (uu___2101_24742.dsenv);
          nbe = (uu___2101_24742.nbe);
          strict_args_tab = (uu___2101_24742.strict_args_tab);
          erasable_types_tab = (uu___2101_24742.erasable_types_tab);
          enable_defer_to_tac = (uu___2101_24742.enable_defer_to_tac)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___2110_24782 = e in
      {
        solver = (uu___2110_24782.solver);
        range = (uu___2110_24782.range);
        curmodule = (uu___2110_24782.curmodule);
        gamma = (uu___2110_24782.gamma);
        gamma_sig = (uu___2110_24782.gamma_sig);
        gamma_cache = (uu___2110_24782.gamma_cache);
        modules = (uu___2110_24782.modules);
        expected_typ = (uu___2110_24782.expected_typ);
        sigtab = (uu___2110_24782.sigtab);
        attrtab = (uu___2110_24782.attrtab);
        instantiate_imp = (uu___2110_24782.instantiate_imp);
        effects = (uu___2110_24782.effects);
        generalize = (uu___2110_24782.generalize);
        letrecs = (uu___2110_24782.letrecs);
        top_level = (uu___2110_24782.top_level);
        check_uvars = (uu___2110_24782.check_uvars);
        use_eq = (uu___2110_24782.use_eq);
        use_eq_strict = (uu___2110_24782.use_eq_strict);
        is_iface = (uu___2110_24782.is_iface);
        admit = (uu___2110_24782.admit);
        lax = (uu___2110_24782.lax);
        lax_universes = (uu___2110_24782.lax_universes);
        phase1 = (uu___2110_24782.phase1);
        failhard = (uu___2110_24782.failhard);
        nosynth = (uu___2110_24782.nosynth);
        uvar_subtyping = (uu___2110_24782.uvar_subtyping);
        tc_term = (uu___2110_24782.tc_term);
        type_of = (uu___2110_24782.type_of);
        universe_of = (uu___2110_24782.universe_of);
        check_type_of = (uu___2110_24782.check_type_of);
        use_bv_sorts = (uu___2110_24782.use_bv_sorts);
        qtbl_name_and_index = (uu___2110_24782.qtbl_name_and_index);
        normalized_eff_names = (uu___2110_24782.normalized_eff_names);
        fv_delta_depths = (uu___2110_24782.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2110_24782.synth_hook);
        try_solve_implicits_hook = (uu___2110_24782.try_solve_implicits_hook);
        splice = (uu___2110_24782.splice);
        mpreprocess = (uu___2110_24782.mpreprocess);
        postprocess = (uu___2110_24782.postprocess);
        identifier_info = (uu___2110_24782.identifier_info);
        tc_hooks = (uu___2110_24782.tc_hooks);
        dsenv = (uu___2110_24782.dsenv);
        nbe = (uu___2110_24782.nbe);
        strict_args_tab = (uu___2110_24782.strict_args_tab);
        erasable_types_tab = (uu___2110_24782.erasable_types_tab);
        enable_defer_to_tac = (uu___2110_24782.enable_defer_to_tac)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____24797 = FStar_Syntax_Free.names t in
      let uu____24800 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____24797 uu____24800
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____24821 = unbound_vars e t in
      FStar_Util.set_is_empty uu____24821
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____24829 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____24829
let (string_of_proof_ns : env -> Prims.string) =
  fun env1 ->
    let aux uu____24846 =
      match uu____24846 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24856 = FStar_Ident.text_of_path p in
             Prims.op_Hat (if b then "+" else "-") uu____24856) in
    let uu____24858 =
      let uu____24861 = FStar_List.map aux env1.proof_ns in
      FStar_All.pipe_right uu____24861 FStar_List.rev in
    FStar_All.pipe_right uu____24858 (FStar_String.concat " ")
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
        FStar_TypeChecker_Common.deferred_to_tac = uu____24901;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([], []);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____24917 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu____24917 with
                   | FStar_Pervasives_Native.Some uu____24920 -> true
                   | FStar_Pervasives_Native.None -> false)))
    | uu____24921 -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial;
        FStar_TypeChecker_Common.deferred_to_tac = uu____24927;
        FStar_TypeChecker_Common.deferred = uu____24928;
        FStar_TypeChecker_Common.univ_ineqs = uu____24929;
        FStar_TypeChecker_Common.implicits = uu____24930;_} -> true
    | uu____24939 -> false
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
          let uu___2156_24958 = g in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2156_24958.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2156_24958.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_24958.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_24958.FStar_TypeChecker_Common.implicits)
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
          let uu____24993 = FStar_Options.defensive () in
          if uu____24993
          then
            let s = FStar_Syntax_Free.names t in
            let uu____24997 =
              let uu____24998 =
                let uu____24999 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24999 in
              Prims.op_Negation uu____24998 in
            (if uu____24997
             then
               let uu____25004 =
                 let uu____25009 =
                   let uu____25010 = FStar_Syntax_Print.term_to_string t in
                   let uu____25011 =
                     let uu____25012 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____25012
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25010 uu____25011 in
                 (FStar_Errors.Warning_Defensive, uu____25009) in
               FStar_Errors.log_issue rng uu____25004
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
          let uu____25043 =
            let uu____25044 = FStar_Options.defensive () in
            Prims.op_Negation uu____25044 in
          if uu____25043
          then ()
          else
            (let uu____25046 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____25046 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____25069 =
            let uu____25070 = FStar_Options.defensive () in
            Prims.op_Negation uu____25070 in
          if uu____25069
          then ()
          else
            (let uu____25072 = bound_vars e in
             def_check_closed_in rng msg uu____25072 t)
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
          let uu___2193_25107 = g in
          let uu____25108 =
            let uu____25109 =
              let uu____25110 =
                let uu____25111 =
                  let uu____25128 =
                    let uu____25139 = FStar_Syntax_Syntax.as_arg e in
                    [uu____25139] in
                  (f, uu____25128) in
                FStar_Syntax_Syntax.Tm_app uu____25111 in
              FStar_Syntax_Syntax.mk uu____25110 f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun uu____25176 ->
                 FStar_TypeChecker_Common.NonTrivial uu____25176) uu____25109 in
          {
            FStar_TypeChecker_Common.guard_f = uu____25108;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2193_25107.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2193_25107.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2193_25107.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2193_25107.FStar_TypeChecker_Common.implicits)
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
          let uu___2200_25193 = g in
          let uu____25194 =
            let uu____25195 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____25195 in
          {
            FStar_TypeChecker_Common.guard_f = uu____25194;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2200_25193.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2200_25193.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2200_25193.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2200_25193.FStar_TypeChecker_Common.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___2205_25211 = g in
          let uu____25212 =
            let uu____25213 = map FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu____25213 in
          {
            FStar_TypeChecker_Common.guard_f = uu____25212;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2205_25211.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2205_25211.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2205_25211.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2205_25211.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2209_25215 = g in
          let uu____25216 =
            let uu____25217 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____25217 in
          {
            FStar_TypeChecker_Common.guard_f = uu____25216;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2209_25215.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2209_25215.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2209_25215.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2209_25215.FStar_TypeChecker_Common.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25223 ->
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
                       let uu____25294 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____25294
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___2232_25298 = g in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2232_25298.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2232_25298.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2232_25298.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2232_25298.FStar_TypeChecker_Common.implicits)
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
               let uu____25331 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____25331
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
            let uu___2247_25354 = g in
            let uu____25355 =
              let uu____25356 = close_forall env1 binders f in
              FStar_TypeChecker_Common.NonTrivial uu____25356 in
            {
              FStar_TypeChecker_Common.guard_f = uu____25355;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2247_25354.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2247_25354.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2247_25354.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2247_25354.FStar_TypeChecker_Common.implicits)
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
              let uu____25403 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
              match uu____25403 with
              | FStar_Pervasives_Native.Some
                  (uu____25428::(tm, uu____25430)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos in
                  (t, [], trivial_guard)
              | uu____25494 ->
                  let binders = all_binders env1 in
                  let gamma = env1.gamma in
                  let ctx_uvar =
                    let uu____25512 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25512;
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
                    (let uu____25545 =
                       debug env1 (FStar_Options.Other "ImplicitTrace") in
                     if uu____25545
                     then
                       let uu____25546 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____25546
                     else ());
                    (let g =
                       let uu___2271_25549 = trivial_guard in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2271_25549.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2271_25549.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2271_25549.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2271_25549.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____25600 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____25661 ->
                      fun b ->
                        match uu____25661 with
                        | (substs1, uvars, g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                            let uu____25703 =
                              match FStar_Pervasives_Native.snd b with
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                  t)) ->
                                  let uu____25721 =
                                    let uu____25724 =
                                      let uu____25725 =
                                        let uu____25732 =
                                          FStar_Dyn.mkdyn env1 in
                                        (uu____25732, t) in
                                      FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                        uu____25725 in
                                    FStar_Pervasives_Native.Some uu____25724 in
                                  (uu____25721, false)
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  ((FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         t)), true)
                              | uu____25742 ->
                                  (FStar_Pervasives_Native.None, false) in
                            (match uu____25703 with
                             | (ctx_uvar_meta_t, strict) ->
                                 let uu____25763 =
                                   let uu____25776 = reason b in
                                   new_implicit_var_aux uu____25776 r env1
                                     sort
                                     (if strict
                                      then FStar_Syntax_Syntax.Strict
                                      else FStar_Syntax_Syntax.Allow_untyped)
                                     ctx_uvar_meta_t in
                                 (match uu____25763 with
                                  | (t, l_ctx_uvars, g_t) ->
                                      ((let uu____25804 =
                                          FStar_All.pipe_left (debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsEqns") in
                                        if uu____25804
                                        then
                                          FStar_List.iter
                                            (fun uu____25813 ->
                                               match uu____25813 with
                                               | (ctx_uvar, uu____25819) ->
                                                   let uu____25820 =
                                                     FStar_Syntax_Print.ctx_uvar_to_string_no_reason
                                                       ctx_uvar in
                                                   FStar_Util.print1
                                                     "Layered Effect uvar : %s\n"
                                                     uu____25820) l_ctx_uvars
                                        else ());
                                       (let uu____25822 =
                                          let uu____25825 =
                                            let uu____25828 =
                                              let uu____25829 =
                                                let uu____25836 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____25836, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____25829 in
                                            [uu____25828] in
                                          FStar_List.append substs1
                                            uu____25825 in
                                        let uu____25847 = conj_guard g g_t in
                                        (uu____25822,
                                          (FStar_List.append uvars [t]),
                                          uu____25847))))))
                   (substs, [], trivial_guard)) in
            FStar_All.pipe_right uu____25600
              (fun uu____25876 ->
                 match uu____25876 with
                 | (uu____25893, uvars, g) -> (uvars, g))
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
                let uu____25933 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid in
                FStar_All.pipe_right uu____25933 FStar_Util.must in
              let uu____25950 = inst_tscheme_with post_ts [u] in
              match uu____25950 with
              | (uu____25955, post) ->
                  let uu____25957 =
                    let uu____25958 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                    [uu____25958] in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____25957 r in
            let uu____25991 =
              let uu____25992 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg in
              [uu____25992] in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____25991 r
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26027 -> ());
    push = (fun uu____26029 -> ());
    pop = (fun uu____26031 -> ());
    snapshot =
      (fun uu____26033 ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26042 -> fun uu____26043 -> ());
    encode_sig = (fun uu____26054 -> fun uu____26055 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____26061 =
             let uu____26068 = FStar_Options.peek () in (e, g, uu____26068) in
           [uu____26061]);
    solve = (fun uu____26084 -> fun uu____26085 -> fun uu____26086 -> ());
    finish = (fun uu____26092 -> ());
    refresh = (fun uu____26094 -> ())
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
        | uu____26194 -> false in
      let uu____26207 =
        FStar_Util.find_opt
          (fun uu____26239 ->
             match uu____26239 with
             | (lbname', uu____26253, uu____26254, uu____26255) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
      match uu____26207 with
      | FStar_Pervasives_Native.Some
          (uu____26266, arity, uu____26268, uu____26269) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None