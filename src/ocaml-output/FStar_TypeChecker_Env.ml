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
                  (fun uu___2_15497 ->
                     match uu___2_15497 with
                     | FStar_Syntax_Syntax.Binding_lid (l, t) ->
                         let uu____15536 = FStar_Ident.lid_equals lid l in
                         if uu____15536
                         then
                           let uu____15557 =
                             let uu____15576 =
                               let uu____15591 = inst_tscheme t in
                               FStar_Util.Inl uu____15591 in
                             let uu____15606 = FStar_Ident.range_of_lid l in
                             (uu____15576, uu____15606) in
                           FStar_Pervasives_Native.Some uu____15557
                         else FStar_Pervasives_Native.None
                     | uu____15658 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu____15453
                (fun uu____15696 ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_15706 ->
                        match uu___3_15706 with
                        | (uu____15709,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               (ses, uu____15711);
                             FStar_Syntax_Syntax.sigrng = uu____15712;
                             FStar_Syntax_Syntax.sigquals = uu____15713;
                             FStar_Syntax_Syntax.sigmeta = uu____15714;
                             FStar_Syntax_Syntax.sigattrs = uu____15715;
                             FStar_Syntax_Syntax.sigopts = uu____15716;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu____15738 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu____15738
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
                                  uu____15786 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15793 -> cache t in
                            let uu____15794 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
                            (match uu____15794 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15800 =
                                   let uu____15801 =
                                     FStar_Ident.range_of_lid l in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15801) in
                                 maybe_cache uu____15800)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15869 = find_in_sigtab env1 lid in
         match uu____15869 with
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
      let uu____15949 = lookup_qname env1 lid in
      match uu____15949 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15970, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1 ->
    fun attr ->
      let uu____16081 = FStar_Util.smap_try_find (attrtab env1) attr in
      match uu____16081 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      let add_one env2 se1 attr =
        let uu____16123 =
          let uu____16126 = lookup_attr env2 attr in se1 :: uu____16126 in
        FStar_Util.smap_add (attrtab env2) attr uu____16123 in
      FStar_List.iter
        (fun attr ->
           let uu____16136 =
             let uu____16137 = FStar_Syntax_Subst.compress attr in
             uu____16137.FStar_Syntax_Syntax.n in
           match uu____16136 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16141 =
                 let uu____16142 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_Ident.string_of_lid uu____16142 in
               add_one env1 se uu____16141
           | uu____16143 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____16165) ->
          add_sigelts env1 ses
      | uu____16174 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l ->
                let uu____16182 = FStar_Ident.string_of_lid l in
                FStar_Util.smap_add (sigtab env1) uu____16182 se) lids;
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
        (fun uu___4_16214 ->
           match uu___4_16214 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____16224 =
                 let uu____16231 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname in
                 ((id.FStar_Syntax_Syntax.sort), uu____16231) in
               FStar_Pervasives_Native.Some uu____16224
           | uu____16240 -> FStar_Pervasives_Native.None)
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16301, lb::[]), uu____16303) ->
            let uu____16310 =
              let uu____16319 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____16328 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____16319, uu____16328) in
            FStar_Pervasives_Native.Some uu____16310
        | FStar_Syntax_Syntax.Sig_let ((uu____16341, lbs), uu____16343) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16373 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16385 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____16385
                     then
                       let uu____16396 =
                         let uu____16405 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____16414 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____16405, uu____16414) in
                       FStar_Pervasives_Native.Some uu____16396
                     else FStar_Pervasives_Native.None)
        | uu____16436 -> FStar_Pervasives_Native.None
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
                    let uu____16526 =
                      let uu____16527 =
                        let uu____16528 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname in
                        let uu____16529 =
                          let uu____16530 =
                            let uu____16531 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature)) in
                            let uu____16536 =
                              let uu____16537 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us) in
                              Prims.op_Hat ", got " uu____16537 in
                            Prims.op_Hat uu____16531 uu____16536 in
                          Prims.op_Hat ", expected " uu____16530 in
                        Prims.op_Hat uu____16528 uu____16529 in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16527 in
                    failwith uu____16526
                  else ());
             (let uu____16539 =
                let uu____16548 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature in
                (uu____16548, (se.FStar_Syntax_Syntax.sigrng)) in
              FStar_Pervasives_Native.Some uu____16539))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid, us, binders, uu____16568, uu____16569) ->
            let uu____16574 =
              let uu____16583 =
                let uu____16588 =
                  let uu____16589 =
                    let uu____16592 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                    FStar_Syntax_Util.arrow binders uu____16592 in
                  (us, uu____16589) in
                inst_ts us_opt uu____16588 in
              (uu____16583, (se.FStar_Syntax_Syntax.sigrng)) in
            FStar_Pervasives_Native.Some uu____16574
        | uu____16611 -> FStar_Pervasives_Native.None
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
        let mapper uu____16699 =
          match uu____16699 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16795, uvs, t, uu____16798, uu____16799,
                         uu____16800);
                      FStar_Syntax_Syntax.sigrng = uu____16801;
                      FStar_Syntax_Syntax.sigquals = uu____16802;
                      FStar_Syntax_Syntax.sigmeta = uu____16803;
                      FStar_Syntax_Syntax.sigattrs = uu____16804;
                      FStar_Syntax_Syntax.sigopts = uu____16805;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____16828 =
                     let uu____16837 = inst_tscheme1 (uvs, t) in
                     (uu____16837, rng) in
                   FStar_Pervasives_Native.Some uu____16828
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____16861;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16863;
                      FStar_Syntax_Syntax.sigattrs = uu____16864;
                      FStar_Syntax_Syntax.sigopts = uu____16865;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____16884 =
                     let uu____16885 = in_cur_mod env1 l in uu____16885 = Yes in
                   if uu____16884
                   then
                     let uu____16896 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface in
                     (if uu____16896
                      then
                        let uu____16909 =
                          let uu____16918 = inst_tscheme1 (uvs, t) in
                          (uu____16918, rng) in
                        FStar_Pervasives_Native.Some uu____16909
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16949 =
                        let uu____16958 = inst_tscheme1 (uvs, t) in
                        (uu____16958, rng) in
                      FStar_Pervasives_Native.Some uu____16949)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____16983, uu____16984);
                      FStar_Syntax_Syntax.sigrng = uu____16985;
                      FStar_Syntax_Syntax.sigquals = uu____16986;
                      FStar_Syntax_Syntax.sigmeta = uu____16987;
                      FStar_Syntax_Syntax.sigattrs = uu____16988;
                      FStar_Syntax_Syntax.sigopts = uu____16989;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17032 =
                          let uu____17041 = inst_tscheme1 (uvs, k) in
                          (uu____17041, rng) in
                        FStar_Pervasives_Native.Some uu____17032
                    | uu____17062 ->
                        let uu____17063 =
                          let uu____17072 =
                            let uu____17077 =
                              let uu____17078 =
                                let uu____17081 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____17081 in
                              (uvs, uu____17078) in
                            inst_tscheme1 uu____17077 in
                          (uu____17072, rng) in
                        FStar_Pervasives_Native.Some uu____17063)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____17104, uu____17105);
                      FStar_Syntax_Syntax.sigrng = uu____17106;
                      FStar_Syntax_Syntax.sigquals = uu____17107;
                      FStar_Syntax_Syntax.sigmeta = uu____17108;
                      FStar_Syntax_Syntax.sigattrs = uu____17109;
                      FStar_Syntax_Syntax.sigopts = uu____17110;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17154 =
                          let uu____17163 = inst_tscheme_with (uvs, k) us in
                          (uu____17163, rng) in
                        FStar_Pervasives_Native.Some uu____17154
                    | uu____17184 ->
                        let uu____17185 =
                          let uu____17194 =
                            let uu____17199 =
                              let uu____17200 =
                                let uu____17203 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____17203 in
                              (uvs, uu____17200) in
                            inst_tscheme_with uu____17199 us in
                          (uu____17194, rng) in
                        FStar_Pervasives_Native.Some uu____17185)
               | FStar_Util.Inr se ->
                   let uu____17239 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17260;
                          FStar_Syntax_Syntax.sigrng = uu____17261;
                          FStar_Syntax_Syntax.sigquals = uu____17262;
                          FStar_Syntax_Syntax.sigmeta = uu____17263;
                          FStar_Syntax_Syntax.sigattrs = uu____17264;
                          FStar_Syntax_Syntax.sigopts = uu____17265;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17282 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range in
                   FStar_All.pipe_right uu____17239
                     (FStar_Util.map_option
                        (fun uu____17330 ->
                           match uu____17330 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____17361 =
          let uu____17372 = lookup_qname env1 lid in
          FStar_Util.bind_opt uu____17372 mapper in
        match uu____17361 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____17446 =
              let uu____17457 =
                let uu____17464 =
                  let uu___861_17467 = t in
                  let uu____17468 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___861_17467.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17468;
                    FStar_Syntax_Syntax.vars =
                      (uu___861_17467.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____17464) in
              (uu____17457, r) in
            FStar_Pervasives_Native.Some uu____17446
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____17515 = lookup_qname env1 l in
      match uu____17515 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____17534 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1 ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____17586 = try_lookup_bv env1 bv in
      match uu____17586 with
      | FStar_Pervasives_Native.None ->
          let uu____17601 = variable_not_found bv in
          FStar_Errors.raise_error uu____17601 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____17616 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____17617 =
            let uu____17618 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____17618 in
          (uu____17616, uu____17617)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____17639 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
      match uu____17639 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____17705 = FStar_Range.use_range use_range in
            FStar_Range.set_use_range r uu____17705 in
          let uu____17706 =
            let uu____17715 =
              let uu____17720 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____17720) in
            (uu____17715, r1) in
          FStar_Pervasives_Native.Some uu____17706
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
        let uu____17754 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l in
        match uu____17754 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17787, t), r) ->
            let use_range = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____17812 = FStar_Range.use_range use_range in
              FStar_Range.set_use_range r uu____17812 in
            let uu____17813 =
              let uu____17818 = FStar_Syntax_Subst.set_use_range use_range t in
              (uu____17818, r1) in
            FStar_Pervasives_Native.Some uu____17813
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1 ->
    fun l ->
      let uu____17841 = try_lookup_lid env1 l in
      match uu____17841 with
      | FStar_Pervasives_Native.None ->
          let uu____17868 = name_not_found l in
          let uu____17873 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____17868 uu____17873
      | FStar_Pervasives_Native.Some v -> v
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1 ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17915 ->
              match uu___5_17915 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____17917 = FStar_Ident.string_of_id x in
                  let uu____17918 = FStar_Ident.string_of_id y in
                  uu____17917 = uu____17918
              | uu____17919 -> false) env1.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____17938 = lookup_qname env1 lid in
      match uu____17938 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17947, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____17950;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17952;
              FStar_Syntax_Syntax.sigattrs = uu____17953;
              FStar_Syntax_Syntax.sigopts = uu____17954;_},
            FStar_Pervasives_Native.None),
           uu____17955)
          ->
          let uu____18006 =
            let uu____18013 =
              let uu____18014 =
                let uu____18017 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____18017 t in
              (uvs, uu____18014) in
            (uu____18013, q) in
          FStar_Pervasives_Native.Some uu____18006
      | uu____18030 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____18051 = lookup_qname env1 lid in
      match uu____18051 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18056, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____18059;
              FStar_Syntax_Syntax.sigquals = uu____18060;
              FStar_Syntax_Syntax.sigmeta = uu____18061;
              FStar_Syntax_Syntax.sigattrs = uu____18062;
              FStar_Syntax_Syntax.sigopts = uu____18063;_},
            FStar_Pervasives_Native.None),
           uu____18064)
          ->
          let uu____18115 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____18115 (uvs, t)
      | uu____18120 ->
          let uu____18121 = name_not_found lid in
          let uu____18126 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____18121 uu____18126
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____18145 = lookup_qname env1 lid in
      match uu____18145 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18150, uvs, t, uu____18153, uu____18154, uu____18155);
              FStar_Syntax_Syntax.sigrng = uu____18156;
              FStar_Syntax_Syntax.sigquals = uu____18157;
              FStar_Syntax_Syntax.sigmeta = uu____18158;
              FStar_Syntax_Syntax.sigattrs = uu____18159;
              FStar_Syntax_Syntax.sigopts = uu____18160;_},
            FStar_Pervasives_Native.None),
           uu____18161)
          ->
          let uu____18216 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____18216 (uvs, t)
      | uu____18221 ->
          let uu____18222 = name_not_found lid in
          let uu____18227 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____18222 uu____18227
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1 ->
    fun lid ->
      let uu____18248 = lookup_qname env1 lid in
      match uu____18248 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18255, uu____18256, uu____18257, uu____18258,
                 uu____18259, dcs);
              FStar_Syntax_Syntax.sigrng = uu____18261;
              FStar_Syntax_Syntax.sigquals = uu____18262;
              FStar_Syntax_Syntax.sigmeta = uu____18263;
              FStar_Syntax_Syntax.sigattrs = uu____18264;
              FStar_Syntax_Syntax.sigopts = uu____18265;_},
            uu____18266),
           uu____18267)
          -> (true, dcs)
      | uu____18330 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu____18343 = lookup_qname env1 lid in
      match uu____18343 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18344, uu____18345, uu____18346, l, uu____18348,
                 uu____18349);
              FStar_Syntax_Syntax.sigrng = uu____18350;
              FStar_Syntax_Syntax.sigquals = uu____18351;
              FStar_Syntax_Syntax.sigmeta = uu____18352;
              FStar_Syntax_Syntax.sigattrs = uu____18353;
              FStar_Syntax_Syntax.sigopts = uu____18354;_},
            uu____18355),
           uu____18356)
          -> l
      | uu____18413 ->
          let uu____18414 =
            let uu____18415 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____18415 in
          failwith uu____18414
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
               uu____18477)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu____18534)
                   when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        let uu____18556 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid in
                        if uu____18556
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18588 -> FStar_Pervasives_Native.None)
          | uu____18597 -> FStar_Pervasives_Native.None
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
        let uu____18656 = lookup_qname env1 lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18656
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
        let uu____18688 = lookup_qname env1 lid in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18688
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv ->
    fun qn ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____18710 =
        let uu____18711 = FStar_Ident.nsstr lid in uu____18711 = "Prims" in
      if uu____18710
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____18735, uu____18736) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se, uu____18784), uu____18785) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18834 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18851 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18860 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18875 ->
                  let uu____18882 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals in
                  FStar_Pervasives_Native.Some uu____18882
              | FStar_Syntax_Syntax.Sig_let ((uu____18883, lbs), uu____18885)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       let uu____18899 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid in
                       if uu____18899
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____18903 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____18916 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____18925 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18932 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18933 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18934 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18947 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____18948 ->
                  FStar_Pervasives_Native.None))
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____18970 =
        let uu____18971 = FStar_Ident.nsstr lid in uu____18971 = "Prims" in
      if uu____18970
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18973 =
           let uu____18976 = FStar_Ident.string_of_lid lid in
           FStar_All.pipe_right uu____18976
             (FStar_Util.smap_try_find env1.fv_delta_depths) in
         FStar_All.pipe_right uu____18973
           (fun d_opt ->
              let uu____18986 = FStar_All.pipe_right d_opt FStar_Util.is_some in
              if uu____18986
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18992 =
                   let uu____18995 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   delta_depth_of_qninfo fv uu____18995 in
                 match uu____18992 with
                 | FStar_Pervasives_Native.None ->
                     let uu____18996 =
                       let uu____18997 = FStar_Syntax_Print.fv_to_string fv in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18997 in
                     failwith uu____18996
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19000 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ()) in
                       if uu____19000
                       then
                         let uu____19001 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____19002 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta in
                         let uu____19003 =
                           FStar_Syntax_Print.delta_depth_to_string d in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19001 uu____19002 uu____19003
                       else ());
                      (let uu____19006 = FStar_Ident.string_of_lid lid in
                       FStar_Util.smap_add env1.fv_delta_depths uu____19006 d);
                      d))))
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____19025), uu____19026) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19075 -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____19096), uu____19097) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19146 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____19167 = lookup_qname env1 lid in
      FStar_All.pipe_left attrs_of_qninfo uu____19167
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____19195 = lookup_attrs_of_lid env1 fv_lid in
        match uu____19195 with
        | FStar_Pervasives_Native.None -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19211 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm ->
                      let uu____19218 =
                        let uu____19219 = FStar_Syntax_Util.un_uinst tm in
                        uu____19219.FStar_Syntax_Syntax.n in
                      match uu____19218 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19223 -> false)) in
            (true, uu____19211)
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____19239 = fv_exists_and_has_attr env1 fv_lid attr_lid in
        FStar_Pervasives_Native.snd uu____19239
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
          let uu____19301 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____19301 in
        let uu____19302 = FStar_Util.smap_try_find tab s in
        match uu____19302 with
        | FStar_Pervasives_Native.None ->
            let uu____19305 = f () in
            (match uu____19305 with
             | (should_cache, res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1 ->
    fun fv ->
      let f uu____19334 =
        let uu____19335 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr in
        match uu____19335 with | (ex, erasable) -> (ex, erasable) in
      cache_in_fv_tab env1.erasable_types_tab fv f
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____19356 =
        let uu____19357 = FStar_Syntax_Util.unrefine t in
        uu____19357.FStar_Syntax_Syntax.n in
      match uu____19356 with
      | FStar_Syntax_Syntax.Tm_type uu____19360 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head, uu____19363) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu____19389) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____19394, c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____19416 -> false
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fv ->
      let f uu____19444 =
        let attrs =
          let uu____19450 = FStar_Syntax_Syntax.lid_of_fv fv in
          lookup_attrs_of_lid env1 uu____19450 in
        match attrs with
        | FStar_Pervasives_Native.None ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x ->
                   let uu____19482 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr in
                   FStar_Pervasives_Native.fst uu____19482) in
            (true, res) in
      cache_in_fv_tab env1.strict_args_tab fv f
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ftv ->
      let uu____19517 = lookup_qname env1 ftv in
      match uu____19517 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____19521) ->
          let uu____19566 =
            effect_signature FStar_Pervasives_Native.None se env1.range in
          (match uu____19566 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19587, t), r) ->
               let uu____19602 =
                 let uu____19603 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____19603 t in
               FStar_Pervasives_Native.Some uu____19602)
      | uu____19604 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun ftv ->
      let uu____19615 = try_lookup_effect_lid env1 ftv in
      match uu____19615 with
      | FStar_Pervasives_Native.None ->
          let uu____19618 = name_not_found ftv in
          let uu____19623 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____19618 uu____19623
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
        let uu____19646 = lookup_qname env1 lid0 in
        match uu____19646 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs, binders, c, uu____19657);
                FStar_Syntax_Syntax.sigrng = uu____19658;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19660;
                FStar_Syntax_Syntax.sigattrs = uu____19661;
                FStar_Syntax_Syntax.sigopts = uu____19662;_},
              FStar_Pervasives_Native.None),
             uu____19663)
            ->
            let lid1 =
              let uu____19719 =
                let uu____19720 = FStar_Ident.range_of_lid lid in
                let uu____19721 =
                  let uu____19722 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____19722 in
                FStar_Range.set_use_range uu____19720 uu____19721 in
              FStar_Ident.set_lid_range lid uu____19719 in
            let uu____19723 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19727 ->
                      match uu___6_19727 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____19728 -> false)) in
            if uu____19723
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____19742 =
                      let uu____19743 =
                        let uu____19744 = get_range env1 in
                        FStar_Range.string_of_range uu____19744 in
                      let uu____19745 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____19746 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19743 uu____19745 uu____19746 in
                    failwith uu____19742) in
               match (binders, univs) with
               | ([], uu____19763) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19788, uu____19789::uu____19790::uu____19791) ->
                   let uu____19812 =
                     let uu____19813 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____19814 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19813 uu____19814 in
                   failwith uu____19812
               | uu____19821 ->
                   let uu____19836 =
                     let uu____19841 =
                       let uu____19842 = FStar_Syntax_Util.arrow binders c in
                       (univs, uu____19842) in
                     inst_tscheme_with uu____19841 insts in
                   (match uu____19836 with
                    | (uu____19855, t) ->
                        let t1 =
                          let uu____19858 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____19858 t in
                        let uu____19859 =
                          let uu____19860 = FStar_Syntax_Subst.compress t1 in
                          uu____19860.FStar_Syntax_Syntax.n in
                        (match uu____19859 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19895 -> failwith "Impossible")))
        | uu____19902 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun l ->
      let rec find l1 =
        let uu____19925 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____19925 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19938, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____19945 = find l2 in
            (match uu____19945 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____19952 =
          let uu____19955 = FStar_Ident.string_of_lid l in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____19955 in
        match uu____19952 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____19957 = find l in
            (match uu____19957 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____19962 = FStar_Ident.string_of_lid l in
                   FStar_Util.smap_add env1.normalized_eff_names uu____19962
                     m);
                  m)) in
      let uu____19963 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____19963
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1 ->
    fun name ->
      fun r ->
        let sig_t =
          let uu____19982 =
            FStar_All.pipe_right name (lookup_effect_lid env1) in
          FStar_All.pipe_right uu____19982 FStar_Syntax_Subst.compress in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs, uu____19987) ->
            FStar_List.length bs
        | uu____20026 ->
            let uu____20027 =
              let uu____20032 =
                let uu____20033 = FStar_Ident.string_of_lid name in
                let uu____20034 = FStar_Syntax_Print.term_to_string sig_t in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20033 uu____20034 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20032) in
            FStar_Errors.raise_error uu____20027 r
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1 ->
    fun l ->
      let l1 = norm_eff_name env1 l in
      let uu____20048 = lookup_qname env1 l1 in
      match uu____20048 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20051;
              FStar_Syntax_Syntax.sigrng = uu____20052;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20054;
              FStar_Syntax_Syntax.sigattrs = uu____20055;
              FStar_Syntax_Syntax.sigopts = uu____20056;_},
            uu____20057),
           uu____20058)
          -> q
      | uu____20111 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      fun i ->
        let fail uu____20132 =
          let uu____20133 =
            let uu____20134 = FStar_Util.string_of_int i in
            let uu____20135 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20134 uu____20135 in
          failwith uu____20133 in
        let uu____20136 = lookup_datacon env1 lid in
        match uu____20136 with
        | (uu____20141, t) ->
            let uu____20143 =
              let uu____20144 = FStar_Syntax_Subst.compress t in
              uu____20144.FStar_Syntax_Syntax.n in
            (match uu____20143 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____20148) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____20191 -> fail ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____20202 = lookup_qname env1 l in
      match uu____20202 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20203, uu____20204, uu____20205);
              FStar_Syntax_Syntax.sigrng = uu____20206;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20208;
              FStar_Syntax_Syntax.sigattrs = uu____20209;
              FStar_Syntax_Syntax.sigopts = uu____20210;_},
            uu____20211),
           uu____20212)
          ->
          FStar_Util.for_some
            (fun uu___7_20267 ->
               match uu___7_20267 with
               | FStar_Syntax_Syntax.Projector uu____20268 -> true
               | uu____20273 -> false) quals
      | uu____20274 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____20285 = lookup_qname env1 lid in
      match uu____20285 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20286, uu____20287, uu____20288, uu____20289,
                 uu____20290, uu____20291);
              FStar_Syntax_Syntax.sigrng = uu____20292;
              FStar_Syntax_Syntax.sigquals = uu____20293;
              FStar_Syntax_Syntax.sigmeta = uu____20294;
              FStar_Syntax_Syntax.sigattrs = uu____20295;
              FStar_Syntax_Syntax.sigopts = uu____20296;_},
            uu____20297),
           uu____20298)
          -> true
      | uu____20355 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____20366 = lookup_qname env1 lid in
      match uu____20366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20367, uu____20368, uu____20369, uu____20370,
                 uu____20371, uu____20372);
              FStar_Syntax_Syntax.sigrng = uu____20373;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20375;
              FStar_Syntax_Syntax.sigattrs = uu____20376;
              FStar_Syntax_Syntax.sigopts = uu____20377;_},
            uu____20378),
           uu____20379)
          ->
          FStar_Util.for_some
            (fun uu___8_20442 ->
               match uu___8_20442 with
               | FStar_Syntax_Syntax.RecordType uu____20443 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20452 -> true
               | uu____20461 -> false) quals
      | uu____20462 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20468, uu____20469);
            FStar_Syntax_Syntax.sigrng = uu____20470;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20472;
            FStar_Syntax_Syntax.sigattrs = uu____20473;
            FStar_Syntax_Syntax.sigopts = uu____20474;_},
          uu____20475),
         uu____20476)
        ->
        FStar_Util.for_some
          (fun uu___9_20535 ->
             match uu___9_20535 with
             | FStar_Syntax_Syntax.Action uu____20536 -> true
             | uu____20537 -> false) quals
    | uu____20538 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____20549 = lookup_qname env1 lid in
      FStar_All.pipe_left qninfo_is_action uu____20549
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
      let uu____20563 =
        let uu____20564 = FStar_Syntax_Util.un_uinst head in
        uu____20564.FStar_Syntax_Syntax.n in
      match uu____20563 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20568 ->
               true
           | uu____20569 -> false)
      | uu____20570 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____20581 = lookup_qname env1 l in
      match uu____20581 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____20583), uu____20584) ->
          FStar_Util.for_some
            (fun uu___10_20632 ->
               match uu___10_20632 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____20633 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20634 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20705 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____20721) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20738 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20745 ->
                 FStar_Pervasives_Native.Some true
             | uu____20762 -> FStar_Pervasives_Native.Some false) in
      let uu____20763 =
        let uu____20766 = lookup_qname env1 lid in
        FStar_Util.bind_opt uu____20766 mapper in
      match uu____20763 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu____20818 = lookup_qname env1 lid in
      match uu____20818 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20821, uu____20822, tps, uu____20824, uu____20825,
                 uu____20826);
              FStar_Syntax_Syntax.sigrng = uu____20827;
              FStar_Syntax_Syntax.sigquals = uu____20828;
              FStar_Syntax_Syntax.sigmeta = uu____20829;
              FStar_Syntax_Syntax.sigattrs = uu____20830;
              FStar_Syntax_Syntax.sigopts = uu____20831;_},
            uu____20832),
           uu____20833)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20900 -> FStar_Pervasives_Native.None
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
           (fun uu____20944 ->
              match uu____20944 with
              | (d, uu____20952) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1 ->
    fun l ->
      let uu____20967 = effect_decl_opt env1 l in
      match uu____20967 with
      | FStar_Pervasives_Native.None ->
          let uu____20982 = name_not_found l in
          let uu____20987 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____20982 uu____20987
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____21013 = FStar_All.pipe_right l (get_effect_decl env1) in
      FStar_All.pipe_right uu____21013 FStar_Syntax_Util.is_layered
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____21018 ->
         fun c -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21032 ->
            fun uu____21033 -> fun e -> FStar_Util.return_all e))
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
        let uu____21066 = FStar_Ident.lid_equals l1 l2 in
        if uu____21066
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____21082 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____21082
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____21098 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21151 ->
                        match uu____21151 with
                        | (m1, m2, uu____21164, uu____21165, uu____21166) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____21098 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____21191, uu____21192, m3, j1, j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____21239 = join_opt env1 l1 l2 in
        match uu____21239 with
        | FStar_Pervasives_Native.None ->
            let uu____21260 =
              let uu____21265 =
                let uu____21266 = FStar_Syntax_Print.lid_to_string l1 in
                let uu____21267 = FStar_Syntax_Print.lid_to_string l2 in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____21266 uu____21267 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21265) in
            FStar_Errors.raise_error uu____21260 env1.range
        | FStar_Pervasives_Native.Some t -> t
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____21306 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____21306
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
  'uuuuuu21322 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu21322) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls ->
    fun m ->
      let uu____21351 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21377 ->
                match uu____21377 with
                | (d, uu____21383) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____21351 with
      | FStar_Pervasives_Native.None ->
          let uu____21394 =
            let uu____21395 = FStar_Ident.string_of_lid m in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____21395 in
          failwith uu____21394
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____21408 = inst_tscheme md.FStar_Syntax_Syntax.signature in
          (match uu____21408 with
           | (uu____21419, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____21437)::(wp, uu____21439)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21495 -> failwith "Impossible"))
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
        | uu____21557 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun comp ->
      let c = comp_to_comp_typ env1 comp in
      let uu____21569 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____21569 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____21586 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____21586 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21608 =
                     let uu____21613 =
                       let uu____21614 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____21621 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one) in
                       let uu____21630 =
                         let uu____21631 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____21631 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21614 uu____21621 uu____21630 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21613) in
                   FStar_Errors.raise_error uu____21608
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____21636 =
                     let uu____21647 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____21647 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____21684 ->
                        fun uu____21685 ->
                          match (uu____21684, uu____21685) with
                          | ((x, uu____21715), (t, uu____21717)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21636 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1 in
                 let c2 =
                   let uu____21748 =
                     let uu___1615_21749 = comp_to_comp_typ env1 c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1615_21749.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1615_21749.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1615_21749.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1615_21749.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____21748
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env1 c2)))
let effect_repr_aux :
  'uuuuuu21760 .
    'uuuuuu21760 ->
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
            let uu____21801 =
              let uu____21806 = num_effect_indices env1 eff_name r in
              ((FStar_List.length args), uu____21806) in
            match uu____21801 with
            | (given, expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____21819 = FStar_Ident.string_of_lid eff_name in
                     let uu____21820 = FStar_Util.string_of_int given in
                     let uu____21821 = FStar_Util.string_of_int expected in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____21819 uu____21820 uu____21821 in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r) in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c) in
          let uu____21823 = effect_decl_opt env1 effect_name in
          match uu____21823 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, uu____21845) ->
              let uu____21856 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              (match uu____21856 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____21874 =
                       let uu____21877 =
                         let uu____21878 =
                           let uu____21895 =
                             let uu____21906 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg in
                             uu____21906 ::
                               (c1.FStar_Syntax_Syntax.effect_args) in
                           (repr, uu____21895) in
                         FStar_Syntax_Syntax.Tm_app uu____21878 in
                       let uu____21943 = get_range env1 in
                       FStar_Syntax_Syntax.mk uu____21877 uu____21943 in
                     FStar_Pervasives_Native.Some uu____21874)))
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
           (fun uu___11_21997 ->
              match uu___11_21997 with
              | FStar_Syntax_Syntax.Reflectable uu____21998 -> true
              | uu____21999 -> false))
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
      | uu____22046 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____22057 =
        let uu____22058 = FStar_Syntax_Subst.compress t in
        uu____22058.FStar_Syntax_Syntax.n in
      match uu____22057 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22061, c) ->
          is_reifiable_comp env1 c
      | uu____22083 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu____22101 =
           let uu____22102 = is_reifiable_effect env1 l in
           Prims.op_Negation uu____22102 in
         if uu____22101
         then
           let uu____22103 =
             let uu____22108 =
               let uu____22109 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22109 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22108) in
           let uu____22110 = get_range env1 in
           FStar_Errors.raise_error uu____22103 uu____22110
         else ());
        (let uu____22112 = effect_repr_aux true env1 c u_c in
         match uu____22112 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env2 =
        let uu___1692_22144 = env1 in
        {
          solver = (uu___1692_22144.solver);
          range = (uu___1692_22144.range);
          curmodule = (uu___1692_22144.curmodule);
          gamma = (uu___1692_22144.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1692_22144.gamma_cache);
          modules = (uu___1692_22144.modules);
          expected_typ = (uu___1692_22144.expected_typ);
          sigtab = (uu___1692_22144.sigtab);
          attrtab = (uu___1692_22144.attrtab);
          instantiate_imp = (uu___1692_22144.instantiate_imp);
          effects = (uu___1692_22144.effects);
          generalize = (uu___1692_22144.generalize);
          letrecs = (uu___1692_22144.letrecs);
          top_level = (uu___1692_22144.top_level);
          check_uvars = (uu___1692_22144.check_uvars);
          use_eq = (uu___1692_22144.use_eq);
          use_eq_strict = (uu___1692_22144.use_eq_strict);
          is_iface = (uu___1692_22144.is_iface);
          admit = (uu___1692_22144.admit);
          lax = (uu___1692_22144.lax);
          lax_universes = (uu___1692_22144.lax_universes);
          phase1 = (uu___1692_22144.phase1);
          failhard = (uu___1692_22144.failhard);
          nosynth = (uu___1692_22144.nosynth);
          uvar_subtyping = (uu___1692_22144.uvar_subtyping);
          tc_term = (uu___1692_22144.tc_term);
          type_of = (uu___1692_22144.type_of);
          universe_of = (uu___1692_22144.universe_of);
          check_type_of = (uu___1692_22144.check_type_of);
          use_bv_sorts = (uu___1692_22144.use_bv_sorts);
          qtbl_name_and_index = (uu___1692_22144.qtbl_name_and_index);
          normalized_eff_names = (uu___1692_22144.normalized_eff_names);
          fv_delta_depths = (uu___1692_22144.fv_delta_depths);
          proof_ns = (uu___1692_22144.proof_ns);
          synth_hook = (uu___1692_22144.synth_hook);
          try_solve_implicits_hook =
            (uu___1692_22144.try_solve_implicits_hook);
          splice = (uu___1692_22144.splice);
          mpreprocess = (uu___1692_22144.mpreprocess);
          postprocess = (uu___1692_22144.postprocess);
          identifier_info = (uu___1692_22144.identifier_info);
          tc_hooks = (uu___1692_22144.tc_hooks);
          dsenv = (uu___1692_22144.dsenv);
          nbe = (uu___1692_22144.nbe);
          strict_args_tab = (uu___1692_22144.strict_args_tab);
          erasable_types_tab = (uu___1692_22144.erasable_types_tab);
          enable_defer_to_tac = (uu___1692_22144.enable_defer_to_tac)
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
    fun uu____22162 ->
      match uu____22162 with
      | (ed, quals) ->
          let effects1 =
            let uu___1701_22176 = env1.effects in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1701_22176.order);
              joins = (uu___1701_22176.joins);
              polymonadic_binds = (uu___1701_22176.polymonadic_binds);
              polymonadic_subcomps = (uu___1701_22176.polymonadic_subcomps)
            } in
          let uu___1704_22185 = env1 in
          {
            solver = (uu___1704_22185.solver);
            range = (uu___1704_22185.range);
            curmodule = (uu___1704_22185.curmodule);
            gamma = (uu___1704_22185.gamma);
            gamma_sig = (uu___1704_22185.gamma_sig);
            gamma_cache = (uu___1704_22185.gamma_cache);
            modules = (uu___1704_22185.modules);
            expected_typ = (uu___1704_22185.expected_typ);
            sigtab = (uu___1704_22185.sigtab);
            attrtab = (uu___1704_22185.attrtab);
            instantiate_imp = (uu___1704_22185.instantiate_imp);
            effects = effects1;
            generalize = (uu___1704_22185.generalize);
            letrecs = (uu___1704_22185.letrecs);
            top_level = (uu___1704_22185.top_level);
            check_uvars = (uu___1704_22185.check_uvars);
            use_eq = (uu___1704_22185.use_eq);
            use_eq_strict = (uu___1704_22185.use_eq_strict);
            is_iface = (uu___1704_22185.is_iface);
            admit = (uu___1704_22185.admit);
            lax = (uu___1704_22185.lax);
            lax_universes = (uu___1704_22185.lax_universes);
            phase1 = (uu___1704_22185.phase1);
            failhard = (uu___1704_22185.failhard);
            nosynth = (uu___1704_22185.nosynth);
            uvar_subtyping = (uu___1704_22185.uvar_subtyping);
            tc_term = (uu___1704_22185.tc_term);
            type_of = (uu___1704_22185.type_of);
            universe_of = (uu___1704_22185.universe_of);
            check_type_of = (uu___1704_22185.check_type_of);
            use_bv_sorts = (uu___1704_22185.use_bv_sorts);
            qtbl_name_and_index = (uu___1704_22185.qtbl_name_and_index);
            normalized_eff_names = (uu___1704_22185.normalized_eff_names);
            fv_delta_depths = (uu___1704_22185.fv_delta_depths);
            proof_ns = (uu___1704_22185.proof_ns);
            synth_hook = (uu___1704_22185.synth_hook);
            try_solve_implicits_hook =
              (uu___1704_22185.try_solve_implicits_hook);
            splice = (uu___1704_22185.splice);
            mpreprocess = (uu___1704_22185.mpreprocess);
            postprocess = (uu___1704_22185.postprocess);
            identifier_info = (uu___1704_22185.identifier_info);
            tc_hooks = (uu___1704_22185.tc_hooks);
            dsenv = (uu___1704_22185.dsenv);
            nbe = (uu___1704_22185.nbe);
            strict_args_tab = (uu___1704_22185.strict_args_tab);
            erasable_types_tab = (uu___1704_22185.erasable_types_tab);
            enable_defer_to_tac = (uu___1704_22185.enable_defer_to_tac)
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
        let uu____22213 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____22281 ->
                  match uu____22281 with
                  | (m1, n1, uu____22298, uu____22299) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____22213 with
        | FStar_Pervasives_Native.Some (uu____22324, uu____22325, p, t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____22370 -> FStar_Pervasives_Native.None
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun m ->
      fun n ->
        let uu____22414 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____22449 ->
                  match uu____22449 with
                  | (m1, n1, uu____22458) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____22414 with
        | FStar_Pervasives_Native.Some (uu____22461, uu____22462, ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____22470 -> FStar_Pervasives_Native.None
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1 ->
    fun src ->
      fun tgt ->
        fun st_mlift ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____22526 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2) in
                FStar_All.pipe_right uu____22526
                  (fun uu____22547 ->
                     match uu____22547 with
                     | (c1, g1) ->
                         let uu____22558 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2) in
                         FStar_All.pipe_right uu____22558
                           (fun uu____22579 ->
                              match uu____22579 with
                              | (c2, g2) ->
                                  let uu____22590 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2 in
                                  (c2, uu____22590))) in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun e ->
                              let uu____22712 = l1 u t e in
                              l2 u t uu____22712))
                | uu____22713 -> FStar_Pervasives_Native.None in
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
                 (fun uu____22781 ->
                    match uu____22781 with
                    | (e, uu____22789) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____22812 =
            match uu____22812 with
            | (i, j) ->
                let uu____22823 = FStar_Ident.lid_equals i j in
                if uu____22823
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____22828 ->
                       FStar_Pervasives_Native.Some uu____22828)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____22856 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i ->
                        let uu____22866 = FStar_Ident.lid_equals i k in
                        if uu____22866
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j ->
                                  let uu____22877 =
                                    FStar_Ident.lid_equals j k in
                                  if uu____22877
                                  then []
                                  else
                                    (let uu____22881 =
                                       let uu____22890 =
                                         find_edge order1 (i, k) in
                                       let uu____22893 =
                                         find_edge order1 (k, j) in
                                       (uu____22890, uu____22893) in
                                     match uu____22881 with
                                     | (FStar_Pervasives_Native.Some e1,
                                        FStar_Pervasives_Native.Some e2) ->
                                         let uu____22908 =
                                           compose_edges e1 e2 in
                                         [uu____22908]
                                     | uu____22909 -> []))))) in
              FStar_List.append order1 uu____22856 in
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
                  let uu____22939 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____22941 =
                         lookup_effect_quals env1 edge2.mtarget in
                       FStar_All.pipe_right uu____22941
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)) in
                  if uu____22939
                  then
                    let uu____22946 =
                      let uu____22951 =
                        let uu____22952 =
                          FStar_Ident.string_of_lid edge2.mtarget in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____22952 in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____22951) in
                    let uu____22953 = get_range env1 in
                    FStar_Errors.raise_error uu____22946 uu____22953
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j ->
                             let join_opt1 =
                               let uu____23030 = FStar_Ident.lid_equals i j in
                               if uu____23030
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt ->
                                         fun k ->
                                           let uu____23079 =
                                             let uu____23088 =
                                               find_edge order2 (i, k) in
                                             let uu____23091 =
                                               find_edge order2 (j, k) in
                                             (uu____23088, uu____23091) in
                                           match uu____23079 with
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
                                                    (ub, uu____23133,
                                                     uu____23134)
                                                    ->
                                                    let uu____23141 =
                                                      let uu____23146 =
                                                        let uu____23147 =
                                                          find_edge order2
                                                            (k, ub) in
                                                        FStar_Util.is_some
                                                          uu____23147 in
                                                      let uu____23150 =
                                                        let uu____23151 =
                                                          find_edge order2
                                                            (ub, k) in
                                                        FStar_Util.is_some
                                                          uu____23151 in
                                                      (uu____23146,
                                                        uu____23150) in
                                                    (match uu____23141 with
                                                     | (true, true) ->
                                                         let uu____23162 =
                                                           FStar_Ident.lid_equals
                                                             k ub in
                                                         if uu____23162
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
                                           | uu____23187 -> bopt)
                                      FStar_Pervasives_Native.None) in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None -> []
                             | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                 let uu____23239 =
                                   let uu____23240 =
                                     exists_polymonadic_bind env1 i j in
                                   FStar_All.pipe_right uu____23240
                                     FStar_Util.is_some in
                                 if uu____23239
                                 then
                                   let uu____23287 =
                                     let uu____23292 =
                                       let uu____23293 =
                                         FStar_Ident.string_of_lid src in
                                       let uu____23294 =
                                         FStar_Ident.string_of_lid tgt in
                                       let uu____23295 =
                                         FStar_Ident.string_of_lid i in
                                       let uu____23296 =
                                         FStar_Ident.string_of_lid j in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____23293 uu____23294 uu____23295
                                         uu____23296 in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____23292) in
                                   FStar_Errors.raise_error uu____23287
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))])))) in
           let effects1 =
             let uu___1838_23331 = env1.effects in
             {
               decls = (uu___1838_23331.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1838_23331.polymonadic_binds);
               polymonadic_subcomps = (uu___1838_23331.polymonadic_subcomps)
             } in
           let uu___1841_23332 = env1 in
           {
             solver = (uu___1841_23332.solver);
             range = (uu___1841_23332.range);
             curmodule = (uu___1841_23332.curmodule);
             gamma = (uu___1841_23332.gamma);
             gamma_sig = (uu___1841_23332.gamma_sig);
             gamma_cache = (uu___1841_23332.gamma_cache);
             modules = (uu___1841_23332.modules);
             expected_typ = (uu___1841_23332.expected_typ);
             sigtab = (uu___1841_23332.sigtab);
             attrtab = (uu___1841_23332.attrtab);
             instantiate_imp = (uu___1841_23332.instantiate_imp);
             effects = effects1;
             generalize = (uu___1841_23332.generalize);
             letrecs = (uu___1841_23332.letrecs);
             top_level = (uu___1841_23332.top_level);
             check_uvars = (uu___1841_23332.check_uvars);
             use_eq = (uu___1841_23332.use_eq);
             use_eq_strict = (uu___1841_23332.use_eq_strict);
             is_iface = (uu___1841_23332.is_iface);
             admit = (uu___1841_23332.admit);
             lax = (uu___1841_23332.lax);
             lax_universes = (uu___1841_23332.lax_universes);
             phase1 = (uu___1841_23332.phase1);
             failhard = (uu___1841_23332.failhard);
             nosynth = (uu___1841_23332.nosynth);
             uvar_subtyping = (uu___1841_23332.uvar_subtyping);
             tc_term = (uu___1841_23332.tc_term);
             type_of = (uu___1841_23332.type_of);
             universe_of = (uu___1841_23332.universe_of);
             check_type_of = (uu___1841_23332.check_type_of);
             use_bv_sorts = (uu___1841_23332.use_bv_sorts);
             qtbl_name_and_index = (uu___1841_23332.qtbl_name_and_index);
             normalized_eff_names = (uu___1841_23332.normalized_eff_names);
             fv_delta_depths = (uu___1841_23332.fv_delta_depths);
             proof_ns = (uu___1841_23332.proof_ns);
             synth_hook = (uu___1841_23332.synth_hook);
             try_solve_implicits_hook =
               (uu___1841_23332.try_solve_implicits_hook);
             splice = (uu___1841_23332.splice);
             mpreprocess = (uu___1841_23332.mpreprocess);
             postprocess = (uu___1841_23332.postprocess);
             identifier_info = (uu___1841_23332.identifier_info);
             tc_hooks = (uu___1841_23332.tc_hooks);
             dsenv = (uu___1841_23332.dsenv);
             nbe = (uu___1841_23332.nbe);
             strict_args_tab = (uu___1841_23332.strict_args_tab);
             erasable_types_tab = (uu___1841_23332.erasable_types_tab);
             enable_defer_to_tac = (uu___1841_23332.enable_defer_to_tac)
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
              let uu____23376 = FStar_Ident.string_of_lid m in
              let uu____23377 = FStar_Ident.string_of_lid n in
              let uu____23378 = FStar_Ident.string_of_lid p in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____23376 uu____23377 uu____23378
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice") in
            let uu____23380 =
              let uu____23381 = exists_polymonadic_bind env1 m n in
              FStar_All.pipe_right uu____23381 FStar_Util.is_some in
            if uu____23380
            then
              let uu____23416 =
                let uu____23421 = err_msg true in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____23421) in
              FStar_Errors.raise_error uu____23416 env1.range
            else
              (let uu____23423 =
                 (let uu____23426 = join_opt env1 m n in
                  FStar_All.pipe_right uu____23426 FStar_Util.is_some) &&
                   (let uu____23450 = FStar_Ident.lid_equals m n in
                    Prims.op_Negation uu____23450) in
               if uu____23423
               then
                 let uu____23451 =
                   let uu____23456 = err_msg false in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____23456) in
                 FStar_Errors.raise_error uu____23451 env1.range
               else
                 (let uu___1856_23458 = env1 in
                  {
                    solver = (uu___1856_23458.solver);
                    range = (uu___1856_23458.range);
                    curmodule = (uu___1856_23458.curmodule);
                    gamma = (uu___1856_23458.gamma);
                    gamma_sig = (uu___1856_23458.gamma_sig);
                    gamma_cache = (uu___1856_23458.gamma_cache);
                    modules = (uu___1856_23458.modules);
                    expected_typ = (uu___1856_23458.expected_typ);
                    sigtab = (uu___1856_23458.sigtab);
                    attrtab = (uu___1856_23458.attrtab);
                    instantiate_imp = (uu___1856_23458.instantiate_imp);
                    effects =
                      (let uu___1858_23460 = env1.effects in
                       {
                         decls = (uu___1858_23460.decls);
                         order = (uu___1858_23460.order);
                         joins = (uu___1858_23460.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1858_23460.polymonadic_subcomps)
                       });
                    generalize = (uu___1856_23458.generalize);
                    letrecs = (uu___1856_23458.letrecs);
                    top_level = (uu___1856_23458.top_level);
                    check_uvars = (uu___1856_23458.check_uvars);
                    use_eq = (uu___1856_23458.use_eq);
                    use_eq_strict = (uu___1856_23458.use_eq_strict);
                    is_iface = (uu___1856_23458.is_iface);
                    admit = (uu___1856_23458.admit);
                    lax = (uu___1856_23458.lax);
                    lax_universes = (uu___1856_23458.lax_universes);
                    phase1 = (uu___1856_23458.phase1);
                    failhard = (uu___1856_23458.failhard);
                    nosynth = (uu___1856_23458.nosynth);
                    uvar_subtyping = (uu___1856_23458.uvar_subtyping);
                    tc_term = (uu___1856_23458.tc_term);
                    type_of = (uu___1856_23458.type_of);
                    universe_of = (uu___1856_23458.universe_of);
                    check_type_of = (uu___1856_23458.check_type_of);
                    use_bv_sorts = (uu___1856_23458.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1856_23458.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1856_23458.normalized_eff_names);
                    fv_delta_depths = (uu___1856_23458.fv_delta_depths);
                    proof_ns = (uu___1856_23458.proof_ns);
                    synth_hook = (uu___1856_23458.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1856_23458.try_solve_implicits_hook);
                    splice = (uu___1856_23458.splice);
                    mpreprocess = (uu___1856_23458.mpreprocess);
                    postprocess = (uu___1856_23458.postprocess);
                    identifier_info = (uu___1856_23458.identifier_info);
                    tc_hooks = (uu___1856_23458.tc_hooks);
                    dsenv = (uu___1856_23458.dsenv);
                    nbe = (uu___1856_23458.nbe);
                    strict_args_tab = (uu___1856_23458.strict_args_tab);
                    erasable_types_tab = (uu___1856_23458.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1856_23458.enable_defer_to_tac)
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
            let uu____23547 = FStar_Ident.string_of_lid m in
            let uu____23548 = FStar_Ident.string_of_lid n in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu____23547 uu____23548
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice") in
          let uu____23550 =
            let uu____23551 = exists_polymonadic_subcomp env1 m n in
            FStar_All.pipe_right uu____23551 FStar_Util.is_some in
          if uu____23550
          then
            let uu____23556 =
              let uu____23561 = err_msg true in
              (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____23561) in
            FStar_Errors.raise_error uu____23556 env1.range
          else
            (let uu____23563 =
               let uu____23564 = join_opt env1 m n in
               FStar_All.pipe_right uu____23564 FStar_Util.is_some in
             if uu____23563
             then
               let uu____23587 =
                 let uu____23592 = err_msg false in
                 (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____23592) in
               FStar_Errors.raise_error uu____23587 env1.range
             else
               (let uu___1871_23594 = env1 in
                {
                  solver = (uu___1871_23594.solver);
                  range = (uu___1871_23594.range);
                  curmodule = (uu___1871_23594.curmodule);
                  gamma = (uu___1871_23594.gamma);
                  gamma_sig = (uu___1871_23594.gamma_sig);
                  gamma_cache = (uu___1871_23594.gamma_cache);
                  modules = (uu___1871_23594.modules);
                  expected_typ = (uu___1871_23594.expected_typ);
                  sigtab = (uu___1871_23594.sigtab);
                  attrtab = (uu___1871_23594.attrtab);
                  instantiate_imp = (uu___1871_23594.instantiate_imp);
                  effects =
                    (let uu___1873_23596 = env1.effects in
                     {
                       decls = (uu___1873_23596.decls);
                       order = (uu___1873_23596.order);
                       joins = (uu___1873_23596.joins);
                       polymonadic_binds =
                         (uu___1873_23596.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___1871_23594.generalize);
                  letrecs = (uu___1871_23594.letrecs);
                  top_level = (uu___1871_23594.top_level);
                  check_uvars = (uu___1871_23594.check_uvars);
                  use_eq = (uu___1871_23594.use_eq);
                  use_eq_strict = (uu___1871_23594.use_eq_strict);
                  is_iface = (uu___1871_23594.is_iface);
                  admit = (uu___1871_23594.admit);
                  lax = (uu___1871_23594.lax);
                  lax_universes = (uu___1871_23594.lax_universes);
                  phase1 = (uu___1871_23594.phase1);
                  failhard = (uu___1871_23594.failhard);
                  nosynth = (uu___1871_23594.nosynth);
                  uvar_subtyping = (uu___1871_23594.uvar_subtyping);
                  tc_term = (uu___1871_23594.tc_term);
                  type_of = (uu___1871_23594.type_of);
                  universe_of = (uu___1871_23594.universe_of);
                  check_type_of = (uu___1871_23594.check_type_of);
                  use_bv_sorts = (uu___1871_23594.use_bv_sorts);
                  qtbl_name_and_index = (uu___1871_23594.qtbl_name_and_index);
                  normalized_eff_names =
                    (uu___1871_23594.normalized_eff_names);
                  fv_delta_depths = (uu___1871_23594.fv_delta_depths);
                  proof_ns = (uu___1871_23594.proof_ns);
                  synth_hook = (uu___1871_23594.synth_hook);
                  try_solve_implicits_hook =
                    (uu___1871_23594.try_solve_implicits_hook);
                  splice = (uu___1871_23594.splice);
                  mpreprocess = (uu___1871_23594.mpreprocess);
                  postprocess = (uu___1871_23594.postprocess);
                  identifier_info = (uu___1871_23594.identifier_info);
                  tc_hooks = (uu___1871_23594.tc_hooks);
                  dsenv = (uu___1871_23594.dsenv);
                  nbe = (uu___1871_23594.nbe);
                  strict_args_tab = (uu___1871_23594.strict_args_tab);
                  erasable_types_tab = (uu___1871_23594.erasable_types_tab);
                  enable_defer_to_tac = (uu___1871_23594.enable_defer_to_tac)
                }))
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1 ->
    fun b ->
      let uu___1877_23613 = env1 in
      {
        solver = (uu___1877_23613.solver);
        range = (uu___1877_23613.range);
        curmodule = (uu___1877_23613.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1877_23613.gamma_sig);
        gamma_cache = (uu___1877_23613.gamma_cache);
        modules = (uu___1877_23613.modules);
        expected_typ = (uu___1877_23613.expected_typ);
        sigtab = (uu___1877_23613.sigtab);
        attrtab = (uu___1877_23613.attrtab);
        instantiate_imp = (uu___1877_23613.instantiate_imp);
        effects = (uu___1877_23613.effects);
        generalize = (uu___1877_23613.generalize);
        letrecs = (uu___1877_23613.letrecs);
        top_level = (uu___1877_23613.top_level);
        check_uvars = (uu___1877_23613.check_uvars);
        use_eq = (uu___1877_23613.use_eq);
        use_eq_strict = (uu___1877_23613.use_eq_strict);
        is_iface = (uu___1877_23613.is_iface);
        admit = (uu___1877_23613.admit);
        lax = (uu___1877_23613.lax);
        lax_universes = (uu___1877_23613.lax_universes);
        phase1 = (uu___1877_23613.phase1);
        failhard = (uu___1877_23613.failhard);
        nosynth = (uu___1877_23613.nosynth);
        uvar_subtyping = (uu___1877_23613.uvar_subtyping);
        tc_term = (uu___1877_23613.tc_term);
        type_of = (uu___1877_23613.type_of);
        universe_of = (uu___1877_23613.universe_of);
        check_type_of = (uu___1877_23613.check_type_of);
        use_bv_sorts = (uu___1877_23613.use_bv_sorts);
        qtbl_name_and_index = (uu___1877_23613.qtbl_name_and_index);
        normalized_eff_names = (uu___1877_23613.normalized_eff_names);
        fv_delta_depths = (uu___1877_23613.fv_delta_depths);
        proof_ns = (uu___1877_23613.proof_ns);
        synth_hook = (uu___1877_23613.synth_hook);
        try_solve_implicits_hook = (uu___1877_23613.try_solve_implicits_hook);
        splice = (uu___1877_23613.splice);
        mpreprocess = (uu___1877_23613.mpreprocess);
        postprocess = (uu___1877_23613.postprocess);
        identifier_info = (uu___1877_23613.identifier_info);
        tc_hooks = (uu___1877_23613.tc_hooks);
        dsenv = (uu___1877_23613.dsenv);
        nbe = (uu___1877_23613.nbe);
        strict_args_tab = (uu___1877_23613.strict_args_tab);
        erasable_types_tab = (uu___1877_23613.erasable_types_tab);
        enable_defer_to_tac = (uu___1877_23613.enable_defer_to_tac)
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
            (let uu___1890_23668 = env1 in
             {
               solver = (uu___1890_23668.solver);
               range = (uu___1890_23668.range);
               curmodule = (uu___1890_23668.curmodule);
               gamma = rest;
               gamma_sig = (uu___1890_23668.gamma_sig);
               gamma_cache = (uu___1890_23668.gamma_cache);
               modules = (uu___1890_23668.modules);
               expected_typ = (uu___1890_23668.expected_typ);
               sigtab = (uu___1890_23668.sigtab);
               attrtab = (uu___1890_23668.attrtab);
               instantiate_imp = (uu___1890_23668.instantiate_imp);
               effects = (uu___1890_23668.effects);
               generalize = (uu___1890_23668.generalize);
               letrecs = (uu___1890_23668.letrecs);
               top_level = (uu___1890_23668.top_level);
               check_uvars = (uu___1890_23668.check_uvars);
               use_eq = (uu___1890_23668.use_eq);
               use_eq_strict = (uu___1890_23668.use_eq_strict);
               is_iface = (uu___1890_23668.is_iface);
               admit = (uu___1890_23668.admit);
               lax = (uu___1890_23668.lax);
               lax_universes = (uu___1890_23668.lax_universes);
               phase1 = (uu___1890_23668.phase1);
               failhard = (uu___1890_23668.failhard);
               nosynth = (uu___1890_23668.nosynth);
               uvar_subtyping = (uu___1890_23668.uvar_subtyping);
               tc_term = (uu___1890_23668.tc_term);
               type_of = (uu___1890_23668.type_of);
               universe_of = (uu___1890_23668.universe_of);
               check_type_of = (uu___1890_23668.check_type_of);
               use_bv_sorts = (uu___1890_23668.use_bv_sorts);
               qtbl_name_and_index = (uu___1890_23668.qtbl_name_and_index);
               normalized_eff_names = (uu___1890_23668.normalized_eff_names);
               fv_delta_depths = (uu___1890_23668.fv_delta_depths);
               proof_ns = (uu___1890_23668.proof_ns);
               synth_hook = (uu___1890_23668.synth_hook);
               try_solve_implicits_hook =
                 (uu___1890_23668.try_solve_implicits_hook);
               splice = (uu___1890_23668.splice);
               mpreprocess = (uu___1890_23668.mpreprocess);
               postprocess = (uu___1890_23668.postprocess);
               identifier_info = (uu___1890_23668.identifier_info);
               tc_hooks = (uu___1890_23668.tc_hooks);
               dsenv = (uu___1890_23668.dsenv);
               nbe = (uu___1890_23668.nbe);
               strict_args_tab = (uu___1890_23668.strict_args_tab);
               erasable_types_tab = (uu___1890_23668.erasable_types_tab);
               enable_defer_to_tac = (uu___1890_23668.enable_defer_to_tac)
             }))
    | uu____23669 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1 ->
    fun bs ->
      FStar_List.fold_left
        (fun env2 ->
           fun uu____23697 ->
             match uu____23697 with | (x, uu____23705) -> push_bv env2 x)
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
            let uu___1904_23739 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1904_23739.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1904_23739.FStar_Syntax_Syntax.index);
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
        let uu____23809 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____23809 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env1 univ_vars in
            let uu____23837 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____23837)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1 ->
    fun t ->
      let uu___1925_23852 = env1 in
      {
        solver = (uu___1925_23852.solver);
        range = (uu___1925_23852.range);
        curmodule = (uu___1925_23852.curmodule);
        gamma = (uu___1925_23852.gamma);
        gamma_sig = (uu___1925_23852.gamma_sig);
        gamma_cache = (uu___1925_23852.gamma_cache);
        modules = (uu___1925_23852.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1925_23852.sigtab);
        attrtab = (uu___1925_23852.attrtab);
        instantiate_imp = (uu___1925_23852.instantiate_imp);
        effects = (uu___1925_23852.effects);
        generalize = (uu___1925_23852.generalize);
        letrecs = (uu___1925_23852.letrecs);
        top_level = (uu___1925_23852.top_level);
        check_uvars = (uu___1925_23852.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1925_23852.use_eq_strict);
        is_iface = (uu___1925_23852.is_iface);
        admit = (uu___1925_23852.admit);
        lax = (uu___1925_23852.lax);
        lax_universes = (uu___1925_23852.lax_universes);
        phase1 = (uu___1925_23852.phase1);
        failhard = (uu___1925_23852.failhard);
        nosynth = (uu___1925_23852.nosynth);
        uvar_subtyping = (uu___1925_23852.uvar_subtyping);
        tc_term = (uu___1925_23852.tc_term);
        type_of = (uu___1925_23852.type_of);
        universe_of = (uu___1925_23852.universe_of);
        check_type_of = (uu___1925_23852.check_type_of);
        use_bv_sorts = (uu___1925_23852.use_bv_sorts);
        qtbl_name_and_index = (uu___1925_23852.qtbl_name_and_index);
        normalized_eff_names = (uu___1925_23852.normalized_eff_names);
        fv_delta_depths = (uu___1925_23852.fv_delta_depths);
        proof_ns = (uu___1925_23852.proof_ns);
        synth_hook = (uu___1925_23852.synth_hook);
        try_solve_implicits_hook = (uu___1925_23852.try_solve_implicits_hook);
        splice = (uu___1925_23852.splice);
        mpreprocess = (uu___1925_23852.mpreprocess);
        postprocess = (uu___1925_23852.postprocess);
        identifier_info = (uu___1925_23852.identifier_info);
        tc_hooks = (uu___1925_23852.tc_hooks);
        dsenv = (uu___1925_23852.dsenv);
        nbe = (uu___1925_23852.nbe);
        strict_args_tab = (uu___1925_23852.strict_args_tab);
        erasable_types_tab = (uu___1925_23852.erasable_types_tab);
        enable_defer_to_tac = (uu___1925_23852.enable_defer_to_tac)
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
    let uu____23880 = expected_typ env_ in
    ((let uu___1932_23886 = env_ in
      {
        solver = (uu___1932_23886.solver);
        range = (uu___1932_23886.range);
        curmodule = (uu___1932_23886.curmodule);
        gamma = (uu___1932_23886.gamma);
        gamma_sig = (uu___1932_23886.gamma_sig);
        gamma_cache = (uu___1932_23886.gamma_cache);
        modules = (uu___1932_23886.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1932_23886.sigtab);
        attrtab = (uu___1932_23886.attrtab);
        instantiate_imp = (uu___1932_23886.instantiate_imp);
        effects = (uu___1932_23886.effects);
        generalize = (uu___1932_23886.generalize);
        letrecs = (uu___1932_23886.letrecs);
        top_level = (uu___1932_23886.top_level);
        check_uvars = (uu___1932_23886.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1932_23886.use_eq_strict);
        is_iface = (uu___1932_23886.is_iface);
        admit = (uu___1932_23886.admit);
        lax = (uu___1932_23886.lax);
        lax_universes = (uu___1932_23886.lax_universes);
        phase1 = (uu___1932_23886.phase1);
        failhard = (uu___1932_23886.failhard);
        nosynth = (uu___1932_23886.nosynth);
        uvar_subtyping = (uu___1932_23886.uvar_subtyping);
        tc_term = (uu___1932_23886.tc_term);
        type_of = (uu___1932_23886.type_of);
        universe_of = (uu___1932_23886.universe_of);
        check_type_of = (uu___1932_23886.check_type_of);
        use_bv_sorts = (uu___1932_23886.use_bv_sorts);
        qtbl_name_and_index = (uu___1932_23886.qtbl_name_and_index);
        normalized_eff_names = (uu___1932_23886.normalized_eff_names);
        fv_delta_depths = (uu___1932_23886.fv_delta_depths);
        proof_ns = (uu___1932_23886.proof_ns);
        synth_hook = (uu___1932_23886.synth_hook);
        try_solve_implicits_hook = (uu___1932_23886.try_solve_implicits_hook);
        splice = (uu___1932_23886.splice);
        mpreprocess = (uu___1932_23886.mpreprocess);
        postprocess = (uu___1932_23886.postprocess);
        identifier_info = (uu___1932_23886.identifier_info);
        tc_hooks = (uu___1932_23886.tc_hooks);
        dsenv = (uu___1932_23886.dsenv);
        nbe = (uu___1932_23886.nbe);
        strict_args_tab = (uu___1932_23886.strict_args_tab);
        erasable_types_tab = (uu___1932_23886.erasable_types_tab);
        enable_defer_to_tac = (uu___1932_23886.enable_defer_to_tac)
      }), uu____23880)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23896 =
      let uu____23897 = FStar_Ident.id_of_text "" in [uu____23897] in
    FStar_Ident.lid_of_ids uu____23896 in
  fun env1 ->
    fun m ->
      let sigs =
        let uu____23903 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____23903
        then
          let uu____23906 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu____23906 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env1 sigs;
      (let uu___1940_23933 = env1 in
       {
         solver = (uu___1940_23933.solver);
         range = (uu___1940_23933.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1940_23933.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1940_23933.expected_typ);
         sigtab = (uu___1940_23933.sigtab);
         attrtab = (uu___1940_23933.attrtab);
         instantiate_imp = (uu___1940_23933.instantiate_imp);
         effects = (uu___1940_23933.effects);
         generalize = (uu___1940_23933.generalize);
         letrecs = (uu___1940_23933.letrecs);
         top_level = (uu___1940_23933.top_level);
         check_uvars = (uu___1940_23933.check_uvars);
         use_eq = (uu___1940_23933.use_eq);
         use_eq_strict = (uu___1940_23933.use_eq_strict);
         is_iface = (uu___1940_23933.is_iface);
         admit = (uu___1940_23933.admit);
         lax = (uu___1940_23933.lax);
         lax_universes = (uu___1940_23933.lax_universes);
         phase1 = (uu___1940_23933.phase1);
         failhard = (uu___1940_23933.failhard);
         nosynth = (uu___1940_23933.nosynth);
         uvar_subtyping = (uu___1940_23933.uvar_subtyping);
         tc_term = (uu___1940_23933.tc_term);
         type_of = (uu___1940_23933.type_of);
         universe_of = (uu___1940_23933.universe_of);
         check_type_of = (uu___1940_23933.check_type_of);
         use_bv_sorts = (uu___1940_23933.use_bv_sorts);
         qtbl_name_and_index = (uu___1940_23933.qtbl_name_and_index);
         normalized_eff_names = (uu___1940_23933.normalized_eff_names);
         fv_delta_depths = (uu___1940_23933.fv_delta_depths);
         proof_ns = (uu___1940_23933.proof_ns);
         synth_hook = (uu___1940_23933.synth_hook);
         try_solve_implicits_hook =
           (uu___1940_23933.try_solve_implicits_hook);
         splice = (uu___1940_23933.splice);
         mpreprocess = (uu___1940_23933.mpreprocess);
         postprocess = (uu___1940_23933.postprocess);
         identifier_info = (uu___1940_23933.identifier_info);
         tc_hooks = (uu___1940_23933.tc_hooks);
         dsenv = (uu___1940_23933.dsenv);
         nbe = (uu___1940_23933.nbe);
         strict_args_tab = (uu___1940_23933.strict_args_tab);
         erasable_types_tab = (uu___1940_23933.erasable_types_tab);
         enable_defer_to_tac = (uu___1940_23933.enable_defer_to_tac)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1 ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23984)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____23988, (uu____23989, t)))::tl
          ->
          let uu____24010 =
            let uu____24013 = FStar_Syntax_Free.uvars t in
            ext out uu____24013 in
          aux uu____24010 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24016;
            FStar_Syntax_Syntax.index = uu____24017;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____24024 =
            let uu____24027 = FStar_Syntax_Free.uvars t in
            ext out uu____24027 in
          aux uu____24024 tl in
    aux no_uvs env1.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1 ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24084)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____24088, (uu____24089, t)))::tl
          ->
          let uu____24110 =
            let uu____24113 = FStar_Syntax_Free.univs t in
            ext out uu____24113 in
          aux uu____24110 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24116;
            FStar_Syntax_Syntax.index = uu____24117;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____24124 =
            let uu____24127 = FStar_Syntax_Free.univs t in
            ext out uu____24127 in
          aux uu____24124 tl in
    aux no_univs env1.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env1 ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu____24188 = FStar_Util.set_add uname out in
          aux uu____24188 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____24191, (uu____24192, t)))::tl
          ->
          let uu____24213 =
            let uu____24216 = FStar_Syntax_Free.univnames t in
            ext out uu____24216 in
          aux uu____24213 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24219;
            FStar_Syntax_Syntax.index = uu____24220;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____24227 =
            let uu____24230 = FStar_Syntax_Free.univnames t in
            ext out uu____24230 in
          aux uu____24227 tl in
    aux no_univ_names env1.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24250 ->
            match uu___12_24250 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24254 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24267 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____24277 =
      let uu____24286 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____24286
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____24277 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1 -> bound_vars_of_bindings env1.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1 -> binders_of_bindings env1.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu____24330 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24340 ->
              match uu___13_24340 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24342 = FStar_Syntax_Print.bv_to_string x in
                  Prims.op_Hat "Binding_var " uu____24342
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____24344 = FStar_Ident.string_of_id u in
                  Prims.op_Hat "Binding_univ " uu____24344
              | FStar_Syntax_Syntax.Binding_lid (l, uu____24346) ->
                  let uu____24363 = FStar_Ident.string_of_lid l in
                  Prims.op_Hat "Binding_lid " uu____24363)) in
    FStar_All.pipe_right uu____24330 (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24370 ->
    match uu___14_24370 with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24372 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.op_Hat "Unfold " uu____24372
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____24392 ->
         fun v ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1 ->
    fun path ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([], uu____24434) -> true
        | (x::xs1, y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24453, uu____24454) -> false in
      let uu____24463 =
        FStar_List.tryFind
          (fun uu____24481 ->
             match uu____24481 with | (p, uu____24489) -> str_i_prefix p path)
          env1.proof_ns in
      match uu____24463 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____24500, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____24522 = FStar_Ident.path_of_lid lid in
      should_enc_path env1 uu____24522
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___2083_24540 = e in
        {
          solver = (uu___2083_24540.solver);
          range = (uu___2083_24540.range);
          curmodule = (uu___2083_24540.curmodule);
          gamma = (uu___2083_24540.gamma);
          gamma_sig = (uu___2083_24540.gamma_sig);
          gamma_cache = (uu___2083_24540.gamma_cache);
          modules = (uu___2083_24540.modules);
          expected_typ = (uu___2083_24540.expected_typ);
          sigtab = (uu___2083_24540.sigtab);
          attrtab = (uu___2083_24540.attrtab);
          instantiate_imp = (uu___2083_24540.instantiate_imp);
          effects = (uu___2083_24540.effects);
          generalize = (uu___2083_24540.generalize);
          letrecs = (uu___2083_24540.letrecs);
          top_level = (uu___2083_24540.top_level);
          check_uvars = (uu___2083_24540.check_uvars);
          use_eq = (uu___2083_24540.use_eq);
          use_eq_strict = (uu___2083_24540.use_eq_strict);
          is_iface = (uu___2083_24540.is_iface);
          admit = (uu___2083_24540.admit);
          lax = (uu___2083_24540.lax);
          lax_universes = (uu___2083_24540.lax_universes);
          phase1 = (uu___2083_24540.phase1);
          failhard = (uu___2083_24540.failhard);
          nosynth = (uu___2083_24540.nosynth);
          uvar_subtyping = (uu___2083_24540.uvar_subtyping);
          tc_term = (uu___2083_24540.tc_term);
          type_of = (uu___2083_24540.type_of);
          universe_of = (uu___2083_24540.universe_of);
          check_type_of = (uu___2083_24540.check_type_of);
          use_bv_sorts = (uu___2083_24540.use_bv_sorts);
          qtbl_name_and_index = (uu___2083_24540.qtbl_name_and_index);
          normalized_eff_names = (uu___2083_24540.normalized_eff_names);
          fv_delta_depths = (uu___2083_24540.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2083_24540.synth_hook);
          try_solve_implicits_hook =
            (uu___2083_24540.try_solve_implicits_hook);
          splice = (uu___2083_24540.splice);
          mpreprocess = (uu___2083_24540.mpreprocess);
          postprocess = (uu___2083_24540.postprocess);
          identifier_info = (uu___2083_24540.identifier_info);
          tc_hooks = (uu___2083_24540.tc_hooks);
          dsenv = (uu___2083_24540.dsenv);
          nbe = (uu___2083_24540.nbe);
          strict_args_tab = (uu___2083_24540.strict_args_tab);
          erasable_types_tab = (uu___2083_24540.erasable_types_tab);
          enable_defer_to_tac = (uu___2083_24540.enable_defer_to_tac)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___2092_24580 = e in
      {
        solver = (uu___2092_24580.solver);
        range = (uu___2092_24580.range);
        curmodule = (uu___2092_24580.curmodule);
        gamma = (uu___2092_24580.gamma);
        gamma_sig = (uu___2092_24580.gamma_sig);
        gamma_cache = (uu___2092_24580.gamma_cache);
        modules = (uu___2092_24580.modules);
        expected_typ = (uu___2092_24580.expected_typ);
        sigtab = (uu___2092_24580.sigtab);
        attrtab = (uu___2092_24580.attrtab);
        instantiate_imp = (uu___2092_24580.instantiate_imp);
        effects = (uu___2092_24580.effects);
        generalize = (uu___2092_24580.generalize);
        letrecs = (uu___2092_24580.letrecs);
        top_level = (uu___2092_24580.top_level);
        check_uvars = (uu___2092_24580.check_uvars);
        use_eq = (uu___2092_24580.use_eq);
        use_eq_strict = (uu___2092_24580.use_eq_strict);
        is_iface = (uu___2092_24580.is_iface);
        admit = (uu___2092_24580.admit);
        lax = (uu___2092_24580.lax);
        lax_universes = (uu___2092_24580.lax_universes);
        phase1 = (uu___2092_24580.phase1);
        failhard = (uu___2092_24580.failhard);
        nosynth = (uu___2092_24580.nosynth);
        uvar_subtyping = (uu___2092_24580.uvar_subtyping);
        tc_term = (uu___2092_24580.tc_term);
        type_of = (uu___2092_24580.type_of);
        universe_of = (uu___2092_24580.universe_of);
        check_type_of = (uu___2092_24580.check_type_of);
        use_bv_sorts = (uu___2092_24580.use_bv_sorts);
        qtbl_name_and_index = (uu___2092_24580.qtbl_name_and_index);
        normalized_eff_names = (uu___2092_24580.normalized_eff_names);
        fv_delta_depths = (uu___2092_24580.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2092_24580.synth_hook);
        try_solve_implicits_hook = (uu___2092_24580.try_solve_implicits_hook);
        splice = (uu___2092_24580.splice);
        mpreprocess = (uu___2092_24580.mpreprocess);
        postprocess = (uu___2092_24580.postprocess);
        identifier_info = (uu___2092_24580.identifier_info);
        tc_hooks = (uu___2092_24580.tc_hooks);
        dsenv = (uu___2092_24580.dsenv);
        nbe = (uu___2092_24580.nbe);
        strict_args_tab = (uu___2092_24580.strict_args_tab);
        erasable_types_tab = (uu___2092_24580.erasable_types_tab);
        enable_defer_to_tac = (uu___2092_24580.enable_defer_to_tac)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____24595 = FStar_Syntax_Free.names t in
      let uu____24598 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____24595 uu____24598
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____24619 = unbound_vars e t in
      FStar_Util.set_is_empty uu____24619
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____24627 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____24627
let (string_of_proof_ns : env -> Prims.string) =
  fun env1 ->
    let aux uu____24644 =
      match uu____24644 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24654 = FStar_Ident.text_of_path p in
             Prims.op_Hat (if b then "+" else "-") uu____24654) in
    let uu____24656 =
      let uu____24659 = FStar_List.map aux env1.proof_ns in
      FStar_All.pipe_right uu____24659 FStar_List.rev in
    FStar_All.pipe_right uu____24656 (FStar_String.concat " ")
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
        FStar_TypeChecker_Common.deferred_to_tac = uu____24699;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([], []);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____24715 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu____24715 with
                   | FStar_Pervasives_Native.Some uu____24718 -> true
                   | FStar_Pervasives_Native.None -> false)))
    | uu____24719 -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial;
        FStar_TypeChecker_Common.deferred_to_tac = uu____24725;
        FStar_TypeChecker_Common.deferred = uu____24726;
        FStar_TypeChecker_Common.univ_ineqs = uu____24727;
        FStar_TypeChecker_Common.implicits = uu____24728;_} -> true
    | uu____24737 -> false
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
          let uu___2138_24756 = g in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2138_24756.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2138_24756.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2138_24756.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2138_24756.FStar_TypeChecker_Common.implicits)
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
          let uu____24791 = FStar_Options.defensive () in
          if uu____24791
          then
            let s = FStar_Syntax_Free.names t in
            let uu____24795 =
              let uu____24796 =
                let uu____24797 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24797 in
              Prims.op_Negation uu____24796 in
            (if uu____24795
             then
               let uu____24802 =
                 let uu____24807 =
                   let uu____24808 = FStar_Syntax_Print.term_to_string t in
                   let uu____24809 =
                     let uu____24810 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____24810
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24808 uu____24809 in
                 (FStar_Errors.Warning_Defensive, uu____24807) in
               FStar_Errors.log_issue rng uu____24802
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
          let uu____24841 =
            let uu____24842 = FStar_Options.defensive () in
            Prims.op_Negation uu____24842 in
          if uu____24841
          then ()
          else
            (let uu____24844 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____24844 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____24867 =
            let uu____24868 = FStar_Options.defensive () in
            Prims.op_Negation uu____24868 in
          if uu____24867
          then ()
          else
            (let uu____24870 = bound_vars e in
             def_check_closed_in rng msg uu____24870 t)
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
          let uu___2175_24905 = g in
          let uu____24906 =
            let uu____24907 =
              let uu____24908 =
                let uu____24909 =
                  let uu____24926 =
                    let uu____24937 = FStar_Syntax_Syntax.as_arg e in
                    [uu____24937] in
                  (f, uu____24926) in
                FStar_Syntax_Syntax.Tm_app uu____24909 in
              FStar_Syntax_Syntax.mk uu____24908 f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun uu____24974 ->
                 FStar_TypeChecker_Common.NonTrivial uu____24974) uu____24907 in
          {
            FStar_TypeChecker_Common.guard_f = uu____24906;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2175_24905.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2175_24905.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2175_24905.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2175_24905.FStar_TypeChecker_Common.implicits)
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
          let uu___2182_24991 = g in
          let uu____24992 =
            let uu____24993 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____24993 in
          {
            FStar_TypeChecker_Common.guard_f = uu____24992;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2182_24991.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2182_24991.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2182_24991.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2182_24991.FStar_TypeChecker_Common.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___2187_25009 = g in
          let uu____25010 =
            let uu____25011 = map FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu____25011 in
          {
            FStar_TypeChecker_Common.guard_f = uu____25010;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2187_25009.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2187_25009.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2187_25009.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2187_25009.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2191_25013 = g in
          let uu____25014 =
            let uu____25015 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____25015 in
          {
            FStar_TypeChecker_Common.guard_f = uu____25014;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2191_25013.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2191_25013.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2191_25013.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2191_25013.FStar_TypeChecker_Common.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25021 ->
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
                       let uu____25092 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____25092
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___2214_25096 = g in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2214_25096.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2214_25096.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2214_25096.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2214_25096.FStar_TypeChecker_Common.implicits)
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
               let uu____25129 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____25129
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
            let uu___2229_25152 = g in
            let uu____25153 =
              let uu____25154 = close_forall env1 binders f in
              FStar_TypeChecker_Common.NonTrivial uu____25154 in
            {
              FStar_TypeChecker_Common.guard_f = uu____25153;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2229_25152.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2229_25152.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2229_25152.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2229_25152.FStar_TypeChecker_Common.implicits)
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
              let uu____25201 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
              match uu____25201 with
              | FStar_Pervasives_Native.Some
                  (uu____25226::(tm, uu____25228)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos in
                  (t, [], trivial_guard)
              | uu____25292 ->
                  let binders = all_binders env1 in
                  let gamma = env1.gamma in
                  let ctx_uvar =
                    let uu____25310 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25310;
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
                    (let uu____25343 =
                       debug env1 (FStar_Options.Other "ImplicitTrace") in
                     if uu____25343
                     then
                       let uu____25344 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____25344
                     else ());
                    (let g =
                       let uu___2253_25347 = trivial_guard in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2253_25347.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2253_25347.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2253_25347.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2253_25347.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____25398 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____25459 ->
                      fun b ->
                        match uu____25459 with
                        | (substs1, uvars, g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                            let uu____25501 =
                              match FStar_Pervasives_Native.snd b with
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                  t)) ->
                                  let uu____25519 =
                                    let uu____25522 =
                                      let uu____25523 =
                                        let uu____25530 =
                                          FStar_Dyn.mkdyn env1 in
                                        (uu____25530, t) in
                                      FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                        uu____25523 in
                                    FStar_Pervasives_Native.Some uu____25522 in
                                  (uu____25519, false)
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  ((FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                         t)), true)
                              | uu____25540 ->
                                  (FStar_Pervasives_Native.None, false) in
                            (match uu____25501 with
                             | (ctx_uvar_meta_t, strict) ->
                                 let uu____25561 =
                                   let uu____25574 = reason b in
                                   new_implicit_var_aux uu____25574 r env1
                                     sort
                                     (if strict
                                      then FStar_Syntax_Syntax.Strict
                                      else FStar_Syntax_Syntax.Allow_untyped)
                                     ctx_uvar_meta_t in
                                 (match uu____25561 with
                                  | (t, l_ctx_uvars, g_t) ->
                                      ((let uu____25602 =
                                          FStar_All.pipe_left (debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsEqns") in
                                        if uu____25602
                                        then
                                          FStar_List.iter
                                            (fun uu____25611 ->
                                               match uu____25611 with
                                               | (ctx_uvar, uu____25617) ->
                                                   let uu____25618 =
                                                     FStar_Syntax_Print.ctx_uvar_to_string_no_reason
                                                       ctx_uvar in
                                                   FStar_Util.print1
                                                     "Layered Effect uvar : %s\n"
                                                     uu____25618) l_ctx_uvars
                                        else ());
                                       (let uu____25620 =
                                          let uu____25623 =
                                            let uu____25626 =
                                              let uu____25627 =
                                                let uu____25634 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____25634, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____25627 in
                                            [uu____25626] in
                                          FStar_List.append substs1
                                            uu____25623 in
                                        let uu____25645 = conj_guard g g_t in
                                        (uu____25620,
                                          (FStar_List.append uvars [t]),
                                          uu____25645))))))
                   (substs, [], trivial_guard)) in
            FStar_All.pipe_right uu____25398
              (fun uu____25674 ->
                 match uu____25674 with
                 | (uu____25691, uvars, g) -> (uvars, g))
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
                let uu____25731 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid in
                FStar_All.pipe_right uu____25731 FStar_Util.must in
              let uu____25748 = inst_tscheme_with post_ts [u] in
              match uu____25748 with
              | (uu____25753, post) ->
                  let uu____25755 =
                    let uu____25756 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                    [uu____25756] in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____25755 r in
            let uu____25789 =
              let uu____25790 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg in
              [uu____25790] in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____25789 r
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25825 -> ());
    push = (fun uu____25827 -> ());
    pop = (fun uu____25829 -> ());
    snapshot =
      (fun uu____25831 ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25840 -> fun uu____25841 -> ());
    encode_sig = (fun uu____25852 -> fun uu____25853 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____25859 =
             let uu____25866 = FStar_Options.peek () in (e, g, uu____25866) in
           [uu____25859]);
    solve = (fun uu____25882 -> fun uu____25883 -> fun uu____25884 -> ());
    finish = (fun uu____25890 -> ());
    refresh = (fun uu____25892 -> ())
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
        | uu____25992 -> false in
      let uu____26005 =
        FStar_Util.find_opt
          (fun uu____26037 ->
             match uu____26037 with
             | (lbname', uu____26051, uu____26052, uu____26053) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
      match uu____26005 with
      | FStar_Pervasives_Native.Some
          (uu____26064, arity, uu____26066, uu____26067) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None