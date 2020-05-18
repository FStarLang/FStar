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
  fun projectee -> match projectee with | Beta -> true | uu____106 -> false
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____117 -> false
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____128 -> false
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____139 -> false
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Exclude _0 -> true | uu____151 -> false
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee -> match projectee with | Exclude _0 -> _0
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____169 -> false
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____180 -> false
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____191 -> false
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding -> true | uu____202 -> false
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Inlining -> true | uu____213 -> false
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee ->
    match projectee with | DoNotUnfoldPureLets -> true | uu____224 -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu____236 -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____257 -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____284 -> false
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____311 -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldTac -> true | uu____335 -> false
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PureSubtermsWithinComputations -> true
    | uu____346 -> false
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Simplify -> true | uu____357 -> false
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | EraseUniverses -> true | uu____368 -> false
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowUnboundUniverses -> true | uu____379 -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____390 -> false
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CompressUvars -> true | uu____401 -> false
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee ->
    match projectee with | NoFullNorm -> true | uu____412 -> false
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckNoUvars -> true | uu____423 -> false
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu____434 -> false
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Unascribe -> true | uu____445 -> false
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____456 -> false
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee ->
    match projectee with | ForExtraction -> true | uu____467 -> false
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
      | uu____528 -> false
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | NoDelta -> true | uu____554 -> false
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | InliningDelta -> true | uu____565 -> false
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding_only -> true | uu____576 -> false
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Unfold _0 -> true | uu____588 -> false
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
    | { decls; order; joins; polymonadic_binds;_} -> decls
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> order
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> joins
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
    | { decls; order; joins; polymonadic_binds;_} -> polymonadic_binds
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
           (fun uu___0_14524 ->
              match uu___0_14524 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14527 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst uu____14527 in
                  let uu____14528 =
                    let uu____14529 = FStar_Syntax_Subst.compress y in
                    uu____14529.FStar_Syntax_Syntax.n in
                  (match uu____14528 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14533 =
                         let uu___327_14534 = y1 in
                         let uu____14535 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14534.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14534.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14535
                         } in
                       FStar_Syntax_Syntax.Binding_var uu____14533
                   | uu____14538 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst ->
    fun env1 ->
      let uu___333_14552 = env1 in
      let uu____14553 = rename_gamma subst env1.gamma in
      {
        solver = (uu___333_14552.solver);
        range = (uu___333_14552.range);
        curmodule = (uu___333_14552.curmodule);
        gamma = uu____14553;
        gamma_sig = (uu___333_14552.gamma_sig);
        gamma_cache = (uu___333_14552.gamma_cache);
        modules = (uu___333_14552.modules);
        expected_typ = (uu___333_14552.expected_typ);
        sigtab = (uu___333_14552.sigtab);
        attrtab = (uu___333_14552.attrtab);
        instantiate_imp = (uu___333_14552.instantiate_imp);
        effects = (uu___333_14552.effects);
        generalize = (uu___333_14552.generalize);
        letrecs = (uu___333_14552.letrecs);
        top_level = (uu___333_14552.top_level);
        check_uvars = (uu___333_14552.check_uvars);
        use_eq = (uu___333_14552.use_eq);
        use_eq_strict = (uu___333_14552.use_eq_strict);
        is_iface = (uu___333_14552.is_iface);
        admit = (uu___333_14552.admit);
        lax = (uu___333_14552.lax);
        lax_universes = (uu___333_14552.lax_universes);
        phase1 = (uu___333_14552.phase1);
        failhard = (uu___333_14552.failhard);
        nosynth = (uu___333_14552.nosynth);
        uvar_subtyping = (uu___333_14552.uvar_subtyping);
        tc_term = (uu___333_14552.tc_term);
        type_of = (uu___333_14552.type_of);
        universe_of = (uu___333_14552.universe_of);
        check_type_of = (uu___333_14552.check_type_of);
        use_bv_sorts = (uu___333_14552.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14552.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14552.normalized_eff_names);
        fv_delta_depths = (uu___333_14552.fv_delta_depths);
        proof_ns = (uu___333_14552.proof_ns);
        synth_hook = (uu___333_14552.synth_hook);
        try_solve_implicits_hook = (uu___333_14552.try_solve_implicits_hook);
        splice = (uu___333_14552.splice);
        mpreprocess = (uu___333_14552.mpreprocess);
        postprocess = (uu___333_14552.postprocess);
        identifier_info = (uu___333_14552.identifier_info);
        tc_hooks = (uu___333_14552.tc_hooks);
        dsenv = (uu___333_14552.dsenv);
        nbe = (uu___333_14552.nbe);
        strict_args_tab = (uu___333_14552.strict_args_tab);
        erasable_types_tab = (uu___333_14552.erasable_types_tab);
        enable_defer_to_tac = (uu___333_14552.enable_defer_to_tac)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14561 -> fun uu____14562 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env1 -> env1.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___340_14584 = env1 in
      {
        solver = (uu___340_14584.solver);
        range = (uu___340_14584.range);
        curmodule = (uu___340_14584.curmodule);
        gamma = (uu___340_14584.gamma);
        gamma_sig = (uu___340_14584.gamma_sig);
        gamma_cache = (uu___340_14584.gamma_cache);
        modules = (uu___340_14584.modules);
        expected_typ = (uu___340_14584.expected_typ);
        sigtab = (uu___340_14584.sigtab);
        attrtab = (uu___340_14584.attrtab);
        instantiate_imp = (uu___340_14584.instantiate_imp);
        effects = (uu___340_14584.effects);
        generalize = (uu___340_14584.generalize);
        letrecs = (uu___340_14584.letrecs);
        top_level = (uu___340_14584.top_level);
        check_uvars = (uu___340_14584.check_uvars);
        use_eq = (uu___340_14584.use_eq);
        use_eq_strict = (uu___340_14584.use_eq_strict);
        is_iface = (uu___340_14584.is_iface);
        admit = (uu___340_14584.admit);
        lax = (uu___340_14584.lax);
        lax_universes = (uu___340_14584.lax_universes);
        phase1 = (uu___340_14584.phase1);
        failhard = (uu___340_14584.failhard);
        nosynth = (uu___340_14584.nosynth);
        uvar_subtyping = (uu___340_14584.uvar_subtyping);
        tc_term = (uu___340_14584.tc_term);
        type_of = (uu___340_14584.type_of);
        universe_of = (uu___340_14584.universe_of);
        check_type_of = (uu___340_14584.check_type_of);
        use_bv_sorts = (uu___340_14584.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14584.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14584.normalized_eff_names);
        fv_delta_depths = (uu___340_14584.fv_delta_depths);
        proof_ns = (uu___340_14584.proof_ns);
        synth_hook = (uu___340_14584.synth_hook);
        try_solve_implicits_hook = (uu___340_14584.try_solve_implicits_hook);
        splice = (uu___340_14584.splice);
        mpreprocess = (uu___340_14584.mpreprocess);
        postprocess = (uu___340_14584.postprocess);
        identifier_info = (uu___340_14584.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14584.dsenv);
        nbe = (uu___340_14584.nbe);
        strict_args_tab = (uu___340_14584.strict_args_tab);
        erasable_types_tab = (uu___340_14584.erasable_types_tab);
        enable_defer_to_tac = (uu___340_14584.enable_defer_to_tac)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___344_14596 = e in
      let uu____14597 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
      {
        solver = (uu___344_14596.solver);
        range = (uu___344_14596.range);
        curmodule = (uu___344_14596.curmodule);
        gamma = (uu___344_14596.gamma);
        gamma_sig = (uu___344_14596.gamma_sig);
        gamma_cache = (uu___344_14596.gamma_cache);
        modules = (uu___344_14596.modules);
        expected_typ = (uu___344_14596.expected_typ);
        sigtab = (uu___344_14596.sigtab);
        attrtab = (uu___344_14596.attrtab);
        instantiate_imp = (uu___344_14596.instantiate_imp);
        effects = (uu___344_14596.effects);
        generalize = (uu___344_14596.generalize);
        letrecs = (uu___344_14596.letrecs);
        top_level = (uu___344_14596.top_level);
        check_uvars = (uu___344_14596.check_uvars);
        use_eq = (uu___344_14596.use_eq);
        use_eq_strict = (uu___344_14596.use_eq_strict);
        is_iface = (uu___344_14596.is_iface);
        admit = (uu___344_14596.admit);
        lax = (uu___344_14596.lax);
        lax_universes = (uu___344_14596.lax_universes);
        phase1 = (uu___344_14596.phase1);
        failhard = (uu___344_14596.failhard);
        nosynth = (uu___344_14596.nosynth);
        uvar_subtyping = (uu___344_14596.uvar_subtyping);
        tc_term = (uu___344_14596.tc_term);
        type_of = (uu___344_14596.type_of);
        universe_of = (uu___344_14596.universe_of);
        check_type_of = (uu___344_14596.check_type_of);
        use_bv_sorts = (uu___344_14596.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14596.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14596.normalized_eff_names);
        fv_delta_depths = (uu___344_14596.fv_delta_depths);
        proof_ns = (uu___344_14596.proof_ns);
        synth_hook = (uu___344_14596.synth_hook);
        try_solve_implicits_hook = (uu___344_14596.try_solve_implicits_hook);
        splice = (uu___344_14596.splice);
        mpreprocess = (uu___344_14596.mpreprocess);
        postprocess = (uu___344_14596.postprocess);
        identifier_info = (uu___344_14596.identifier_info);
        tc_hooks = (uu___344_14596.tc_hooks);
        dsenv = uu____14597;
        nbe = (uu___344_14596.nbe);
        strict_args_tab = (uu___344_14596.strict_args_tab);
        erasable_types_tab = (uu___344_14596.erasable_types_tab);
        enable_defer_to_tac = (uu___344_14596.enable_defer_to_tac)
      }
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e -> FStar_Syntax_DsEnv.dep_graph e.dsenv
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1 ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14614 = FStar_Ident.string_of_lid env1.curmodule in
       FStar_Options.should_verify uu____14614)
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d ->
    fun q ->
      match (d, q) with
      | (NoDelta, uu____14629) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____14632,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____14634, FStar_Syntax_Syntax.Visible_default) -> true
      | (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu____14637 -> false
let (default_table_size : Prims.int) = (Prims.of_int (200))
let new_sigtab : 'uuuuuu14651 . unit -> 'uuuuuu14651 FStar_Util.smap =
  fun uu____14658 -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'uuuuuu14664 . unit -> 'uuuuuu14664 FStar_Util.smap =
  fun uu____14671 -> FStar_Util.smap_create (Prims.of_int (100))
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
                  let uu____14809 = new_gamma_cache () in
                  let uu____14812 = new_sigtab () in
                  let uu____14815 = new_sigtab () in
                  let uu____14822 =
                    let uu____14837 =
                      FStar_Util.smap_create (Prims.of_int (10)) in
                    (uu____14837, FStar_Pervasives_Native.None) in
                  let uu____14858 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu____14862 =
                    FStar_Util.smap_create (Prims.of_int (50)) in
                  let uu____14866 = FStar_Options.using_facts_from () in
                  let uu____14867 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty in
                  let uu____14870 = FStar_Syntax_DsEnv.empty_env deps in
                  let uu____14871 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  let uu____14885 =
                    FStar_Util.smap_create (Prims.of_int (20)) in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14809;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14812;
                    attrtab = uu____14815;
                    instantiate_imp = true;
                    effects =
                      {
                        decls = [];
                        order = [];
                        joins = [];
                        polymonadic_binds = []
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
                    qtbl_name_and_index = uu____14822;
                    normalized_eff_names = uu____14858;
                    fv_delta_depths = uu____14862;
                    proof_ns = uu____14866;
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
                    identifier_info = uu____14867;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14870;
                    nbe;
                    strict_args_tab = uu____14871;
                    erasable_types_tab = uu____14885;
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
  fun uu____15082 ->
    let uu____15083 = FStar_ST.op_Bang query_indices in
    match uu____15083 with
    | [] -> failwith "Empty query indices!"
    | uu____15138 ->
        let uu____15148 =
          let uu____15158 =
            let uu____15166 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____15166 in
          let uu____15220 = FStar_ST.op_Bang query_indices in uu____15158 ::
            uu____15220 in
        FStar_ST.op_Colon_Equals query_indices uu____15148
let (pop_query_indices : unit -> unit) =
  fun uu____15316 ->
    let uu____15317 = FStar_ST.op_Bang query_indices in
    match uu____15317 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15444 ->
    FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15481 ->
    match uu____15481 with
    | (l, n) ->
        let uu____15491 = FStar_ST.op_Bang query_indices in
        (match uu____15491 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15613 -> failwith "Empty query indices")
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15636 ->
    let uu____15637 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____15637
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env1 ->
    (let uu____15705 =
       let uu____15708 = FStar_ST.op_Bang stack in env1 :: uu____15708 in
     FStar_ST.op_Colon_Equals stack uu____15705);
    (let uu___418_15757 = env1 in
     let uu____15758 = FStar_Util.smap_copy (gamma_cache env1) in
     let uu____15761 = FStar_Util.smap_copy (sigtab env1) in
     let uu____15764 = FStar_Util.smap_copy (attrtab env1) in
     let uu____15771 =
       let uu____15786 =
         let uu____15790 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu____15790 in
       let uu____15822 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu____15786, uu____15822) in
     let uu____15871 = FStar_Util.smap_copy env1.normalized_eff_names in
     let uu____15874 = FStar_Util.smap_copy env1.fv_delta_depths in
     let uu____15877 =
       let uu____15880 = FStar_ST.op_Bang env1.identifier_info in
       FStar_Util.mk_ref uu____15880 in
     let uu____15900 = FStar_Util.smap_copy env1.strict_args_tab in
     let uu____15913 = FStar_Util.smap_copy env1.erasable_types_tab in
     {
       solver = (uu___418_15757.solver);
       range = (uu___418_15757.range);
       curmodule = (uu___418_15757.curmodule);
       gamma = (uu___418_15757.gamma);
       gamma_sig = (uu___418_15757.gamma_sig);
       gamma_cache = uu____15758;
       modules = (uu___418_15757.modules);
       expected_typ = (uu___418_15757.expected_typ);
       sigtab = uu____15761;
       attrtab = uu____15764;
       instantiate_imp = (uu___418_15757.instantiate_imp);
       effects = (uu___418_15757.effects);
       generalize = (uu___418_15757.generalize);
       letrecs = (uu___418_15757.letrecs);
       top_level = (uu___418_15757.top_level);
       check_uvars = (uu___418_15757.check_uvars);
       use_eq = (uu___418_15757.use_eq);
       use_eq_strict = (uu___418_15757.use_eq_strict);
       is_iface = (uu___418_15757.is_iface);
       admit = (uu___418_15757.admit);
       lax = (uu___418_15757.lax);
       lax_universes = (uu___418_15757.lax_universes);
       phase1 = (uu___418_15757.phase1);
       failhard = (uu___418_15757.failhard);
       nosynth = (uu___418_15757.nosynth);
       uvar_subtyping = (uu___418_15757.uvar_subtyping);
       tc_term = (uu___418_15757.tc_term);
       type_of = (uu___418_15757.type_of);
       universe_of = (uu___418_15757.universe_of);
       check_type_of = (uu___418_15757.check_type_of);
       use_bv_sorts = (uu___418_15757.use_bv_sorts);
       qtbl_name_and_index = uu____15771;
       normalized_eff_names = uu____15871;
       fv_delta_depths = uu____15874;
       proof_ns = (uu___418_15757.proof_ns);
       synth_hook = (uu___418_15757.synth_hook);
       try_solve_implicits_hook = (uu___418_15757.try_solve_implicits_hook);
       splice = (uu___418_15757.splice);
       mpreprocess = (uu___418_15757.mpreprocess);
       postprocess = (uu___418_15757.postprocess);
       identifier_info = uu____15877;
       tc_hooks = (uu___418_15757.tc_hooks);
       dsenv = (uu___418_15757.dsenv);
       nbe = (uu___418_15757.nbe);
       strict_args_tab = uu____15900;
       erasable_types_tab = uu____15913;
       enable_defer_to_tac = (uu___418_15757.enable_defer_to_tac)
     })
let (pop_stack : unit -> env) =
  fun uu____15923 ->
    let uu____15924 = FStar_ST.op_Bang stack in
    match uu____15924 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15978 -> failwith "Impossible: Too many pops"
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push_stack stack env1
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop_stack stack depth
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1 ->
    fun msg ->
      FStar_Util.atomically
        (fun uu____16068 ->
           let uu____16069 = snapshot_stack env1 in
           match uu____16069 with
           | (stack_depth, env2) ->
               let uu____16103 = snapshot_query_indices () in
               (match uu____16103 with
                | (query_indices_depth, ()) ->
                    let uu____16136 = (env2.solver).snapshot msg in
                    (match uu____16136 with
                     | (solver_depth, ()) ->
                         let uu____16193 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv in
                         (match uu____16193 with
                          | (dsenv_depth, dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_16260 = env2 in
                                 {
                                   solver = (uu___443_16260.solver);
                                   range = (uu___443_16260.range);
                                   curmodule = (uu___443_16260.curmodule);
                                   gamma = (uu___443_16260.gamma);
                                   gamma_sig = (uu___443_16260.gamma_sig);
                                   gamma_cache = (uu___443_16260.gamma_cache);
                                   modules = (uu___443_16260.modules);
                                   expected_typ =
                                     (uu___443_16260.expected_typ);
                                   sigtab = (uu___443_16260.sigtab);
                                   attrtab = (uu___443_16260.attrtab);
                                   instantiate_imp =
                                     (uu___443_16260.instantiate_imp);
                                   effects = (uu___443_16260.effects);
                                   generalize = (uu___443_16260.generalize);
                                   letrecs = (uu___443_16260.letrecs);
                                   top_level = (uu___443_16260.top_level);
                                   check_uvars = (uu___443_16260.check_uvars);
                                   use_eq = (uu___443_16260.use_eq);
                                   use_eq_strict =
                                     (uu___443_16260.use_eq_strict);
                                   is_iface = (uu___443_16260.is_iface);
                                   admit = (uu___443_16260.admit);
                                   lax = (uu___443_16260.lax);
                                   lax_universes =
                                     (uu___443_16260.lax_universes);
                                   phase1 = (uu___443_16260.phase1);
                                   failhard = (uu___443_16260.failhard);
                                   nosynth = (uu___443_16260.nosynth);
                                   uvar_subtyping =
                                     (uu___443_16260.uvar_subtyping);
                                   tc_term = (uu___443_16260.tc_term);
                                   type_of = (uu___443_16260.type_of);
                                   universe_of = (uu___443_16260.universe_of);
                                   check_type_of =
                                     (uu___443_16260.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_16260.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_16260.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_16260.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_16260.fv_delta_depths);
                                   proof_ns = (uu___443_16260.proof_ns);
                                   synth_hook = (uu___443_16260.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_16260.try_solve_implicits_hook);
                                   splice = (uu___443_16260.splice);
                                   mpreprocess = (uu___443_16260.mpreprocess);
                                   postprocess = (uu___443_16260.postprocess);
                                   identifier_info =
                                     (uu___443_16260.identifier_info);
                                   tc_hooks = (uu___443_16260.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_16260.nbe);
                                   strict_args_tab =
                                     (uu___443_16260.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_16260.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___443_16260.enable_defer_to_tac)
                                 }))))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
          (fun uu____16294 ->
             let uu____16295 =
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
             match uu____16295 with
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
                             ((let uu____16475 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1 in
                               FStar_Common.runtime_assert uu____16475
                                 "Inconsistent stack state");
                              tcenv))))))
let (push : env -> Prims.string -> env) =
  fun env1 ->
    fun msg ->
      let uu____16491 = snapshot env1 msg in
      FStar_Pervasives_Native.snd uu____16491
let (pop : env -> Prims.string -> env) =
  fun env1 ->
    fun msg -> rollback env1.solver msg FStar_Pervasives_Native.None
let (incr_query_index : env -> env) =
  fun env1 ->
    let qix = peek_query_indices () in
    match env1.qtbl_name_and_index with
    | (uu____16523, FStar_Pervasives_Native.None) -> env1
    | (tbl, FStar_Pervasives_Native.Some (l, n)) ->
        let uu____16565 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16595 ->
                  match uu____16595 with
                  | (m, uu____16603) -> FStar_Ident.lid_equals l m)) in
        (match uu____16565 with
         | FStar_Pervasives_Native.None ->
             let next = n + Prims.int_one in
             (add_query_index (l, next);
              (let uu____16617 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu____16617 next);
              (let uu___488_16620 = env1 in
               {
                 solver = (uu___488_16620.solver);
                 range = (uu___488_16620.range);
                 curmodule = (uu___488_16620.curmodule);
                 gamma = (uu___488_16620.gamma);
                 gamma_sig = (uu___488_16620.gamma_sig);
                 gamma_cache = (uu___488_16620.gamma_cache);
                 modules = (uu___488_16620.modules);
                 expected_typ = (uu___488_16620.expected_typ);
                 sigtab = (uu___488_16620.sigtab);
                 attrtab = (uu___488_16620.attrtab);
                 instantiate_imp = (uu___488_16620.instantiate_imp);
                 effects = (uu___488_16620.effects);
                 generalize = (uu___488_16620.generalize);
                 letrecs = (uu___488_16620.letrecs);
                 top_level = (uu___488_16620.top_level);
                 check_uvars = (uu___488_16620.check_uvars);
                 use_eq = (uu___488_16620.use_eq);
                 use_eq_strict = (uu___488_16620.use_eq_strict);
                 is_iface = (uu___488_16620.is_iface);
                 admit = (uu___488_16620.admit);
                 lax = (uu___488_16620.lax);
                 lax_universes = (uu___488_16620.lax_universes);
                 phase1 = (uu___488_16620.phase1);
                 failhard = (uu___488_16620.failhard);
                 nosynth = (uu___488_16620.nosynth);
                 uvar_subtyping = (uu___488_16620.uvar_subtyping);
                 tc_term = (uu___488_16620.tc_term);
                 type_of = (uu___488_16620.type_of);
                 universe_of = (uu___488_16620.universe_of);
                 check_type_of = (uu___488_16620.check_type_of);
                 use_bv_sorts = (uu___488_16620.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16620.normalized_eff_names);
                 fv_delta_depths = (uu___488_16620.fv_delta_depths);
                 proof_ns = (uu___488_16620.proof_ns);
                 synth_hook = (uu___488_16620.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16620.try_solve_implicits_hook);
                 splice = (uu___488_16620.splice);
                 mpreprocess = (uu___488_16620.mpreprocess);
                 postprocess = (uu___488_16620.postprocess);
                 identifier_info = (uu___488_16620.identifier_info);
                 tc_hooks = (uu___488_16620.tc_hooks);
                 dsenv = (uu___488_16620.dsenv);
                 nbe = (uu___488_16620.nbe);
                 strict_args_tab = (uu___488_16620.strict_args_tab);
                 erasable_types_tab = (uu___488_16620.erasable_types_tab);
                 enable_defer_to_tac = (uu___488_16620.enable_defer_to_tac)
               }))
         | FStar_Pervasives_Native.Some (uu____16637, m) ->
             let next = m + Prims.int_one in
             (add_query_index (l, next);
              (let uu____16652 = FStar_Ident.string_of_lid l in
               FStar_Util.smap_add tbl uu____16652 next);
              (let uu___497_16655 = env1 in
               {
                 solver = (uu___497_16655.solver);
                 range = (uu___497_16655.range);
                 curmodule = (uu___497_16655.curmodule);
                 gamma = (uu___497_16655.gamma);
                 gamma_sig = (uu___497_16655.gamma_sig);
                 gamma_cache = (uu___497_16655.gamma_cache);
                 modules = (uu___497_16655.modules);
                 expected_typ = (uu___497_16655.expected_typ);
                 sigtab = (uu___497_16655.sigtab);
                 attrtab = (uu___497_16655.attrtab);
                 instantiate_imp = (uu___497_16655.instantiate_imp);
                 effects = (uu___497_16655.effects);
                 generalize = (uu___497_16655.generalize);
                 letrecs = (uu___497_16655.letrecs);
                 top_level = (uu___497_16655.top_level);
                 check_uvars = (uu___497_16655.check_uvars);
                 use_eq = (uu___497_16655.use_eq);
                 use_eq_strict = (uu___497_16655.use_eq_strict);
                 is_iface = (uu___497_16655.is_iface);
                 admit = (uu___497_16655.admit);
                 lax = (uu___497_16655.lax);
                 lax_universes = (uu___497_16655.lax_universes);
                 phase1 = (uu___497_16655.phase1);
                 failhard = (uu___497_16655.failhard);
                 nosynth = (uu___497_16655.nosynth);
                 uvar_subtyping = (uu___497_16655.uvar_subtyping);
                 tc_term = (uu___497_16655.tc_term);
                 type_of = (uu___497_16655.type_of);
                 universe_of = (uu___497_16655.universe_of);
                 check_type_of = (uu___497_16655.check_type_of);
                 use_bv_sorts = (uu___497_16655.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16655.normalized_eff_names);
                 fv_delta_depths = (uu___497_16655.fv_delta_depths);
                 proof_ns = (uu___497_16655.proof_ns);
                 synth_hook = (uu___497_16655.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16655.try_solve_implicits_hook);
                 splice = (uu___497_16655.splice);
                 mpreprocess = (uu___497_16655.mpreprocess);
                 postprocess = (uu___497_16655.postprocess);
                 identifier_info = (uu___497_16655.identifier_info);
                 tc_hooks = (uu___497_16655.tc_hooks);
                 dsenv = (uu___497_16655.dsenv);
                 nbe = (uu___497_16655.nbe);
                 strict_args_tab = (uu___497_16655.strict_args_tab);
                 erasable_types_tab = (uu___497_16655.erasable_types_tab);
                 enable_defer_to_tac = (uu___497_16655.enable_defer_to_tac)
               })))
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____16684 = FStar_Ident.string_of_lid env1.curmodule in
      FStar_Options.debug_at_level uu____16684 l
let (set_range : env -> FStar_Range.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___504_16700 = e in
         {
           solver = (uu___504_16700.solver);
           range = r;
           curmodule = (uu___504_16700.curmodule);
           gamma = (uu___504_16700.gamma);
           gamma_sig = (uu___504_16700.gamma_sig);
           gamma_cache = (uu___504_16700.gamma_cache);
           modules = (uu___504_16700.modules);
           expected_typ = (uu___504_16700.expected_typ);
           sigtab = (uu___504_16700.sigtab);
           attrtab = (uu___504_16700.attrtab);
           instantiate_imp = (uu___504_16700.instantiate_imp);
           effects = (uu___504_16700.effects);
           generalize = (uu___504_16700.generalize);
           letrecs = (uu___504_16700.letrecs);
           top_level = (uu___504_16700.top_level);
           check_uvars = (uu___504_16700.check_uvars);
           use_eq = (uu___504_16700.use_eq);
           use_eq_strict = (uu___504_16700.use_eq_strict);
           is_iface = (uu___504_16700.is_iface);
           admit = (uu___504_16700.admit);
           lax = (uu___504_16700.lax);
           lax_universes = (uu___504_16700.lax_universes);
           phase1 = (uu___504_16700.phase1);
           failhard = (uu___504_16700.failhard);
           nosynth = (uu___504_16700.nosynth);
           uvar_subtyping = (uu___504_16700.uvar_subtyping);
           tc_term = (uu___504_16700.tc_term);
           type_of = (uu___504_16700.type_of);
           universe_of = (uu___504_16700.universe_of);
           check_type_of = (uu___504_16700.check_type_of);
           use_bv_sorts = (uu___504_16700.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16700.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16700.normalized_eff_names);
           fv_delta_depths = (uu___504_16700.fv_delta_depths);
           proof_ns = (uu___504_16700.proof_ns);
           synth_hook = (uu___504_16700.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16700.try_solve_implicits_hook);
           splice = (uu___504_16700.splice);
           mpreprocess = (uu___504_16700.mpreprocess);
           postprocess = (uu___504_16700.postprocess);
           identifier_info = (uu___504_16700.identifier_info);
           tc_hooks = (uu___504_16700.tc_hooks);
           dsenv = (uu___504_16700.dsenv);
           nbe = (uu___504_16700.nbe);
           strict_args_tab = (uu___504_16700.strict_args_tab);
           erasable_types_tab = (uu___504_16700.erasable_types_tab);
           enable_defer_to_tac = (uu___504_16700.enable_defer_to_tac)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1 ->
    fun enabled ->
      let uu____16720 =
        let uu____16721 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____16721 enabled in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16720
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun bv ->
      fun ty ->
        let uu____16776 =
          let uu____16777 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16777 bv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16776
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1 ->
    fun fv ->
      fun ty ->
        let uu____16832 =
          let uu____16833 = FStar_ST.op_Bang env1.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16833 fv ty in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16832
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1 ->
    fun ty_map ->
      let uu____16888 =
        let uu____16889 = FStar_ST.op_Bang env1.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____16889 ty_map in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16888
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1 -> env1.modules
let (current_module : env -> FStar_Ident.lident) = fun env1 -> env1.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun lid ->
      let uu___521_16953 = env1 in
      {
        solver = (uu___521_16953.solver);
        range = (uu___521_16953.range);
        curmodule = lid;
        gamma = (uu___521_16953.gamma);
        gamma_sig = (uu___521_16953.gamma_sig);
        gamma_cache = (uu___521_16953.gamma_cache);
        modules = (uu___521_16953.modules);
        expected_typ = (uu___521_16953.expected_typ);
        sigtab = (uu___521_16953.sigtab);
        attrtab = (uu___521_16953.attrtab);
        instantiate_imp = (uu___521_16953.instantiate_imp);
        effects = (uu___521_16953.effects);
        generalize = (uu___521_16953.generalize);
        letrecs = (uu___521_16953.letrecs);
        top_level = (uu___521_16953.top_level);
        check_uvars = (uu___521_16953.check_uvars);
        use_eq = (uu___521_16953.use_eq);
        use_eq_strict = (uu___521_16953.use_eq_strict);
        is_iface = (uu___521_16953.is_iface);
        admit = (uu___521_16953.admit);
        lax = (uu___521_16953.lax);
        lax_universes = (uu___521_16953.lax_universes);
        phase1 = (uu___521_16953.phase1);
        failhard = (uu___521_16953.failhard);
        nosynth = (uu___521_16953.nosynth);
        uvar_subtyping = (uu___521_16953.uvar_subtyping);
        tc_term = (uu___521_16953.tc_term);
        type_of = (uu___521_16953.type_of);
        universe_of = (uu___521_16953.universe_of);
        check_type_of = (uu___521_16953.check_type_of);
        use_bv_sorts = (uu___521_16953.use_bv_sorts);
        qtbl_name_and_index = (uu___521_16953.qtbl_name_and_index);
        normalized_eff_names = (uu___521_16953.normalized_eff_names);
        fv_delta_depths = (uu___521_16953.fv_delta_depths);
        proof_ns = (uu___521_16953.proof_ns);
        synth_hook = (uu___521_16953.synth_hook);
        try_solve_implicits_hook = (uu___521_16953.try_solve_implicits_hook);
        splice = (uu___521_16953.splice);
        mpreprocess = (uu___521_16953.mpreprocess);
        postprocess = (uu___521_16953.postprocess);
        identifier_info = (uu___521_16953.identifier_info);
        tc_hooks = (uu___521_16953.tc_hooks);
        dsenv = (uu___521_16953.dsenv);
        nbe = (uu___521_16953.nbe);
        strict_args_tab = (uu___521_16953.strict_args_tab);
        erasable_types_tab = (uu___521_16953.erasable_types_tab);
        enable_defer_to_tac = (uu___521_16953.enable_defer_to_tac)
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
      let uu____16984 = FStar_Ident.string_of_lid lid in
      FStar_Util.smap_try_find (sigtab env1) uu____16984
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu____16997 =
      let uu____16999 = FStar_Ident.string_of_lid l in
      FStar_Util.format1 "Name \"%s\" not found" uu____16999 in
    (FStar_Errors.Fatal_NameNotFound, uu____16997)
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v ->
    let uu____17014 =
      let uu____17016 = FStar_Syntax_Print.bv_to_string v in
      FStar_Util.format1 "Variable \"%s\" not found" uu____17016 in
    (FStar_Errors.Fatal_VariableNotFound, uu____17014)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____17025 ->
    let uu____17026 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
    FStar_Syntax_Syntax.U_unif uu____17026
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
      | ((formals, t), uu____17128) ->
          let vs = mk_univ_subst formals us in
          let uu____17152 = FStar_Syntax_Subst.subst vs t in
          (us, uu____17152)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17169 ->
    match uu___1_17169 with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17195 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r ->
    fun t ->
      let uu____17215 = inst_tscheme t in
      match uu____17215 with
      | (us, t1) ->
          let uu____17226 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____17226)
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
          let uu____17251 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu____17253 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17251 uu____17253 in
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
        fun uu____17280 ->
          match uu____17280 with
          | (us, t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17294 =
                    let uu____17296 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us) in
                    let uu____17300 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts) in
                    let uu____17304 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname in
                    let uu____17306 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17296 uu____17300 uu____17304 uu____17306 in
                  failwith uu____17294)
               else ();
               (let uu____17311 = inst_tscheme_with (us, t) insts in
                FStar_Pervasives_Native.snd uu____17311))
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu____17329 -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____17340 -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____17351 -> false
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1 ->
    fun l ->
      let cur = current_module env1 in
      let uu____17365 =
        let uu____17367 = FStar_Ident.nsstr l in
        let uu____17369 = FStar_Ident.string_of_lid cur in
        uu____17367 = uu____17369 in
      if uu____17365
      then Yes
      else
        (let uu____17375 =
           let uu____17377 = FStar_Ident.nsstr l in
           let uu____17379 = FStar_Ident.string_of_lid cur in
           FStar_Util.starts_with uu____17377 uu____17379 in
         if uu____17375
         then
           let lns =
             let uu____17385 = FStar_Ident.ns_of_lid l in
             let uu____17388 =
               let uu____17391 = FStar_Ident.ident_of_lid l in [uu____17391] in
             FStar_List.append uu____17385 uu____17388 in
           let cur1 =
             let uu____17395 = FStar_Ident.ns_of_lid cur in
             let uu____17398 =
               let uu____17401 = FStar_Ident.ident_of_lid cur in
               [uu____17401] in
             FStar_List.append uu____17395 uu____17398 in
           let rec aux c l1 =
             match (c, l1) with
             | ([], uu____17425) -> Maybe
             | (uu____17432, []) -> No
             | (hd::tl, hd'::tl') when
                 let uu____17451 = FStar_Ident.string_of_id hd in
                 let uu____17453 = FStar_Ident.string_of_id hd' in
                 uu____17451 = uu____17453 -> aux tl tl'
             | uu____17456 -> No in
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
        (let uu____17508 = FStar_Ident.string_of_lid lid in
         FStar_Util.smap_add (gamma_cache env1) uu____17508 t);
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____17552 =
            let uu____17555 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17555 in
          match uu____17552 with
          | FStar_Pervasives_Native.None ->
              let uu____17577 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17621 ->
                     match uu___2_17621 with
                     | FStar_Syntax_Syntax.Binding_lid (l, t) ->
                         let uu____17660 = FStar_Ident.lid_equals lid l in
                         if uu____17660
                         then
                           let uu____17683 =
                             let uu____17702 =
                               let uu____17717 = inst_tscheme t in
                               FStar_Util.Inl uu____17717 in
                             let uu____17732 = FStar_Ident.range_of_lid l in
                             (uu____17702, uu____17732) in
                           FStar_Pervasives_Native.Some uu____17683
                         else FStar_Pervasives_Native.None
                     | uu____17785 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu____17577
                (fun uu____17823 ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17833 ->
                        match uu___3_17833 with
                        | (uu____17836,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               (ses, uu____17838);
                             FStar_Syntax_Syntax.sigrng = uu____17839;
                             FStar_Syntax_Syntax.sigquals = uu____17840;
                             FStar_Syntax_Syntax.sigmeta = uu____17841;
                             FStar_Syntax_Syntax.sigattrs = uu____17842;
                             FStar_Syntax_Syntax.sigopts = uu____17843;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu____17865 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu____17865
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
                                  uu____17917 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17924 -> cache t in
                            let uu____17925 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
                            (match uu____17925 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17931 =
                                   let uu____17932 =
                                     FStar_Ident.range_of_lid l in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17932) in
                                 maybe_cache uu____17931)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____18003 = find_in_sigtab env1 lid in
         match uu____18003 with
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
      let uu____18084 = lookup_qname env1 lid in
      match uu____18084 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____18105, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1 ->
    fun attr ->
      let uu____18219 = FStar_Util.smap_try_find (attrtab env1) attr in
      match uu____18219 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      let add_one env2 se1 attr =
        let uu____18264 =
          let uu____18267 = lookup_attr env2 attr in se1 :: uu____18267 in
        FStar_Util.smap_add (attrtab env2) attr uu____18264 in
      FStar_List.iter
        (fun attr ->
           let uu____18277 =
             let uu____18278 = FStar_Syntax_Subst.compress attr in
             uu____18278.FStar_Syntax_Syntax.n in
           match uu____18277 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18282 =
                 let uu____18284 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_Ident.string_of_lid uu____18284 in
               add_one env1 se uu____18282
           | uu____18285 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1 ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____18308) ->
          add_sigelts env1 ses
      | uu____18317 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l ->
                let uu____18325 = FStar_Ident.string_of_lid l in
                FStar_Util.smap_add (sigtab env1) uu____18325 se) lids;
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
        (fun uu___4_18359 ->
           match uu___4_18359 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____18369 =
                 let uu____18376 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname in
                 ((id.FStar_Syntax_Syntax.sort), uu____18376) in
               FStar_Pervasives_Native.Some uu____18369
           | uu____18385 -> FStar_Pervasives_Native.None)
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18447, lb::[]), uu____18449) ->
            let uu____18458 =
              let uu____18467 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____18476 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____18467, uu____18476) in
            FStar_Pervasives_Native.Some uu____18458
        | FStar_Syntax_Syntax.Sig_let ((uu____18489, lbs), uu____18491) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18523 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18536 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____18536
                     then
                       let uu____18549 =
                         let uu____18558 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____18567 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____18558, uu____18567) in
                       FStar_Pervasives_Native.Some uu____18549
                     else FStar_Pervasives_Native.None)
        | uu____18590 -> FStar_Pervasives_Native.None
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
                    let uu____18682 =
                      let uu____18684 =
                        let uu____18686 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname in
                        let uu____18688 =
                          let uu____18690 =
                            let uu____18692 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature)) in
                            let uu____18698 =
                              let uu____18700 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us) in
                              Prims.op_Hat ", got " uu____18700 in
                            Prims.op_Hat uu____18692 uu____18698 in
                          Prims.op_Hat ", expected " uu____18690 in
                        Prims.op_Hat uu____18686 uu____18688 in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18684 in
                    failwith uu____18682
                  else ());
             (let uu____18707 =
                let uu____18716 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature in
                (uu____18716, (se.FStar_Syntax_Syntax.sigrng)) in
              FStar_Pervasives_Native.Some uu____18707))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid, us, binders, uu____18736, uu____18737) ->
            let uu____18742 =
              let uu____18751 =
                let uu____18756 =
                  let uu____18757 =
                    let uu____18760 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                    FStar_Syntax_Util.arrow binders uu____18760 in
                  (us, uu____18757) in
                inst_ts us_opt uu____18756 in
              (uu____18751, (se.FStar_Syntax_Syntax.sigrng)) in
            FStar_Pervasives_Native.Some uu____18742
        | uu____18779 -> FStar_Pervasives_Native.None
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
        let mapper uu____18868 =
          match uu____18868 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18964, uvs, t, uu____18967, uu____18968,
                         uu____18969);
                      FStar_Syntax_Syntax.sigrng = uu____18970;
                      FStar_Syntax_Syntax.sigquals = uu____18971;
                      FStar_Syntax_Syntax.sigmeta = uu____18972;
                      FStar_Syntax_Syntax.sigattrs = uu____18973;
                      FStar_Syntax_Syntax.sigopts = uu____18974;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____18999 =
                     let uu____19008 = inst_tscheme1 (uvs, t) in
                     (uu____19008, rng) in
                   FStar_Pervasives_Native.Some uu____18999
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____19032;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____19034;
                      FStar_Syntax_Syntax.sigattrs = uu____19035;
                      FStar_Syntax_Syntax.sigopts = uu____19036;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____19055 =
                     let uu____19057 = in_cur_mod env1 l in uu____19057 = Yes in
                   if uu____19055
                   then
                     let uu____19069 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface in
                     (if uu____19069
                      then
                        let uu____19085 =
                          let uu____19094 = inst_tscheme1 (uvs, t) in
                          (uu____19094, rng) in
                        FStar_Pervasives_Native.Some uu____19085
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____19127 =
                        let uu____19136 = inst_tscheme1 (uvs, t) in
                        (uu____19136, rng) in
                      FStar_Pervasives_Native.Some uu____19127)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____19161, uu____19162);
                      FStar_Syntax_Syntax.sigrng = uu____19163;
                      FStar_Syntax_Syntax.sigquals = uu____19164;
                      FStar_Syntax_Syntax.sigmeta = uu____19165;
                      FStar_Syntax_Syntax.sigattrs = uu____19166;
                      FStar_Syntax_Syntax.sigopts = uu____19167;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19210 =
                          let uu____19219 = inst_tscheme1 (uvs, k) in
                          (uu____19219, rng) in
                        FStar_Pervasives_Native.Some uu____19210
                    | uu____19240 ->
                        let uu____19241 =
                          let uu____19250 =
                            let uu____19255 =
                              let uu____19256 =
                                let uu____19259 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____19259 in
                              (uvs, uu____19256) in
                            inst_tscheme1 uu____19255 in
                          (uu____19250, rng) in
                        FStar_Pervasives_Native.Some uu____19241)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____19282, uu____19283);
                      FStar_Syntax_Syntax.sigrng = uu____19284;
                      FStar_Syntax_Syntax.sigquals = uu____19285;
                      FStar_Syntax_Syntax.sigmeta = uu____19286;
                      FStar_Syntax_Syntax.sigattrs = uu____19287;
                      FStar_Syntax_Syntax.sigopts = uu____19288;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19332 =
                          let uu____19341 = inst_tscheme_with (uvs, k) us in
                          (uu____19341, rng) in
                        FStar_Pervasives_Native.Some uu____19332
                    | uu____19362 ->
                        let uu____19363 =
                          let uu____19372 =
                            let uu____19377 =
                              let uu____19378 =
                                let uu____19381 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____19381 in
                              (uvs, uu____19378) in
                            inst_tscheme_with uu____19377 us in
                          (uu____19372, rng) in
                        FStar_Pervasives_Native.Some uu____19363)
               | FStar_Util.Inr se ->
                   let uu____19417 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19438;
                          FStar_Syntax_Syntax.sigrng = uu____19439;
                          FStar_Syntax_Syntax.sigquals = uu____19440;
                          FStar_Syntax_Syntax.sigmeta = uu____19441;
                          FStar_Syntax_Syntax.sigattrs = uu____19442;
                          FStar_Syntax_Syntax.sigopts = uu____19443;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19460 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range in
                   FStar_All.pipe_right uu____19417
                     (FStar_Util.map_option
                        (fun uu____19508 ->
                           match uu____19508 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____19539 =
          let uu____19550 = lookup_qname env1 lid in
          FStar_Util.bind_opt uu____19550 mapper in
        match uu____19539 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____19624 =
              let uu____19635 =
                let uu____19642 =
                  let uu___858_19645 = t in
                  let uu____19646 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19645.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19646;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19645.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____19642) in
              (uu____19635, r) in
            FStar_Pervasives_Native.Some uu____19624
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____19695 = lookup_qname env1 l in
      match uu____19695 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____19716 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1 ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____19770 = try_lookup_bv env1 bv in
      match uu____19770 with
      | FStar_Pervasives_Native.None ->
          let uu____19785 = variable_not_found bv in
          FStar_Errors.raise_error uu____19785 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____19801 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____19802 =
            let uu____19803 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____19803 in
          (uu____19801, uu____19802)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____19825 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l in
      match uu____19825 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____19891 = FStar_Range.use_range use_range in
            FStar_Range.set_use_range r uu____19891 in
          let uu____19892 =
            let uu____19901 =
              let uu____19906 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____19906) in
            (uu____19901, r1) in
          FStar_Pervasives_Native.Some uu____19892
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
        let uu____19941 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l in
        match uu____19941 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19974, t), r) ->
            let use_range = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____19999 = FStar_Range.use_range use_range in
              FStar_Range.set_use_range r uu____19999 in
            let uu____20000 =
              let uu____20005 = FStar_Syntax_Subst.set_use_range use_range t in
              (uu____20005, r1) in
            FStar_Pervasives_Native.Some uu____20000
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1 ->
    fun l ->
      let uu____20029 = try_lookup_lid env1 l in
      match uu____20029 with
      | FStar_Pervasives_Native.None ->
          let uu____20056 = name_not_found l in
          let uu____20062 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____20056 uu____20062
      | FStar_Pervasives_Native.Some v -> v
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1 ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_20107 ->
              match uu___5_20107 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____20110 = FStar_Ident.string_of_id x in
                  let uu____20112 = FStar_Ident.string_of_id y in
                  uu____20110 = uu____20112
              | uu____20115 -> false) env1.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____20136 = lookup_qname env1 lid in
      match uu____20136 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20145, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____20148;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20150;
              FStar_Syntax_Syntax.sigattrs = uu____20151;
              FStar_Syntax_Syntax.sigopts = uu____20152;_},
            FStar_Pervasives_Native.None),
           uu____20153)
          ->
          let uu____20204 =
            let uu____20211 =
              let uu____20212 =
                let uu____20215 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____20215 t in
              (uvs, uu____20212) in
            (uu____20211, q) in
          FStar_Pervasives_Native.Some uu____20204
      | uu____20228 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____20250 = lookup_qname env1 lid in
      match uu____20250 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20255, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____20258;
              FStar_Syntax_Syntax.sigquals = uu____20259;
              FStar_Syntax_Syntax.sigmeta = uu____20260;
              FStar_Syntax_Syntax.sigattrs = uu____20261;
              FStar_Syntax_Syntax.sigopts = uu____20262;_},
            FStar_Pervasives_Native.None),
           uu____20263)
          ->
          let uu____20314 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____20314 (uvs, t)
      | uu____20319 ->
          let uu____20320 = name_not_found lid in
          let uu____20326 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____20320 uu____20326
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1 ->
    fun lid ->
      let uu____20346 = lookup_qname env1 lid in
      match uu____20346 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20351, uvs, t, uu____20354, uu____20355, uu____20356);
              FStar_Syntax_Syntax.sigrng = uu____20357;
              FStar_Syntax_Syntax.sigquals = uu____20358;
              FStar_Syntax_Syntax.sigmeta = uu____20359;
              FStar_Syntax_Syntax.sigattrs = uu____20360;
              FStar_Syntax_Syntax.sigopts = uu____20361;_},
            FStar_Pervasives_Native.None),
           uu____20362)
          ->
          let uu____20419 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____20419 (uvs, t)
      | uu____20424 ->
          let uu____20425 = name_not_found lid in
          let uu____20431 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____20425 uu____20431
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1 ->
    fun lid ->
      let uu____20454 = lookup_qname env1 lid in
      match uu____20454 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20462, uu____20463, uu____20464, uu____20465,
                 uu____20466, dcs);
              FStar_Syntax_Syntax.sigrng = uu____20468;
              FStar_Syntax_Syntax.sigquals = uu____20469;
              FStar_Syntax_Syntax.sigmeta = uu____20470;
              FStar_Syntax_Syntax.sigattrs = uu____20471;
              FStar_Syntax_Syntax.sigopts = uu____20472;_},
            uu____20473),
           uu____20474)
          -> (true, dcs)
      | uu____20539 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu____20555 = lookup_qname env1 lid in
      match uu____20555 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20556, uu____20557, uu____20558, l, uu____20560,
                 uu____20561);
              FStar_Syntax_Syntax.sigrng = uu____20562;
              FStar_Syntax_Syntax.sigquals = uu____20563;
              FStar_Syntax_Syntax.sigmeta = uu____20564;
              FStar_Syntax_Syntax.sigattrs = uu____20565;
              FStar_Syntax_Syntax.sigopts = uu____20566;_},
            uu____20567),
           uu____20568)
          -> l
      | uu____20627 ->
          let uu____20628 =
            let uu____20630 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____20630 in
          failwith uu____20628
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
               uu____20700)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu____20757)
                   when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        let uu____20781 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid in
                        if uu____20781
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20816 -> FStar_Pervasives_Native.None)
          | uu____20825 -> FStar_Pervasives_Native.None
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
        let uu____20887 = lookup_qname env1 lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20887
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
        let uu____20920 = lookup_qname env1 lid in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20920
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv ->
    fun qn ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____20944 =
        let uu____20946 = FStar_Ident.nsstr lid in uu____20946 = "Prims" in
      if uu____20944
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20976, uu____20977) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se, uu____21026), uu____21027) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____21076 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____21094 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____21104 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____21121 ->
                  let uu____21128 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals in
                  FStar_Pervasives_Native.Some uu____21128
              | FStar_Syntax_Syntax.Sig_let ((uu____21129, lbs), uu____21131)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       let uu____21147 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid in
                       if uu____21147
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____21154 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____21170 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____21180 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____21187 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____21188 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21189 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____21202 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____21203 ->
                  FStar_Pervasives_Native.None))
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1 ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____21226 =
        let uu____21228 = FStar_Ident.nsstr lid in uu____21228 = "Prims" in
      if uu____21226
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21235 =
           let uu____21238 = FStar_Ident.string_of_lid lid in
           FStar_All.pipe_right uu____21238
             (FStar_Util.smap_try_find env1.fv_delta_depths) in
         FStar_All.pipe_right uu____21235
           (fun d_opt ->
              let uu____21250 = FStar_All.pipe_right d_opt FStar_Util.is_some in
              if uu____21250
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21260 =
                   let uu____21263 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   delta_depth_of_qninfo fv uu____21263 in
                 match uu____21260 with
                 | FStar_Pervasives_Native.None ->
                     let uu____21264 =
                       let uu____21266 = FStar_Syntax_Print.fv_to_string fv in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21266 in
                     failwith uu____21264
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21271 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ()) in
                       if uu____21271
                       then
                         let uu____21274 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____21276 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta in
                         let uu____21278 =
                           FStar_Syntax_Print.delta_depth_to_string d in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21274 uu____21276 uu____21278
                       else ());
                      (let uu____21284 = FStar_Ident.string_of_lid lid in
                       FStar_Util.smap_add env1.fv_delta_depths uu____21284 d);
                      d))))
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____21305), uu____21306) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21355 -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____21377), uu____21378) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21427 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let uu____21449 = lookup_qname env1 lid in
      FStar_All.pipe_left attrs_of_qninfo uu____21449
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____21482 = lookup_attrs_of_lid env1 fv_lid in
        match uu____21482 with
        | FStar_Pervasives_Native.None -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21504 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm ->
                      let uu____21513 =
                        let uu____21514 = FStar_Syntax_Util.un_uinst tm in
                        uu____21514.FStar_Syntax_Syntax.n in
                      match uu____21513 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21519 -> false)) in
            (true, uu____21504)
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1 ->
    fun fv_lid ->
      fun attr_lid ->
        let uu____21542 = fv_exists_and_has_attr env1 fv_lid attr_lid in
        FStar_Pervasives_Native.snd uu____21542
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
          let uu____21614 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____21614 in
        let uu____21615 = FStar_Util.smap_try_find tab s in
        match uu____21615 with
        | FStar_Pervasives_Native.None ->
            let uu____21618 = f () in
            (match uu____21618 with
             | (should_cache, res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1 ->
    fun fv ->
      let f uu____21656 =
        let uu____21657 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr in
        match uu____21657 with | (ex, erasable) -> (ex, erasable) in
      cache_in_fv_tab env1.erasable_types_tab fv f
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____21691 =
        let uu____21692 = FStar_Syntax_Util.unrefine t in
        uu____21692.FStar_Syntax_Syntax.n in
      match uu____21691 with
      | FStar_Syntax_Syntax.Tm_type uu____21696 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head, uu____21700) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu____21726) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21731, c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21753 -> false
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fv ->
      let f uu____21786 =
        let attrs =
          let uu____21792 = FStar_Syntax_Syntax.lid_of_fv fv in
          lookup_attrs_of_lid env1 uu____21792 in
        match attrs with
        | FStar_Pervasives_Native.None ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x ->
                   let uu____21832 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr in
                   FStar_Pervasives_Native.fst uu____21832) in
            (true, res) in
      cache_in_fv_tab env1.strict_args_tab fv f
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ftv ->
      let uu____21877 = lookup_qname env1 ftv in
      match uu____21877 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____21881) ->
          let uu____21926 =
            effect_signature FStar_Pervasives_Native.None se env1.range in
          (match uu____21926 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21947, t), r) ->
               let uu____21962 =
                 let uu____21963 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____21963 t in
               FStar_Pervasives_Native.Some uu____21962)
      | uu____21964 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun ftv ->
      let uu____21976 = try_lookup_effect_lid env1 ftv in
      match uu____21976 with
      | FStar_Pervasives_Native.None ->
          let uu____21979 = name_not_found ftv in
          let uu____21985 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____21979 uu____21985
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
        let uu____22009 = lookup_qname env1 lid0 in
        match uu____22009 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs, binders, c, uu____22020);
                FStar_Syntax_Syntax.sigrng = uu____22021;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____22023;
                FStar_Syntax_Syntax.sigattrs = uu____22024;
                FStar_Syntax_Syntax.sigopts = uu____22025;_},
              FStar_Pervasives_Native.None),
             uu____22026)
            ->
            let lid1 =
              let uu____22082 =
                let uu____22083 = FStar_Ident.range_of_lid lid in
                let uu____22084 =
                  let uu____22085 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____22085 in
                FStar_Range.set_use_range uu____22083 uu____22084 in
              FStar_Ident.set_lid_range lid uu____22082 in
            let uu____22086 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_22092 ->
                      match uu___6_22092 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____22095 -> false)) in
            if uu____22086
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____22114 =
                      let uu____22116 =
                        let uu____22118 = get_range env1 in
                        FStar_Range.string_of_range uu____22118 in
                      let uu____22119 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____22121 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____22116 uu____22119 uu____22121 in
                    failwith uu____22114) in
               match (binders, univs) with
               | ([], uu____22142) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____22168, uu____22169::uu____22170::uu____22171) ->
                   let uu____22192 =
                     let uu____22194 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____22196 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____22194 uu____22196 in
                   failwith uu____22192
               | uu____22207 ->
                   let uu____22222 =
                     let uu____22227 =
                       let uu____22228 = FStar_Syntax_Util.arrow binders c in
                       (univs, uu____22228) in
                     inst_tscheme_with uu____22227 insts in
                   (match uu____22222 with
                    | (uu____22241, t) ->
                        let t1 =
                          let uu____22244 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____22244 t in
                        let uu____22245 =
                          let uu____22246 = FStar_Syntax_Subst.compress t1 in
                          uu____22246.FStar_Syntax_Syntax.n in
                        (match uu____22245 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22281 -> failwith "Impossible")))
        | uu____22289 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun l ->
      let rec find l1 =
        let uu____22313 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____22313 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22326, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____22333 = find l2 in
            (match uu____22333 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____22340 =
          let uu____22343 = FStar_Ident.string_of_lid l in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____22343 in
        match uu____22340 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____22346 = find l in
            (match uu____22346 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____22351 = FStar_Ident.string_of_lid l in
                   FStar_Util.smap_add env1.normalized_eff_names uu____22351
                     m);
                  m)) in
      let uu____22353 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____22353
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1 ->
    fun name ->
      fun r ->
        let sig_t =
          let uu____22374 =
            FStar_All.pipe_right name (lookup_effect_lid env1) in
          FStar_All.pipe_right uu____22374 FStar_Syntax_Subst.compress in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs, uu____22380) ->
            FStar_List.length bs
        | uu____22419 ->
            let uu____22420 =
              let uu____22426 =
                let uu____22428 = FStar_Ident.string_of_lid name in
                let uu____22430 = FStar_Syntax_Print.term_to_string sig_t in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22428 uu____22430 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22426) in
            FStar_Errors.raise_error uu____22420 r
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1 ->
    fun l ->
      let l1 = norm_eff_name env1 l in
      let uu____22449 = lookup_qname env1 l1 in
      match uu____22449 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22452;
              FStar_Syntax_Syntax.sigrng = uu____22453;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22455;
              FStar_Syntax_Syntax.sigattrs = uu____22456;
              FStar_Syntax_Syntax.sigopts = uu____22457;_},
            uu____22458),
           uu____22459)
          -> q
      | uu____22512 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      fun i ->
        let fail uu____22536 =
          let uu____22537 =
            let uu____22539 = FStar_Util.string_of_int i in
            let uu____22541 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22539 uu____22541 in
          failwith uu____22537 in
        let uu____22544 = lookup_datacon env1 lid in
        match uu____22544 with
        | (uu____22549, t) ->
            let uu____22551 =
              let uu____22552 = FStar_Syntax_Subst.compress t in
              uu____22552.FStar_Syntax_Syntax.n in
            (match uu____22551 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____22556) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22602 -> fail ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____22616 = lookup_qname env1 l in
      match uu____22616 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22618, uu____22619, uu____22620);
              FStar_Syntax_Syntax.sigrng = uu____22621;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22623;
              FStar_Syntax_Syntax.sigattrs = uu____22624;
              FStar_Syntax_Syntax.sigopts = uu____22625;_},
            uu____22626),
           uu____22627)
          ->
          FStar_Util.for_some
            (fun uu___7_22682 ->
               match uu___7_22682 with
               | FStar_Syntax_Syntax.Projector uu____22684 -> true
               | uu____22690 -> false) quals
      | uu____22692 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____22706 = lookup_qname env1 lid in
      match uu____22706 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22708, uu____22709, uu____22710, uu____22711,
                 uu____22712, uu____22713);
              FStar_Syntax_Syntax.sigrng = uu____22714;
              FStar_Syntax_Syntax.sigquals = uu____22715;
              FStar_Syntax_Syntax.sigmeta = uu____22716;
              FStar_Syntax_Syntax.sigattrs = uu____22717;
              FStar_Syntax_Syntax.sigopts = uu____22718;_},
            uu____22719),
           uu____22720)
          -> true
      | uu____22780 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____22794 = lookup_qname env1 lid in
      match uu____22794 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22796, uu____22797, uu____22798, uu____22799,
                 uu____22800, uu____22801);
              FStar_Syntax_Syntax.sigrng = uu____22802;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22804;
              FStar_Syntax_Syntax.sigattrs = uu____22805;
              FStar_Syntax_Syntax.sigopts = uu____22806;_},
            uu____22807),
           uu____22808)
          ->
          FStar_Util.for_some
            (fun uu___8_22871 ->
               match uu___8_22871 with
               | FStar_Syntax_Syntax.RecordType uu____22873 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22883 -> true
               | uu____22893 -> false) quals
      | uu____22895 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1 ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22905, uu____22906);
            FStar_Syntax_Syntax.sigrng = uu____22907;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22909;
            FStar_Syntax_Syntax.sigattrs = uu____22910;
            FStar_Syntax_Syntax.sigopts = uu____22911;_},
          uu____22912),
         uu____22913)
        ->
        FStar_Util.for_some
          (fun uu___9_22972 ->
             match uu___9_22972 with
             | FStar_Syntax_Syntax.Action uu____22974 -> true
             | uu____22976 -> false) quals
    | uu____22978 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____22992 = lookup_qname env1 lid in
      FStar_All.pipe_left qninfo_is_action uu____22992
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
      let uu____23009 =
        let uu____23010 = FStar_Syntax_Util.un_uinst head in
        uu____23010.FStar_Syntax_Syntax.n in
      match uu____23009 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____23016 ->
               true
           | uu____23019 -> false)
      | uu____23021 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____23035 = lookup_qname env1 l in
      match uu____23035 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____23038), uu____23039) ->
          FStar_Util.for_some
            (fun uu___10_23087 ->
               match uu___10_23087 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____23090 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____23092 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____23168 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____23186) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____23204 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____23212 ->
                 FStar_Pervasives_Native.Some true
             | uu____23231 -> FStar_Pervasives_Native.Some false) in
      let uu____23234 =
        let uu____23238 = lookup_qname env1 lid in
        FStar_Util.bind_opt uu____23238 mapper in
      match uu____23234 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1 ->
    fun lid ->
      let uu____23298 = lookup_qname env1 lid in
      match uu____23298 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23302, uu____23303, tps, uu____23305, uu____23306,
                 uu____23307);
              FStar_Syntax_Syntax.sigrng = uu____23308;
              FStar_Syntax_Syntax.sigquals = uu____23309;
              FStar_Syntax_Syntax.sigmeta = uu____23310;
              FStar_Syntax_Syntax.sigattrs = uu____23311;
              FStar_Syntax_Syntax.sigopts = uu____23312;_},
            uu____23313),
           uu____23314)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23382 -> FStar_Pervasives_Native.None
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
           (fun uu____23428 ->
              match uu____23428 with
              | (d, uu____23437) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1 ->
    fun l ->
      let uu____23453 = effect_decl_opt env1 l in
      match uu____23453 with
      | FStar_Pervasives_Native.None ->
          let uu____23468 = name_not_found l in
          let uu____23474 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____23468 uu____23474
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun l ->
      let uu____23502 = FStar_All.pipe_right l (get_effect_decl env1) in
      FStar_All.pipe_right uu____23502 FStar_Syntax_Util.is_layered
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23509 ->
         fun c -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23523 ->
            fun uu____23524 -> fun e -> FStar_Util.return_all e))
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
        let uu____23558 = FStar_Ident.lid_equals l1 l2 in
        if uu____23558
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23577 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____23577
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23596 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23649 ->
                        match uu____23649 with
                        | (m1, m2, uu____23663, uu____23664, uu____23665) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____23596 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23690, uu____23691, m3, j1, j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____23739 = join_opt env1 l1 l2 in
        match uu____23739 with
        | FStar_Pervasives_Native.None ->
            let uu____23760 =
              let uu____23766 =
                let uu____23768 = FStar_Syntax_Print.lid_to_string l1 in
                let uu____23770 = FStar_Syntax_Print.lid_to_string l2 in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23768 uu____23770 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23766) in
            FStar_Errors.raise_error uu____23760 env1.range
        | FStar_Pervasives_Native.Some t -> t
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l1 ->
      fun l2 ->
        let uu____23813 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____23813
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
  'uuuuuu23833 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23833) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls ->
    fun m ->
      let uu____23862 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23888 ->
                match uu____23888 with
                | (d, uu____23895) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____23862 with
      | FStar_Pervasives_Native.None ->
          let uu____23906 =
            let uu____23908 = FStar_Ident.string_of_lid m in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23908 in
          failwith uu____23906
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____23923 = inst_tscheme md.FStar_Syntax_Syntax.signature in
          (match uu____23923 with
           | (uu____23934, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____23952)::(wp, uu____23954)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____24010 -> failwith "Impossible"))
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
        | uu____24075 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1 ->
    fun comp ->
      let c = comp_to_comp_typ env1 comp in
      let uu____24088 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____24088 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____24105 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____24105 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____24130 =
                     let uu____24136 =
                       let uu____24138 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____24146 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one) in
                       let uu____24157 =
                         let uu____24159 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____24159 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____24138 uu____24146 uu____24157 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____24136) in
                   FStar_Errors.raise_error uu____24130
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____24167 =
                     let uu____24178 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____24178 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____24215 ->
                        fun uu____24216 ->
                          match (uu____24215, uu____24216) with
                          | ((x, uu____24246), (t, uu____24248)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____24167 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1 in
                 let c2 =
                   let uu____24279 =
                     let uu___1612_24280 = comp_to_comp_typ env1 c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1612_24280.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1612_24280.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1612_24280.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1612_24280.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____24279
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env1 c2)))
let effect_repr_aux :
  'uuuuuu24292 .
    'uuuuuu24292 ->
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
            let uu____24333 =
              let uu____24340 = num_effect_indices env1 eff_name r in
              ((FStar_List.length args), uu____24340) in
            match uu____24333 with
            | (given, expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24364 = FStar_Ident.string_of_lid eff_name in
                     let uu____24366 = FStar_Util.string_of_int given in
                     let uu____24368 = FStar_Util.string_of_int expected in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24364 uu____24366 uu____24368 in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r) in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c) in
          let uu____24373 = effect_decl_opt env1 effect_name in
          match uu____24373 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, uu____24395) ->
              let uu____24406 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              (match uu____24406 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24424 =
                       let uu____24427 =
                         let uu____24428 =
                           let uu____24445 =
                             let uu____24456 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg in
                             uu____24456 ::
                               (c1.FStar_Syntax_Syntax.effect_args) in
                           (repr, uu____24445) in
                         FStar_Syntax_Syntax.Tm_app uu____24428 in
                       let uu____24493 = get_range env1 in
                       FStar_Syntax_Syntax.mk uu____24427 uu____24493 in
                     FStar_Pervasives_Native.Some uu____24424)))
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
           (fun uu___11_24557 ->
              match uu___11_24557 with
              | FStar_Syntax_Syntax.Reflectable uu____24559 -> true
              | uu____24561 -> false))
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
      | uu____24621 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let uu____24636 =
        let uu____24637 = FStar_Syntax_Subst.compress t in
        uu____24637.FStar_Syntax_Syntax.n in
      match uu____24636 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24641, c) ->
          is_reifiable_comp env1 c
      | uu____24663 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu____24683 =
           let uu____24685 = is_reifiable_effect env1 l in
           Prims.op_Negation uu____24685 in
         if uu____24683
         then
           let uu____24688 =
             let uu____24694 =
               let uu____24696 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24696 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24694) in
           let uu____24700 = get_range env1 in
           FStar_Errors.raise_error uu____24688 uu____24700
         else ());
        (let uu____24703 = effect_repr_aux true env1 c u_c in
         match uu____24703 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env2 =
        let uu___1689_24739 = env1 in
        {
          solver = (uu___1689_24739.solver);
          range = (uu___1689_24739.range);
          curmodule = (uu___1689_24739.curmodule);
          gamma = (uu___1689_24739.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1689_24739.gamma_cache);
          modules = (uu___1689_24739.modules);
          expected_typ = (uu___1689_24739.expected_typ);
          sigtab = (uu___1689_24739.sigtab);
          attrtab = (uu___1689_24739.attrtab);
          instantiate_imp = (uu___1689_24739.instantiate_imp);
          effects = (uu___1689_24739.effects);
          generalize = (uu___1689_24739.generalize);
          letrecs = (uu___1689_24739.letrecs);
          top_level = (uu___1689_24739.top_level);
          check_uvars = (uu___1689_24739.check_uvars);
          use_eq = (uu___1689_24739.use_eq);
          use_eq_strict = (uu___1689_24739.use_eq_strict);
          is_iface = (uu___1689_24739.is_iface);
          admit = (uu___1689_24739.admit);
          lax = (uu___1689_24739.lax);
          lax_universes = (uu___1689_24739.lax_universes);
          phase1 = (uu___1689_24739.phase1);
          failhard = (uu___1689_24739.failhard);
          nosynth = (uu___1689_24739.nosynth);
          uvar_subtyping = (uu___1689_24739.uvar_subtyping);
          tc_term = (uu___1689_24739.tc_term);
          type_of = (uu___1689_24739.type_of);
          universe_of = (uu___1689_24739.universe_of);
          check_type_of = (uu___1689_24739.check_type_of);
          use_bv_sorts = (uu___1689_24739.use_bv_sorts);
          qtbl_name_and_index = (uu___1689_24739.qtbl_name_and_index);
          normalized_eff_names = (uu___1689_24739.normalized_eff_names);
          fv_delta_depths = (uu___1689_24739.fv_delta_depths);
          proof_ns = (uu___1689_24739.proof_ns);
          synth_hook = (uu___1689_24739.synth_hook);
          try_solve_implicits_hook =
            (uu___1689_24739.try_solve_implicits_hook);
          splice = (uu___1689_24739.splice);
          mpreprocess = (uu___1689_24739.mpreprocess);
          postprocess = (uu___1689_24739.postprocess);
          identifier_info = (uu___1689_24739.identifier_info);
          tc_hooks = (uu___1689_24739.tc_hooks);
          dsenv = (uu___1689_24739.dsenv);
          nbe = (uu___1689_24739.nbe);
          strict_args_tab = (uu___1689_24739.strict_args_tab);
          erasable_types_tab = (uu___1689_24739.erasable_types_tab);
          enable_defer_to_tac = (uu___1689_24739.enable_defer_to_tac)
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
    fun uu____24758 ->
      match uu____24758 with
      | (ed, quals) ->
          let effects1 =
            let uu___1698_24772 = env1.effects in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1698_24772.order);
              joins = (uu___1698_24772.joins);
              polymonadic_binds = (uu___1698_24772.polymonadic_binds)
            } in
          let uu___1701_24781 = env1 in
          {
            solver = (uu___1701_24781.solver);
            range = (uu___1701_24781.range);
            curmodule = (uu___1701_24781.curmodule);
            gamma = (uu___1701_24781.gamma);
            gamma_sig = (uu___1701_24781.gamma_sig);
            gamma_cache = (uu___1701_24781.gamma_cache);
            modules = (uu___1701_24781.modules);
            expected_typ = (uu___1701_24781.expected_typ);
            sigtab = (uu___1701_24781.sigtab);
            attrtab = (uu___1701_24781.attrtab);
            instantiate_imp = (uu___1701_24781.instantiate_imp);
            effects = effects1;
            generalize = (uu___1701_24781.generalize);
            letrecs = (uu___1701_24781.letrecs);
            top_level = (uu___1701_24781.top_level);
            check_uvars = (uu___1701_24781.check_uvars);
            use_eq = (uu___1701_24781.use_eq);
            use_eq_strict = (uu___1701_24781.use_eq_strict);
            is_iface = (uu___1701_24781.is_iface);
            admit = (uu___1701_24781.admit);
            lax = (uu___1701_24781.lax);
            lax_universes = (uu___1701_24781.lax_universes);
            phase1 = (uu___1701_24781.phase1);
            failhard = (uu___1701_24781.failhard);
            nosynth = (uu___1701_24781.nosynth);
            uvar_subtyping = (uu___1701_24781.uvar_subtyping);
            tc_term = (uu___1701_24781.tc_term);
            type_of = (uu___1701_24781.type_of);
            universe_of = (uu___1701_24781.universe_of);
            check_type_of = (uu___1701_24781.check_type_of);
            use_bv_sorts = (uu___1701_24781.use_bv_sorts);
            qtbl_name_and_index = (uu___1701_24781.qtbl_name_and_index);
            normalized_eff_names = (uu___1701_24781.normalized_eff_names);
            fv_delta_depths = (uu___1701_24781.fv_delta_depths);
            proof_ns = (uu___1701_24781.proof_ns);
            synth_hook = (uu___1701_24781.synth_hook);
            try_solve_implicits_hook =
              (uu___1701_24781.try_solve_implicits_hook);
            splice = (uu___1701_24781.splice);
            mpreprocess = (uu___1701_24781.mpreprocess);
            postprocess = (uu___1701_24781.postprocess);
            identifier_info = (uu___1701_24781.identifier_info);
            tc_hooks = (uu___1701_24781.tc_hooks);
            dsenv = (uu___1701_24781.dsenv);
            nbe = (uu___1701_24781.nbe);
            strict_args_tab = (uu___1701_24781.strict_args_tab);
            erasable_types_tab = (uu___1701_24781.erasable_types_tab);
            enable_defer_to_tac = (uu___1701_24781.enable_defer_to_tac)
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
        let uu____24810 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24878 ->
                  match uu____24878 with
                  | (m1, n1, uu____24896, uu____24897) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1))) in
        match uu____24810 with
        | FStar_Pervasives_Native.Some (uu____24922, uu____24923, p, t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24968 -> FStar_Pervasives_Native.None
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1 ->
    fun src ->
      fun tgt ->
        fun st_mlift ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____25043 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2) in
                FStar_All.pipe_right uu____25043
                  (fun uu____25064 ->
                     match uu____25064 with
                     | (c1, g1) ->
                         let uu____25075 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2) in
                         FStar_All.pipe_right uu____25075
                           (fun uu____25096 ->
                              match uu____25096 with
                              | (c2, g2) ->
                                  let uu____25107 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2 in
                                  (c2, uu____25107))) in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun e ->
                              let uu____25229 = l1 u t e in
                              l2 u t uu____25229))
                | uu____25230 -> FStar_Pervasives_Native.None in
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
                 (fun uu____25298 ->
                    match uu____25298 with
                    | (e, uu____25306) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____25329 =
            match uu____25329 with
            | (i, j) ->
                let uu____25340 = FStar_Ident.lid_equals i j in
                if uu____25340
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____25347 ->
                       FStar_Pervasives_Native.Some uu____25347)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____25376 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i ->
                        let uu____25386 = FStar_Ident.lid_equals i k in
                        if uu____25386
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j ->
                                  let uu____25400 =
                                    FStar_Ident.lid_equals j k in
                                  if uu____25400
                                  then []
                                  else
                                    (let uu____25407 =
                                       let uu____25416 =
                                         find_edge order1 (i, k) in
                                       let uu____25419 =
                                         find_edge order1 (k, j) in
                                       (uu____25416, uu____25419) in
                                     match uu____25407 with
                                     | (FStar_Pervasives_Native.Some e1,
                                        FStar_Pervasives_Native.Some e2) ->
                                         let uu____25434 =
                                           compose_edges e1 e2 in
                                         [uu____25434]
                                     | uu____25435 -> []))))) in
              FStar_List.append order1 uu____25376 in
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
                  let uu____25465 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25468 =
                         lookup_effect_quals env1 edge2.mtarget in
                       FStar_All.pipe_right uu____25468
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)) in
                  if uu____25465
                  then
                    let uu____25475 =
                      let uu____25481 =
                        let uu____25483 =
                          FStar_Ident.string_of_lid edge2.mtarget in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25483 in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25481) in
                    let uu____25487 = get_range env1 in
                    FStar_Errors.raise_error uu____25475 uu____25487
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j ->
                             let join_opt1 =
                               let uu____25565 = FStar_Ident.lid_equals i j in
                               if uu____25565
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt ->
                                         fun k ->
                                           let uu____25617 =
                                             let uu____25626 =
                                               find_edge order2 (i, k) in
                                             let uu____25629 =
                                               find_edge order2 (j, k) in
                                             (uu____25626, uu____25629) in
                                           match uu____25617 with
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
                                                    (ub, uu____25671,
                                                     uu____25672)
                                                    ->
                                                    let uu____25679 =
                                                      let uu____25686 =
                                                        let uu____25688 =
                                                          find_edge order2
                                                            (k, ub) in
                                                        FStar_Util.is_some
                                                          uu____25688 in
                                                      let uu____25691 =
                                                        let uu____25693 =
                                                          find_edge order2
                                                            (ub, k) in
                                                        FStar_Util.is_some
                                                          uu____25693 in
                                                      (uu____25686,
                                                        uu____25691) in
                                                    (match uu____25679 with
                                                     | (true, true) ->
                                                         let uu____25710 =
                                                           FStar_Ident.lid_equals
                                                             k ub in
                                                         if uu____25710
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
                                           | uu____25753 -> bopt)
                                      FStar_Pervasives_Native.None) in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None -> []
                             | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                 let uu____25805 =
                                   let uu____25807 =
                                     exists_polymonadic_bind env1 i j in
                                   FStar_All.pipe_right uu____25807
                                     FStar_Util.is_some in
                                 if uu____25805
                                 then
                                   let uu____25856 =
                                     let uu____25862 =
                                       let uu____25864 =
                                         FStar_Ident.string_of_lid src in
                                       let uu____25866 =
                                         FStar_Ident.string_of_lid tgt in
                                       let uu____25868 =
                                         FStar_Ident.string_of_lid i in
                                       let uu____25870 =
                                         FStar_Ident.string_of_lid j in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25864 uu____25866 uu____25868
                                         uu____25870 in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25862) in
                                   FStar_Errors.raise_error uu____25856
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))])))) in
           let effects1 =
             let uu___1822_25909 = env1.effects in
             {
               decls = (uu___1822_25909.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1822_25909.polymonadic_binds)
             } in
           let uu___1825_25910 = env1 in
           {
             solver = (uu___1825_25910.solver);
             range = (uu___1825_25910.range);
             curmodule = (uu___1825_25910.curmodule);
             gamma = (uu___1825_25910.gamma);
             gamma_sig = (uu___1825_25910.gamma_sig);
             gamma_cache = (uu___1825_25910.gamma_cache);
             modules = (uu___1825_25910.modules);
             expected_typ = (uu___1825_25910.expected_typ);
             sigtab = (uu___1825_25910.sigtab);
             attrtab = (uu___1825_25910.attrtab);
             instantiate_imp = (uu___1825_25910.instantiate_imp);
             effects = effects1;
             generalize = (uu___1825_25910.generalize);
             letrecs = (uu___1825_25910.letrecs);
             top_level = (uu___1825_25910.top_level);
             check_uvars = (uu___1825_25910.check_uvars);
             use_eq = (uu___1825_25910.use_eq);
             use_eq_strict = (uu___1825_25910.use_eq_strict);
             is_iface = (uu___1825_25910.is_iface);
             admit = (uu___1825_25910.admit);
             lax = (uu___1825_25910.lax);
             lax_universes = (uu___1825_25910.lax_universes);
             phase1 = (uu___1825_25910.phase1);
             failhard = (uu___1825_25910.failhard);
             nosynth = (uu___1825_25910.nosynth);
             uvar_subtyping = (uu___1825_25910.uvar_subtyping);
             tc_term = (uu___1825_25910.tc_term);
             type_of = (uu___1825_25910.type_of);
             universe_of = (uu___1825_25910.universe_of);
             check_type_of = (uu___1825_25910.check_type_of);
             use_bv_sorts = (uu___1825_25910.use_bv_sorts);
             qtbl_name_and_index = (uu___1825_25910.qtbl_name_and_index);
             normalized_eff_names = (uu___1825_25910.normalized_eff_names);
             fv_delta_depths = (uu___1825_25910.fv_delta_depths);
             proof_ns = (uu___1825_25910.proof_ns);
             synth_hook = (uu___1825_25910.synth_hook);
             try_solve_implicits_hook =
               (uu___1825_25910.try_solve_implicits_hook);
             splice = (uu___1825_25910.splice);
             mpreprocess = (uu___1825_25910.mpreprocess);
             postprocess = (uu___1825_25910.postprocess);
             identifier_info = (uu___1825_25910.identifier_info);
             tc_hooks = (uu___1825_25910.tc_hooks);
             dsenv = (uu___1825_25910.dsenv);
             nbe = (uu___1825_25910.nbe);
             strict_args_tab = (uu___1825_25910.strict_args_tab);
             erasable_types_tab = (uu___1825_25910.erasable_types_tab);
             enable_defer_to_tac = (uu___1825_25910.enable_defer_to_tac)
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
              let uu____25958 = FStar_Ident.string_of_lid m in
              let uu____25960 = FStar_Ident.string_of_lid n in
              let uu____25962 = FStar_Ident.string_of_lid p in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25958 uu____25960 uu____25962
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice") in
            let uu____25971 =
              let uu____25973 = exists_polymonadic_bind env1 m n in
              FStar_All.pipe_right uu____25973 FStar_Util.is_some in
            if uu____25971
            then
              let uu____26010 =
                let uu____26016 = err_msg true in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26016) in
              FStar_Errors.raise_error uu____26010 env1.range
            else
              (let uu____26022 =
                 let uu____26024 = join_opt env1 m n in
                 FStar_All.pipe_right uu____26024 FStar_Util.is_some in
               if uu____26022
               then
                 let uu____26049 =
                   let uu____26055 = err_msg false in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26055) in
                 FStar_Errors.raise_error uu____26049 env1.range
               else
                 (let uu___1840_26061 = env1 in
                  {
                    solver = (uu___1840_26061.solver);
                    range = (uu___1840_26061.range);
                    curmodule = (uu___1840_26061.curmodule);
                    gamma = (uu___1840_26061.gamma);
                    gamma_sig = (uu___1840_26061.gamma_sig);
                    gamma_cache = (uu___1840_26061.gamma_cache);
                    modules = (uu___1840_26061.modules);
                    expected_typ = (uu___1840_26061.expected_typ);
                    sigtab = (uu___1840_26061.sigtab);
                    attrtab = (uu___1840_26061.attrtab);
                    instantiate_imp = (uu___1840_26061.instantiate_imp);
                    effects =
                      (let uu___1842_26063 = env1.effects in
                       {
                         decls = (uu___1842_26063.decls);
                         order = (uu___1842_26063.order);
                         joins = (uu___1842_26063.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1840_26061.generalize);
                    letrecs = (uu___1840_26061.letrecs);
                    top_level = (uu___1840_26061.top_level);
                    check_uvars = (uu___1840_26061.check_uvars);
                    use_eq = (uu___1840_26061.use_eq);
                    use_eq_strict = (uu___1840_26061.use_eq_strict);
                    is_iface = (uu___1840_26061.is_iface);
                    admit = (uu___1840_26061.admit);
                    lax = (uu___1840_26061.lax);
                    lax_universes = (uu___1840_26061.lax_universes);
                    phase1 = (uu___1840_26061.phase1);
                    failhard = (uu___1840_26061.failhard);
                    nosynth = (uu___1840_26061.nosynth);
                    uvar_subtyping = (uu___1840_26061.uvar_subtyping);
                    tc_term = (uu___1840_26061.tc_term);
                    type_of = (uu___1840_26061.type_of);
                    universe_of = (uu___1840_26061.universe_of);
                    check_type_of = (uu___1840_26061.check_type_of);
                    use_bv_sorts = (uu___1840_26061.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1840_26061.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1840_26061.normalized_eff_names);
                    fv_delta_depths = (uu___1840_26061.fv_delta_depths);
                    proof_ns = (uu___1840_26061.proof_ns);
                    synth_hook = (uu___1840_26061.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1840_26061.try_solve_implicits_hook);
                    splice = (uu___1840_26061.splice);
                    mpreprocess = (uu___1840_26061.mpreprocess);
                    postprocess = (uu___1840_26061.postprocess);
                    identifier_info = (uu___1840_26061.identifier_info);
                    tc_hooks = (uu___1840_26061.tc_hooks);
                    dsenv = (uu___1840_26061.dsenv);
                    nbe = (uu___1840_26061.nbe);
                    strict_args_tab = (uu___1840_26061.strict_args_tab);
                    erasable_types_tab = (uu___1840_26061.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1840_26061.enable_defer_to_tac)
                  }))
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1 ->
    fun b ->
      let uu___1846_26135 = env1 in
      {
        solver = (uu___1846_26135.solver);
        range = (uu___1846_26135.range);
        curmodule = (uu___1846_26135.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1846_26135.gamma_sig);
        gamma_cache = (uu___1846_26135.gamma_cache);
        modules = (uu___1846_26135.modules);
        expected_typ = (uu___1846_26135.expected_typ);
        sigtab = (uu___1846_26135.sigtab);
        attrtab = (uu___1846_26135.attrtab);
        instantiate_imp = (uu___1846_26135.instantiate_imp);
        effects = (uu___1846_26135.effects);
        generalize = (uu___1846_26135.generalize);
        letrecs = (uu___1846_26135.letrecs);
        top_level = (uu___1846_26135.top_level);
        check_uvars = (uu___1846_26135.check_uvars);
        use_eq = (uu___1846_26135.use_eq);
        use_eq_strict = (uu___1846_26135.use_eq_strict);
        is_iface = (uu___1846_26135.is_iface);
        admit = (uu___1846_26135.admit);
        lax = (uu___1846_26135.lax);
        lax_universes = (uu___1846_26135.lax_universes);
        phase1 = (uu___1846_26135.phase1);
        failhard = (uu___1846_26135.failhard);
        nosynth = (uu___1846_26135.nosynth);
        uvar_subtyping = (uu___1846_26135.uvar_subtyping);
        tc_term = (uu___1846_26135.tc_term);
        type_of = (uu___1846_26135.type_of);
        universe_of = (uu___1846_26135.universe_of);
        check_type_of = (uu___1846_26135.check_type_of);
        use_bv_sorts = (uu___1846_26135.use_bv_sorts);
        qtbl_name_and_index = (uu___1846_26135.qtbl_name_and_index);
        normalized_eff_names = (uu___1846_26135.normalized_eff_names);
        fv_delta_depths = (uu___1846_26135.fv_delta_depths);
        proof_ns = (uu___1846_26135.proof_ns);
        synth_hook = (uu___1846_26135.synth_hook);
        try_solve_implicits_hook = (uu___1846_26135.try_solve_implicits_hook);
        splice = (uu___1846_26135.splice);
        mpreprocess = (uu___1846_26135.mpreprocess);
        postprocess = (uu___1846_26135.postprocess);
        identifier_info = (uu___1846_26135.identifier_info);
        tc_hooks = (uu___1846_26135.tc_hooks);
        dsenv = (uu___1846_26135.dsenv);
        nbe = (uu___1846_26135.nbe);
        strict_args_tab = (uu___1846_26135.strict_args_tab);
        erasable_types_tab = (uu___1846_26135.erasable_types_tab);
        enable_defer_to_tac = (uu___1846_26135.enable_defer_to_tac)
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
            (let uu___1859_26193 = env1 in
             {
               solver = (uu___1859_26193.solver);
               range = (uu___1859_26193.range);
               curmodule = (uu___1859_26193.curmodule);
               gamma = rest;
               gamma_sig = (uu___1859_26193.gamma_sig);
               gamma_cache = (uu___1859_26193.gamma_cache);
               modules = (uu___1859_26193.modules);
               expected_typ = (uu___1859_26193.expected_typ);
               sigtab = (uu___1859_26193.sigtab);
               attrtab = (uu___1859_26193.attrtab);
               instantiate_imp = (uu___1859_26193.instantiate_imp);
               effects = (uu___1859_26193.effects);
               generalize = (uu___1859_26193.generalize);
               letrecs = (uu___1859_26193.letrecs);
               top_level = (uu___1859_26193.top_level);
               check_uvars = (uu___1859_26193.check_uvars);
               use_eq = (uu___1859_26193.use_eq);
               use_eq_strict = (uu___1859_26193.use_eq_strict);
               is_iface = (uu___1859_26193.is_iface);
               admit = (uu___1859_26193.admit);
               lax = (uu___1859_26193.lax);
               lax_universes = (uu___1859_26193.lax_universes);
               phase1 = (uu___1859_26193.phase1);
               failhard = (uu___1859_26193.failhard);
               nosynth = (uu___1859_26193.nosynth);
               uvar_subtyping = (uu___1859_26193.uvar_subtyping);
               tc_term = (uu___1859_26193.tc_term);
               type_of = (uu___1859_26193.type_of);
               universe_of = (uu___1859_26193.universe_of);
               check_type_of = (uu___1859_26193.check_type_of);
               use_bv_sorts = (uu___1859_26193.use_bv_sorts);
               qtbl_name_and_index = (uu___1859_26193.qtbl_name_and_index);
               normalized_eff_names = (uu___1859_26193.normalized_eff_names);
               fv_delta_depths = (uu___1859_26193.fv_delta_depths);
               proof_ns = (uu___1859_26193.proof_ns);
               synth_hook = (uu___1859_26193.synth_hook);
               try_solve_implicits_hook =
                 (uu___1859_26193.try_solve_implicits_hook);
               splice = (uu___1859_26193.splice);
               mpreprocess = (uu___1859_26193.mpreprocess);
               postprocess = (uu___1859_26193.postprocess);
               identifier_info = (uu___1859_26193.identifier_info);
               tc_hooks = (uu___1859_26193.tc_hooks);
               dsenv = (uu___1859_26193.dsenv);
               nbe = (uu___1859_26193.nbe);
               strict_args_tab = (uu___1859_26193.strict_args_tab);
               erasable_types_tab = (uu___1859_26193.erasable_types_tab);
               enable_defer_to_tac = (uu___1859_26193.enable_defer_to_tac)
             }))
    | uu____26194 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1 ->
    fun bs ->
      FStar_List.fold_left
        (fun env2 ->
           fun uu____26223 ->
             match uu____26223 with | (x, uu____26231) -> push_bv env2 x)
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
            let uu___1873_26266 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1873_26266.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1873_26266.FStar_Syntax_Syntax.index);
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
        let uu____26339 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____26339 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env1 univ_vars in
            let uu____26367 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____26367)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1 ->
    fun t ->
      let uu___1894_26383 = env1 in
      {
        solver = (uu___1894_26383.solver);
        range = (uu___1894_26383.range);
        curmodule = (uu___1894_26383.curmodule);
        gamma = (uu___1894_26383.gamma);
        gamma_sig = (uu___1894_26383.gamma_sig);
        gamma_cache = (uu___1894_26383.gamma_cache);
        modules = (uu___1894_26383.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1894_26383.sigtab);
        attrtab = (uu___1894_26383.attrtab);
        instantiate_imp = (uu___1894_26383.instantiate_imp);
        effects = (uu___1894_26383.effects);
        generalize = (uu___1894_26383.generalize);
        letrecs = (uu___1894_26383.letrecs);
        top_level = (uu___1894_26383.top_level);
        check_uvars = (uu___1894_26383.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1894_26383.use_eq_strict);
        is_iface = (uu___1894_26383.is_iface);
        admit = (uu___1894_26383.admit);
        lax = (uu___1894_26383.lax);
        lax_universes = (uu___1894_26383.lax_universes);
        phase1 = (uu___1894_26383.phase1);
        failhard = (uu___1894_26383.failhard);
        nosynth = (uu___1894_26383.nosynth);
        uvar_subtyping = (uu___1894_26383.uvar_subtyping);
        tc_term = (uu___1894_26383.tc_term);
        type_of = (uu___1894_26383.type_of);
        universe_of = (uu___1894_26383.universe_of);
        check_type_of = (uu___1894_26383.check_type_of);
        use_bv_sorts = (uu___1894_26383.use_bv_sorts);
        qtbl_name_and_index = (uu___1894_26383.qtbl_name_and_index);
        normalized_eff_names = (uu___1894_26383.normalized_eff_names);
        fv_delta_depths = (uu___1894_26383.fv_delta_depths);
        proof_ns = (uu___1894_26383.proof_ns);
        synth_hook = (uu___1894_26383.synth_hook);
        try_solve_implicits_hook = (uu___1894_26383.try_solve_implicits_hook);
        splice = (uu___1894_26383.splice);
        mpreprocess = (uu___1894_26383.mpreprocess);
        postprocess = (uu___1894_26383.postprocess);
        identifier_info = (uu___1894_26383.identifier_info);
        tc_hooks = (uu___1894_26383.tc_hooks);
        dsenv = (uu___1894_26383.dsenv);
        nbe = (uu___1894_26383.nbe);
        strict_args_tab = (uu___1894_26383.strict_args_tab);
        erasable_types_tab = (uu___1894_26383.erasable_types_tab);
        enable_defer_to_tac = (uu___1894_26383.enable_defer_to_tac)
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
    let uu____26414 = expected_typ env_ in
    ((let uu___1901_26420 = env_ in
      {
        solver = (uu___1901_26420.solver);
        range = (uu___1901_26420.range);
        curmodule = (uu___1901_26420.curmodule);
        gamma = (uu___1901_26420.gamma);
        gamma_sig = (uu___1901_26420.gamma_sig);
        gamma_cache = (uu___1901_26420.gamma_cache);
        modules = (uu___1901_26420.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1901_26420.sigtab);
        attrtab = (uu___1901_26420.attrtab);
        instantiate_imp = (uu___1901_26420.instantiate_imp);
        effects = (uu___1901_26420.effects);
        generalize = (uu___1901_26420.generalize);
        letrecs = (uu___1901_26420.letrecs);
        top_level = (uu___1901_26420.top_level);
        check_uvars = (uu___1901_26420.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1901_26420.use_eq_strict);
        is_iface = (uu___1901_26420.is_iface);
        admit = (uu___1901_26420.admit);
        lax = (uu___1901_26420.lax);
        lax_universes = (uu___1901_26420.lax_universes);
        phase1 = (uu___1901_26420.phase1);
        failhard = (uu___1901_26420.failhard);
        nosynth = (uu___1901_26420.nosynth);
        uvar_subtyping = (uu___1901_26420.uvar_subtyping);
        tc_term = (uu___1901_26420.tc_term);
        type_of = (uu___1901_26420.type_of);
        universe_of = (uu___1901_26420.universe_of);
        check_type_of = (uu___1901_26420.check_type_of);
        use_bv_sorts = (uu___1901_26420.use_bv_sorts);
        qtbl_name_and_index = (uu___1901_26420.qtbl_name_and_index);
        normalized_eff_names = (uu___1901_26420.normalized_eff_names);
        fv_delta_depths = (uu___1901_26420.fv_delta_depths);
        proof_ns = (uu___1901_26420.proof_ns);
        synth_hook = (uu___1901_26420.synth_hook);
        try_solve_implicits_hook = (uu___1901_26420.try_solve_implicits_hook);
        splice = (uu___1901_26420.splice);
        mpreprocess = (uu___1901_26420.mpreprocess);
        postprocess = (uu___1901_26420.postprocess);
        identifier_info = (uu___1901_26420.identifier_info);
        tc_hooks = (uu___1901_26420.tc_hooks);
        dsenv = (uu___1901_26420.dsenv);
        nbe = (uu___1901_26420.nbe);
        strict_args_tab = (uu___1901_26420.strict_args_tab);
        erasable_types_tab = (uu___1901_26420.erasable_types_tab);
        enable_defer_to_tac = (uu___1901_26420.enable_defer_to_tac)
      }), uu____26414)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26432 =
      let uu____26433 = FStar_Ident.id_of_text "" in [uu____26433] in
    FStar_Ident.lid_of_ids uu____26432 in
  fun env1 ->
    fun m ->
      let sigs =
        let uu____26440 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____26440
        then
          let uu____26445 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu____26445 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env1 sigs;
      (let uu___1909_26473 = env1 in
       {
         solver = (uu___1909_26473.solver);
         range = (uu___1909_26473.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1909_26473.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1909_26473.expected_typ);
         sigtab = (uu___1909_26473.sigtab);
         attrtab = (uu___1909_26473.attrtab);
         instantiate_imp = (uu___1909_26473.instantiate_imp);
         effects = (uu___1909_26473.effects);
         generalize = (uu___1909_26473.generalize);
         letrecs = (uu___1909_26473.letrecs);
         top_level = (uu___1909_26473.top_level);
         check_uvars = (uu___1909_26473.check_uvars);
         use_eq = (uu___1909_26473.use_eq);
         use_eq_strict = (uu___1909_26473.use_eq_strict);
         is_iface = (uu___1909_26473.is_iface);
         admit = (uu___1909_26473.admit);
         lax = (uu___1909_26473.lax);
         lax_universes = (uu___1909_26473.lax_universes);
         phase1 = (uu___1909_26473.phase1);
         failhard = (uu___1909_26473.failhard);
         nosynth = (uu___1909_26473.nosynth);
         uvar_subtyping = (uu___1909_26473.uvar_subtyping);
         tc_term = (uu___1909_26473.tc_term);
         type_of = (uu___1909_26473.type_of);
         universe_of = (uu___1909_26473.universe_of);
         check_type_of = (uu___1909_26473.check_type_of);
         use_bv_sorts = (uu___1909_26473.use_bv_sorts);
         qtbl_name_and_index = (uu___1909_26473.qtbl_name_and_index);
         normalized_eff_names = (uu___1909_26473.normalized_eff_names);
         fv_delta_depths = (uu___1909_26473.fv_delta_depths);
         proof_ns = (uu___1909_26473.proof_ns);
         synth_hook = (uu___1909_26473.synth_hook);
         try_solve_implicits_hook =
           (uu___1909_26473.try_solve_implicits_hook);
         splice = (uu___1909_26473.splice);
         mpreprocess = (uu___1909_26473.mpreprocess);
         postprocess = (uu___1909_26473.postprocess);
         identifier_info = (uu___1909_26473.identifier_info);
         tc_hooks = (uu___1909_26473.tc_hooks);
         dsenv = (uu___1909_26473.dsenv);
         nbe = (uu___1909_26473.nbe);
         strict_args_tab = (uu___1909_26473.strict_args_tab);
         erasable_types_tab = (uu___1909_26473.erasable_types_tab);
         enable_defer_to_tac = (uu___1909_26473.enable_defer_to_tac)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1 ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26525)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26529, (uu____26530, t)))::tl
          ->
          let uu____26551 =
            let uu____26554 = FStar_Syntax_Free.uvars t in
            ext out uu____26554 in
          aux uu____26551 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26557;
            FStar_Syntax_Syntax.index = uu____26558;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26566 =
            let uu____26569 = FStar_Syntax_Free.uvars t in
            ext out uu____26569 in
          aux uu____26566 tl in
    aux no_uvs env1.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1 ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26627)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26631, (uu____26632, t)))::tl
          ->
          let uu____26653 =
            let uu____26656 = FStar_Syntax_Free.univs t in
            ext out uu____26656 in
          aux uu____26653 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26659;
            FStar_Syntax_Syntax.index = uu____26660;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26668 =
            let uu____26671 = FStar_Syntax_Free.univs t in
            ext out uu____26671 in
          aux uu____26668 tl in
    aux no_univs env1.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env1 ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu____26733 = FStar_Util.set_add uname out in
          aux uu____26733 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26736, (uu____26737, t)))::tl
          ->
          let uu____26758 =
            let uu____26761 = FStar_Syntax_Free.univnames t in
            ext out uu____26761 in
          aux uu____26758 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26764;
            FStar_Syntax_Syntax.index = uu____26765;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26773 =
            let uu____26776 = FStar_Syntax_Free.univnames t in
            ext out uu____26776 in
          aux uu____26773 tl in
    aux no_univ_names env1.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26797 ->
            match uu___12_26797 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26801 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26814 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____26825 =
      let uu____26834 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____26834
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____26825 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1 -> bound_vars_of_bindings env1.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1 -> binders_of_bindings env1.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu____26882 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26895 ->
              match uu___13_26895 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26898 = FStar_Syntax_Print.bv_to_string x in
                  Prims.op_Hat "Binding_var " uu____26898
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26902 = FStar_Ident.string_of_id u in
                  Prims.op_Hat "Binding_univ " uu____26902
              | FStar_Syntax_Syntax.Binding_lid (l, uu____26906) ->
                  let uu____26923 = FStar_Ident.string_of_lid l in
                  Prims.op_Hat "Binding_lid " uu____26923)) in
    FStar_All.pipe_right uu____26882 (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26937 ->
    match uu___14_26937 with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26943 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.op_Hat "Unfold " uu____26943
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26966 ->
         fun v ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1 ->
    fun path ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([], uu____27021) -> true
        | (x::xs1, y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____27054, uu____27055) -> false in
      let uu____27069 =
        FStar_List.tryFind
          (fun uu____27091 ->
             match uu____27091 with | (p, uu____27102) -> str_i_prefix p path)
          env1.proof_ns in
      match uu____27069 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____27121, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____27151 = FStar_Ident.path_of_lid lid in
      should_enc_path env1 uu____27151
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___2052_27173 = e in
        {
          solver = (uu___2052_27173.solver);
          range = (uu___2052_27173.range);
          curmodule = (uu___2052_27173.curmodule);
          gamma = (uu___2052_27173.gamma);
          gamma_sig = (uu___2052_27173.gamma_sig);
          gamma_cache = (uu___2052_27173.gamma_cache);
          modules = (uu___2052_27173.modules);
          expected_typ = (uu___2052_27173.expected_typ);
          sigtab = (uu___2052_27173.sigtab);
          attrtab = (uu___2052_27173.attrtab);
          instantiate_imp = (uu___2052_27173.instantiate_imp);
          effects = (uu___2052_27173.effects);
          generalize = (uu___2052_27173.generalize);
          letrecs = (uu___2052_27173.letrecs);
          top_level = (uu___2052_27173.top_level);
          check_uvars = (uu___2052_27173.check_uvars);
          use_eq = (uu___2052_27173.use_eq);
          use_eq_strict = (uu___2052_27173.use_eq_strict);
          is_iface = (uu___2052_27173.is_iface);
          admit = (uu___2052_27173.admit);
          lax = (uu___2052_27173.lax);
          lax_universes = (uu___2052_27173.lax_universes);
          phase1 = (uu___2052_27173.phase1);
          failhard = (uu___2052_27173.failhard);
          nosynth = (uu___2052_27173.nosynth);
          uvar_subtyping = (uu___2052_27173.uvar_subtyping);
          tc_term = (uu___2052_27173.tc_term);
          type_of = (uu___2052_27173.type_of);
          universe_of = (uu___2052_27173.universe_of);
          check_type_of = (uu___2052_27173.check_type_of);
          use_bv_sorts = (uu___2052_27173.use_bv_sorts);
          qtbl_name_and_index = (uu___2052_27173.qtbl_name_and_index);
          normalized_eff_names = (uu___2052_27173.normalized_eff_names);
          fv_delta_depths = (uu___2052_27173.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2052_27173.synth_hook);
          try_solve_implicits_hook =
            (uu___2052_27173.try_solve_implicits_hook);
          splice = (uu___2052_27173.splice);
          mpreprocess = (uu___2052_27173.mpreprocess);
          postprocess = (uu___2052_27173.postprocess);
          identifier_info = (uu___2052_27173.identifier_info);
          tc_hooks = (uu___2052_27173.tc_hooks);
          dsenv = (uu___2052_27173.dsenv);
          nbe = (uu___2052_27173.nbe);
          strict_args_tab = (uu___2052_27173.strict_args_tab);
          erasable_types_tab = (uu___2052_27173.erasable_types_tab);
          enable_defer_to_tac = (uu___2052_27173.enable_defer_to_tac)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___2061_27221 = e in
      {
        solver = (uu___2061_27221.solver);
        range = (uu___2061_27221.range);
        curmodule = (uu___2061_27221.curmodule);
        gamma = (uu___2061_27221.gamma);
        gamma_sig = (uu___2061_27221.gamma_sig);
        gamma_cache = (uu___2061_27221.gamma_cache);
        modules = (uu___2061_27221.modules);
        expected_typ = (uu___2061_27221.expected_typ);
        sigtab = (uu___2061_27221.sigtab);
        attrtab = (uu___2061_27221.attrtab);
        instantiate_imp = (uu___2061_27221.instantiate_imp);
        effects = (uu___2061_27221.effects);
        generalize = (uu___2061_27221.generalize);
        letrecs = (uu___2061_27221.letrecs);
        top_level = (uu___2061_27221.top_level);
        check_uvars = (uu___2061_27221.check_uvars);
        use_eq = (uu___2061_27221.use_eq);
        use_eq_strict = (uu___2061_27221.use_eq_strict);
        is_iface = (uu___2061_27221.is_iface);
        admit = (uu___2061_27221.admit);
        lax = (uu___2061_27221.lax);
        lax_universes = (uu___2061_27221.lax_universes);
        phase1 = (uu___2061_27221.phase1);
        failhard = (uu___2061_27221.failhard);
        nosynth = (uu___2061_27221.nosynth);
        uvar_subtyping = (uu___2061_27221.uvar_subtyping);
        tc_term = (uu___2061_27221.tc_term);
        type_of = (uu___2061_27221.type_of);
        universe_of = (uu___2061_27221.universe_of);
        check_type_of = (uu___2061_27221.check_type_of);
        use_bv_sorts = (uu___2061_27221.use_bv_sorts);
        qtbl_name_and_index = (uu___2061_27221.qtbl_name_and_index);
        normalized_eff_names = (uu___2061_27221.normalized_eff_names);
        fv_delta_depths = (uu___2061_27221.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2061_27221.synth_hook);
        try_solve_implicits_hook = (uu___2061_27221.try_solve_implicits_hook);
        splice = (uu___2061_27221.splice);
        mpreprocess = (uu___2061_27221.mpreprocess);
        postprocess = (uu___2061_27221.postprocess);
        identifier_info = (uu___2061_27221.identifier_info);
        tc_hooks = (uu___2061_27221.tc_hooks);
        dsenv = (uu___2061_27221.dsenv);
        nbe = (uu___2061_27221.nbe);
        strict_args_tab = (uu___2061_27221.strict_args_tab);
        erasable_types_tab = (uu___2061_27221.erasable_types_tab);
        enable_defer_to_tac = (uu___2061_27221.enable_defer_to_tac)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____27237 = FStar_Syntax_Free.names t in
      let uu____27240 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____27237 uu____27240
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____27263 = unbound_vars e t in
      FStar_Util.set_is_empty uu____27263
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____27273 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____27273
let (string_of_proof_ns : env -> Prims.string) =
  fun env1 ->
    let aux uu____27294 =
      match uu____27294 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27314 = FStar_Ident.text_of_path p in
             Prims.op_Hat (if b then "+" else "-") uu____27314) in
    let uu____27322 =
      let uu____27326 = FStar_List.map aux env1.proof_ns in
      FStar_All.pipe_right uu____27326 FStar_List.rev in
    FStar_All.pipe_right uu____27322 (FStar_String.concat " ")
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
        FStar_TypeChecker_Common.deferred_to_tac = uu____27382;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([], []);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27400 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu____27400 with
                   | FStar_Pervasives_Native.Some uu____27404 -> true
                   | FStar_Pervasives_Native.None -> false)))
    | uu____27407 -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial;
        FStar_TypeChecker_Common.deferred_to_tac = uu____27417;
        FStar_TypeChecker_Common.deferred = uu____27418;
        FStar_TypeChecker_Common.univ_ineqs = uu____27419;
        FStar_TypeChecker_Common.implicits = uu____27420;_} -> true
    | uu____27430 -> false
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
          let uu___2107_27452 = g in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2107_27452.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2107_27452.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2107_27452.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2107_27452.FStar_TypeChecker_Common.implicits)
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
          let uu____27491 = FStar_Options.defensive () in
          if uu____27491
          then
            let s = FStar_Syntax_Free.names t in
            let uu____27497 =
              let uu____27499 =
                let uu____27501 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27501 in
              Prims.op_Negation uu____27499 in
            (if uu____27497
             then
               let uu____27508 =
                 let uu____27514 =
                   let uu____27516 = FStar_Syntax_Print.term_to_string t in
                   let uu____27518 =
                     let uu____27520 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____27520
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27516 uu____27518 in
                 (FStar_Errors.Warning_Defensive, uu____27514) in
               FStar_Errors.log_issue rng uu____27508
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
          let uu____27560 =
            let uu____27562 = FStar_Options.defensive () in
            Prims.op_Negation uu____27562 in
          if uu____27560
          then ()
          else
            (let uu____27567 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____27567 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____27593 =
            let uu____27595 = FStar_Options.defensive () in
            Prims.op_Negation uu____27595 in
          if uu____27593
          then ()
          else
            (let uu____27600 = bound_vars e in
             def_check_closed_in rng msg uu____27600 t)
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
          let uu___2144_27639 = g in
          let uu____27640 =
            let uu____27641 =
              let uu____27642 =
                let uu____27643 =
                  let uu____27660 =
                    let uu____27671 = FStar_Syntax_Syntax.as_arg e in
                    [uu____27671] in
                  (f, uu____27660) in
                FStar_Syntax_Syntax.Tm_app uu____27643 in
              FStar_Syntax_Syntax.mk uu____27642 f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun uu____27708 ->
                 FStar_TypeChecker_Common.NonTrivial uu____27708) uu____27641 in
          {
            FStar_TypeChecker_Common.guard_f = uu____27640;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2144_27639.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2144_27639.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2144_27639.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2144_27639.FStar_TypeChecker_Common.implicits)
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
          let uu___2151_27726 = g in
          let uu____27727 =
            let uu____27728 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____27728 in
          {
            FStar_TypeChecker_Common.guard_f = uu____27727;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2151_27726.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27726.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27726.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27726.FStar_TypeChecker_Common.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___2156_27745 = g in
          let uu____27746 =
            let uu____27747 = map FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu____27747 in
          {
            FStar_TypeChecker_Common.guard_f = uu____27746;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2156_27745.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27745.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27745.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27745.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2160_27749 = g in
          let uu____27750 =
            let uu____27751 = map f in
            FStar_TypeChecker_Common.NonTrivial uu____27751 in
          {
            FStar_TypeChecker_Common.guard_f = uu____27750;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2160_27749.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2160_27749.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2160_27749.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2160_27749.FStar_TypeChecker_Common.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27758 ->
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
                       let uu____27835 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____27835
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___2183_27842 = g in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2183_27842.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2183_27842.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2183_27842.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2183_27842.FStar_TypeChecker_Common.implicits)
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
               let uu____27876 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____27876
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
            let uu___2198_27903 = g in
            let uu____27904 =
              let uu____27905 = close_forall env1 binders f in
              FStar_TypeChecker_Common.NonTrivial uu____27905 in
            {
              FStar_TypeChecker_Common.guard_f = uu____27904;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2198_27903.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2198_27903.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2198_27903.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2198_27903.FStar_TypeChecker_Common.implicits)
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
              let uu____27955 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
              match uu____27955 with
              | FStar_Pervasives_Native.Some
                  (uu____27980::(tm, uu____27982)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos in
                  (t, [], trivial_guard)
              | uu____28046 ->
                  let binders = all_binders env1 in
                  let gamma = env1.gamma in
                  let ctx_uvar =
                    let uu____28064 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____28064;
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
                    (let uu____28098 =
                       debug env1 (FStar_Options.Other "ImplicitTrace") in
                     if uu____28098
                     then
                       let uu____28102 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____28102
                     else ());
                    (let g =
                       let uu___2222_28108 = trivial_guard in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2222_28108.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2222_28108.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2222_28108.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2222_28108.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____28162 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28220 ->
                      fun b ->
                        match uu____28220 with
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
                                  let uu____28272 =
                                    let uu____28273 =
                                      let uu____28280 = FStar_Dyn.mkdyn env1 in
                                      (uu____28280, t) in
                                    FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                      uu____28273 in
                                  FStar_Pervasives_Native.Some uu____28272
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr t)
                              | uu____28286 -> FStar_Pervasives_Native.None in
                            let uu____28289 =
                              let uu____28302 = reason b in
                              new_implicit_var_aux uu____28302 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                ctx_uvar_meta_t in
                            (match uu____28289 with
                             | (t, uu____28315, g_t) ->
                                 let uu____28329 =
                                   let uu____28332 =
                                     let uu____28335 =
                                       let uu____28336 =
                                         let uu____28343 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst in
                                         (uu____28343, t) in
                                       FStar_Syntax_Syntax.NT uu____28336 in
                                     [uu____28335] in
                                   FStar_List.append substs1 uu____28332 in
                                 let uu____28354 = conj_guard g g_t in
                                 (uu____28329, (FStar_List.append uvars [t]),
                                   uu____28354))) (substs, [], trivial_guard)) in
            FStar_All.pipe_right uu____28162
              (fun uu____28383 ->
                 match uu____28383 with
                 | (uu____28400, uvars, g) -> (uvars, g))
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
                let uu____28441 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid in
                FStar_All.pipe_right uu____28441 FStar_Util.must in
              let uu____28458 = inst_tscheme_with post_ts [u] in
              match uu____28458 with
              | (uu____28463, post) ->
                  let uu____28465 =
                    let uu____28466 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                    [uu____28466] in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____28465 r in
            let uu____28499 =
              let uu____28500 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg in
              [uu____28500] in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____28499 r
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28536 -> ());
    push = (fun uu____28538 -> ());
    pop = (fun uu____28541 -> ());
    snapshot =
      (fun uu____28544 ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28563 -> fun uu____28564 -> ());
    encode_sig = (fun uu____28579 -> fun uu____28580 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____28586 =
             let uu____28593 = FStar_Options.peek () in (e, g, uu____28593) in
           [uu____28586]);
    solve = (fun uu____28609 -> fun uu____28610 -> fun uu____28611 -> ());
    finish = (fun uu____28618 -> ());
    refresh = (fun uu____28620 -> ())
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
        | uu____28729 -> false in
      let uu____28743 =
        FStar_Util.find_opt
          (fun uu____28777 ->
             match uu____28777 with
             | (lbname', uu____28793, uu____28794, uu____28795) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs in
      match uu____28743 with
      | FStar_Pervasives_Native.Some
          (uu____28809, arity, uu____28811, uu____28812) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None