open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____107 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____118 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____129 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____141 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____159 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____170 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____181 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____192 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____203 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____214 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____226 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____247 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____274 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____301 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____325 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____336 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____347 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____358 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____369 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____380 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____391 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____402 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____413 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____424 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____435 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____446 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____457 -> false
  
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
      | (Weak ,Weak ) -> true
      | (HNF ,HNF ) -> true
      | (Primops ,Primops ) -> true
      | (Eager_unfolding ,Eager_unfolding ) -> true
      | (Inlining ,Inlining ) -> true
      | (DoNotUnfoldPureLets ,DoNotUnfoldPureLets ) -> true
      | (UnfoldTac ,UnfoldTac ) -> true
      | (PureSubtermsWithinComputations ,PureSubtermsWithinComputations ) ->
          true
      | (Simplify ,Simplify ) -> true
      | (EraseUniverses ,EraseUniverses ) -> true
      | (AllowUnboundUniverses ,AllowUnboundUniverses ) -> true
      | (Reify ,Reify ) -> true
      | (CompressUvars ,CompressUvars ) -> true
      | (NoFullNorm ,NoFullNorm ) -> true
      | (CheckNoUvars ,CheckNoUvars ) -> true
      | (Unmeta ,Unmeta ) -> true
      | (Unascribe ,Unascribe ) -> true
      | (NBE ,NBE ) -> true
      | (Exclude s11,Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11,UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1,UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1,UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr lids1,UnfoldAttr lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | uu____517 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____543 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____554 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____565 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____577 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
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
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
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
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
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
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
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
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_term
  
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mlift
  
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> polymonadic_binds
  
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> use_eq
  
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        use_eq_strict
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        splice1
  
let (__proj__Mkenv__item__mpreprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        mpreprocess
  
let (__proj__Mkenv__item__postprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> dsenv
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        erasable_types_tab
  
let (__proj__Mkenv__item__enable_defer_to_tac : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab; enable_defer_to_tac;_} ->
        enable_defer_to_tac
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> init1
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> push1
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> pop1
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> snapshot1
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> rollback1
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> finish1
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> refresh
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
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
  = fun env  -> fun tau  -> fun tm  -> env.mpreprocess env tau tm 
let (postprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  -> fun tau  -> fun ty  -> fun tm  -> env.postprocess env tau ty tm 
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___0_14694  ->
              match uu___0_14694 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14697 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14697  in
                  let uu____14698 =
                    let uu____14699 = FStar_Syntax_Subst.compress y  in
                    uu____14699.FStar_Syntax_Syntax.n  in
                  (match uu____14698 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14703 =
                         let uu___327_14704 = y1  in
                         let uu____14705 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14704.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14704.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14705
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14703
                   | uu____14708 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___333_14722 = env  in
      let uu____14723 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___333_14722.solver);
        range = (uu___333_14722.range);
        curmodule = (uu___333_14722.curmodule);
        gamma = uu____14723;
        gamma_sig = (uu___333_14722.gamma_sig);
        gamma_cache = (uu___333_14722.gamma_cache);
        modules = (uu___333_14722.modules);
        expected_typ = (uu___333_14722.expected_typ);
        sigtab = (uu___333_14722.sigtab);
        attrtab = (uu___333_14722.attrtab);
        instantiate_imp = (uu___333_14722.instantiate_imp);
        effects = (uu___333_14722.effects);
        generalize = (uu___333_14722.generalize);
        letrecs = (uu___333_14722.letrecs);
        top_level = (uu___333_14722.top_level);
        check_uvars = (uu___333_14722.check_uvars);
        use_eq = (uu___333_14722.use_eq);
        use_eq_strict = (uu___333_14722.use_eq_strict);
        is_iface = (uu___333_14722.is_iface);
        admit = (uu___333_14722.admit);
        lax = (uu___333_14722.lax);
        lax_universes = (uu___333_14722.lax_universes);
        phase1 = (uu___333_14722.phase1);
        failhard = (uu___333_14722.failhard);
        nosynth = (uu___333_14722.nosynth);
        uvar_subtyping = (uu___333_14722.uvar_subtyping);
        tc_term = (uu___333_14722.tc_term);
        type_of = (uu___333_14722.type_of);
        universe_of = (uu___333_14722.universe_of);
        check_type_of = (uu___333_14722.check_type_of);
        use_bv_sorts = (uu___333_14722.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14722.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14722.normalized_eff_names);
        fv_delta_depths = (uu___333_14722.fv_delta_depths);
        proof_ns = (uu___333_14722.proof_ns);
        synth_hook = (uu___333_14722.synth_hook);
        try_solve_implicits_hook = (uu___333_14722.try_solve_implicits_hook);
        splice = (uu___333_14722.splice);
        mpreprocess = (uu___333_14722.mpreprocess);
        postprocess = (uu___333_14722.postprocess);
        is_native_tactic = (uu___333_14722.is_native_tactic);
        identifier_info = (uu___333_14722.identifier_info);
        tc_hooks = (uu___333_14722.tc_hooks);
        dsenv = (uu___333_14722.dsenv);
        nbe = (uu___333_14722.nbe);
        strict_args_tab = (uu___333_14722.strict_args_tab);
        erasable_types_tab = (uu___333_14722.erasable_types_tab);
        enable_defer_to_tac = (uu___333_14722.enable_defer_to_tac)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14731  -> fun uu____14732  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___340_14754 = env  in
      {
        solver = (uu___340_14754.solver);
        range = (uu___340_14754.range);
        curmodule = (uu___340_14754.curmodule);
        gamma = (uu___340_14754.gamma);
        gamma_sig = (uu___340_14754.gamma_sig);
        gamma_cache = (uu___340_14754.gamma_cache);
        modules = (uu___340_14754.modules);
        expected_typ = (uu___340_14754.expected_typ);
        sigtab = (uu___340_14754.sigtab);
        attrtab = (uu___340_14754.attrtab);
        instantiate_imp = (uu___340_14754.instantiate_imp);
        effects = (uu___340_14754.effects);
        generalize = (uu___340_14754.generalize);
        letrecs = (uu___340_14754.letrecs);
        top_level = (uu___340_14754.top_level);
        check_uvars = (uu___340_14754.check_uvars);
        use_eq = (uu___340_14754.use_eq);
        use_eq_strict = (uu___340_14754.use_eq_strict);
        is_iface = (uu___340_14754.is_iface);
        admit = (uu___340_14754.admit);
        lax = (uu___340_14754.lax);
        lax_universes = (uu___340_14754.lax_universes);
        phase1 = (uu___340_14754.phase1);
        failhard = (uu___340_14754.failhard);
        nosynth = (uu___340_14754.nosynth);
        uvar_subtyping = (uu___340_14754.uvar_subtyping);
        tc_term = (uu___340_14754.tc_term);
        type_of = (uu___340_14754.type_of);
        universe_of = (uu___340_14754.universe_of);
        check_type_of = (uu___340_14754.check_type_of);
        use_bv_sorts = (uu___340_14754.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14754.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14754.normalized_eff_names);
        fv_delta_depths = (uu___340_14754.fv_delta_depths);
        proof_ns = (uu___340_14754.proof_ns);
        synth_hook = (uu___340_14754.synth_hook);
        try_solve_implicits_hook = (uu___340_14754.try_solve_implicits_hook);
        splice = (uu___340_14754.splice);
        mpreprocess = (uu___340_14754.mpreprocess);
        postprocess = (uu___340_14754.postprocess);
        is_native_tactic = (uu___340_14754.is_native_tactic);
        identifier_info = (uu___340_14754.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14754.dsenv);
        nbe = (uu___340_14754.nbe);
        strict_args_tab = (uu___340_14754.strict_args_tab);
        erasable_types_tab = (uu___340_14754.erasable_types_tab);
        enable_defer_to_tac = (uu___340_14754.enable_defer_to_tac)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___344_14766 = e  in
      let uu____14767 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___344_14766.solver);
        range = (uu___344_14766.range);
        curmodule = (uu___344_14766.curmodule);
        gamma = (uu___344_14766.gamma);
        gamma_sig = (uu___344_14766.gamma_sig);
        gamma_cache = (uu___344_14766.gamma_cache);
        modules = (uu___344_14766.modules);
        expected_typ = (uu___344_14766.expected_typ);
        sigtab = (uu___344_14766.sigtab);
        attrtab = (uu___344_14766.attrtab);
        instantiate_imp = (uu___344_14766.instantiate_imp);
        effects = (uu___344_14766.effects);
        generalize = (uu___344_14766.generalize);
        letrecs = (uu___344_14766.letrecs);
        top_level = (uu___344_14766.top_level);
        check_uvars = (uu___344_14766.check_uvars);
        use_eq = (uu___344_14766.use_eq);
        use_eq_strict = (uu___344_14766.use_eq_strict);
        is_iface = (uu___344_14766.is_iface);
        admit = (uu___344_14766.admit);
        lax = (uu___344_14766.lax);
        lax_universes = (uu___344_14766.lax_universes);
        phase1 = (uu___344_14766.phase1);
        failhard = (uu___344_14766.failhard);
        nosynth = (uu___344_14766.nosynth);
        uvar_subtyping = (uu___344_14766.uvar_subtyping);
        tc_term = (uu___344_14766.tc_term);
        type_of = (uu___344_14766.type_of);
        universe_of = (uu___344_14766.universe_of);
        check_type_of = (uu___344_14766.check_type_of);
        use_bv_sorts = (uu___344_14766.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14766.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14766.normalized_eff_names);
        fv_delta_depths = (uu___344_14766.fv_delta_depths);
        proof_ns = (uu___344_14766.proof_ns);
        synth_hook = (uu___344_14766.synth_hook);
        try_solve_implicits_hook = (uu___344_14766.try_solve_implicits_hook);
        splice = (uu___344_14766.splice);
        mpreprocess = (uu___344_14766.mpreprocess);
        postprocess = (uu___344_14766.postprocess);
        is_native_tactic = (uu___344_14766.is_native_tactic);
        identifier_info = (uu___344_14766.identifier_info);
        tc_hooks = (uu___344_14766.tc_hooks);
        dsenv = uu____14767;
        nbe = (uu___344_14766.nbe);
        strict_args_tab = (uu___344_14766.strict_args_tab);
        erasable_types_tab = (uu___344_14766.erasable_types_tab);
        enable_defer_to_tac = (uu___344_14766.enable_defer_to_tac)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14796) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14799,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14801,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14804 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14818 . unit -> 'Auu____14818 FStar_Util.smap =
  fun uu____14825  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14831 . unit -> 'Auu____14831 FStar_Util.smap =
  fun uu____14838  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun check_type_of  ->
            fun solver  ->
              fun module_lid  ->
                fun nbe1  ->
                  let uu____14976 = new_gamma_cache ()  in
                  let uu____14979 = new_sigtab ()  in
                  let uu____14982 = new_sigtab ()  in
                  let uu____14989 =
                    let uu____15004 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____15004, FStar_Pervasives_Native.None)  in
                  let uu____15025 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____15029 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____15033 = FStar_Options.using_facts_from ()  in
                  let uu____15034 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____15037 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____15038 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____15052 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14976;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14979;
                    attrtab = uu____14982;
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
                    qtbl_name_and_index = uu____14989;
                    normalized_eff_names = uu____15025;
                    fv_delta_depths = uu____15029;
                    proof_ns = uu____15033;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    try_solve_implicits_hook =
                      (fun e  ->
                         fun tau  ->
                           fun imps  -> failwith "no implicit hook available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    mpreprocess =
                      (fun e  ->
                         fun tau  ->
                           fun tm  -> failwith "no preprocessor available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____15167  -> false);
                    identifier_info = uu____15034;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____15037;
                    nbe = nbe1;
                    strict_args_tab = uu____15038;
                    erasable_types_tab = uu____15052;
                    enable_defer_to_tac = true
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____15247  ->
    let uu____15248 = FStar_ST.op_Bang query_indices  in
    match uu____15248 with
    | [] -> failwith "Empty query indices!"
    | uu____15303 ->
        let uu____15313 =
          let uu____15323 =
            let uu____15331 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____15331  in
          let uu____15385 = FStar_ST.op_Bang query_indices  in uu____15323 ::
            uu____15385
           in
        FStar_ST.op_Colon_Equals query_indices uu____15313
  
let (pop_query_indices : unit -> unit) =
  fun uu____15481  ->
    let uu____15482 = FStar_ST.op_Bang query_indices  in
    match uu____15482 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15609  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15646  ->
    match uu____15646 with
    | (l,n1) ->
        let uu____15656 = FStar_ST.op_Bang query_indices  in
        (match uu____15656 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15778 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15801  ->
    let uu____15802 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15802
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15870 =
       let uu____15873 = FStar_ST.op_Bang stack  in env :: uu____15873  in
     FStar_ST.op_Colon_Equals stack uu____15870);
    (let uu___418_15922 = env  in
     let uu____15923 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15926 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15929 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15936 =
       let uu____15951 =
         let uu____15955 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15955  in
       let uu____15987 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15951, uu____15987)  in
     let uu____16036 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____16039 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____16042 =
       let uu____16045 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____16045  in
     let uu____16065 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____16078 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___418_15922.solver);
       range = (uu___418_15922.range);
       curmodule = (uu___418_15922.curmodule);
       gamma = (uu___418_15922.gamma);
       gamma_sig = (uu___418_15922.gamma_sig);
       gamma_cache = uu____15923;
       modules = (uu___418_15922.modules);
       expected_typ = (uu___418_15922.expected_typ);
       sigtab = uu____15926;
       attrtab = uu____15929;
       instantiate_imp = (uu___418_15922.instantiate_imp);
       effects = (uu___418_15922.effects);
       generalize = (uu___418_15922.generalize);
       letrecs = (uu___418_15922.letrecs);
       top_level = (uu___418_15922.top_level);
       check_uvars = (uu___418_15922.check_uvars);
       use_eq = (uu___418_15922.use_eq);
       use_eq_strict = (uu___418_15922.use_eq_strict);
       is_iface = (uu___418_15922.is_iface);
       admit = (uu___418_15922.admit);
       lax = (uu___418_15922.lax);
       lax_universes = (uu___418_15922.lax_universes);
       phase1 = (uu___418_15922.phase1);
       failhard = (uu___418_15922.failhard);
       nosynth = (uu___418_15922.nosynth);
       uvar_subtyping = (uu___418_15922.uvar_subtyping);
       tc_term = (uu___418_15922.tc_term);
       type_of = (uu___418_15922.type_of);
       universe_of = (uu___418_15922.universe_of);
       check_type_of = (uu___418_15922.check_type_of);
       use_bv_sorts = (uu___418_15922.use_bv_sorts);
       qtbl_name_and_index = uu____15936;
       normalized_eff_names = uu____16036;
       fv_delta_depths = uu____16039;
       proof_ns = (uu___418_15922.proof_ns);
       synth_hook = (uu___418_15922.synth_hook);
       try_solve_implicits_hook = (uu___418_15922.try_solve_implicits_hook);
       splice = (uu___418_15922.splice);
       mpreprocess = (uu___418_15922.mpreprocess);
       postprocess = (uu___418_15922.postprocess);
       is_native_tactic = (uu___418_15922.is_native_tactic);
       identifier_info = uu____16042;
       tc_hooks = (uu___418_15922.tc_hooks);
       dsenv = (uu___418_15922.dsenv);
       nbe = (uu___418_15922.nbe);
       strict_args_tab = uu____16065;
       erasable_types_tab = uu____16078;
       enable_defer_to_tac = (uu___418_15922.enable_defer_to_tac)
     })
  
let (pop_stack : unit -> env) =
  fun uu____16088  ->
    let uu____16089 = FStar_ST.op_Bang stack  in
    match uu____16089 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____16143 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____16233  ->
           let uu____16234 = snapshot_stack env  in
           match uu____16234 with
           | (stack_depth,env1) ->
               let uu____16268 = snapshot_query_indices ()  in
               (match uu____16268 with
                | (query_indices_depth,()) ->
                    let uu____16301 = (env1.solver).snapshot msg  in
                    (match uu____16301 with
                     | (solver_depth,()) ->
                         let uu____16358 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____16358 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_16425 = env1  in
                                 {
                                   solver = (uu___443_16425.solver);
                                   range = (uu___443_16425.range);
                                   curmodule = (uu___443_16425.curmodule);
                                   gamma = (uu___443_16425.gamma);
                                   gamma_sig = (uu___443_16425.gamma_sig);
                                   gamma_cache = (uu___443_16425.gamma_cache);
                                   modules = (uu___443_16425.modules);
                                   expected_typ =
                                     (uu___443_16425.expected_typ);
                                   sigtab = (uu___443_16425.sigtab);
                                   attrtab = (uu___443_16425.attrtab);
                                   instantiate_imp =
                                     (uu___443_16425.instantiate_imp);
                                   effects = (uu___443_16425.effects);
                                   generalize = (uu___443_16425.generalize);
                                   letrecs = (uu___443_16425.letrecs);
                                   top_level = (uu___443_16425.top_level);
                                   check_uvars = (uu___443_16425.check_uvars);
                                   use_eq = (uu___443_16425.use_eq);
                                   use_eq_strict =
                                     (uu___443_16425.use_eq_strict);
                                   is_iface = (uu___443_16425.is_iface);
                                   admit = (uu___443_16425.admit);
                                   lax = (uu___443_16425.lax);
                                   lax_universes =
                                     (uu___443_16425.lax_universes);
                                   phase1 = (uu___443_16425.phase1);
                                   failhard = (uu___443_16425.failhard);
                                   nosynth = (uu___443_16425.nosynth);
                                   uvar_subtyping =
                                     (uu___443_16425.uvar_subtyping);
                                   tc_term = (uu___443_16425.tc_term);
                                   type_of = (uu___443_16425.type_of);
                                   universe_of = (uu___443_16425.universe_of);
                                   check_type_of =
                                     (uu___443_16425.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_16425.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_16425.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_16425.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_16425.fv_delta_depths);
                                   proof_ns = (uu___443_16425.proof_ns);
                                   synth_hook = (uu___443_16425.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_16425.try_solve_implicits_hook);
                                   splice = (uu___443_16425.splice);
                                   mpreprocess = (uu___443_16425.mpreprocess);
                                   postprocess = (uu___443_16425.postprocess);
                                   is_native_tactic =
                                     (uu___443_16425.is_native_tactic);
                                   identifier_info =
                                     (uu___443_16425.identifier_info);
                                   tc_hooks = (uu___443_16425.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_16425.nbe);
                                   strict_args_tab =
                                     (uu___443_16425.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_16425.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___443_16425.enable_defer_to_tac)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16459  ->
             let uu____16460 =
               match depth with
               | FStar_Pervasives_Native.Some (s1,s2,s3,s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None  ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None)
                in
             match uu____16460 with
             | (stack_depth,query_indices_depth,solver_depth,dsenv_depth) ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth  in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth  in
                             ((let uu____16640 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16640
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____16656 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____16656
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16688,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16730 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16760  ->
                  match uu____16760 with
                  | (m,uu____16768) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16730 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___488_16783 = env  in
               {
                 solver = (uu___488_16783.solver);
                 range = (uu___488_16783.range);
                 curmodule = (uu___488_16783.curmodule);
                 gamma = (uu___488_16783.gamma);
                 gamma_sig = (uu___488_16783.gamma_sig);
                 gamma_cache = (uu___488_16783.gamma_cache);
                 modules = (uu___488_16783.modules);
                 expected_typ = (uu___488_16783.expected_typ);
                 sigtab = (uu___488_16783.sigtab);
                 attrtab = (uu___488_16783.attrtab);
                 instantiate_imp = (uu___488_16783.instantiate_imp);
                 effects = (uu___488_16783.effects);
                 generalize = (uu___488_16783.generalize);
                 letrecs = (uu___488_16783.letrecs);
                 top_level = (uu___488_16783.top_level);
                 check_uvars = (uu___488_16783.check_uvars);
                 use_eq = (uu___488_16783.use_eq);
                 use_eq_strict = (uu___488_16783.use_eq_strict);
                 is_iface = (uu___488_16783.is_iface);
                 admit = (uu___488_16783.admit);
                 lax = (uu___488_16783.lax);
                 lax_universes = (uu___488_16783.lax_universes);
                 phase1 = (uu___488_16783.phase1);
                 failhard = (uu___488_16783.failhard);
                 nosynth = (uu___488_16783.nosynth);
                 uvar_subtyping = (uu___488_16783.uvar_subtyping);
                 tc_term = (uu___488_16783.tc_term);
                 type_of = (uu___488_16783.type_of);
                 universe_of = (uu___488_16783.universe_of);
                 check_type_of = (uu___488_16783.check_type_of);
                 use_bv_sorts = (uu___488_16783.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16783.normalized_eff_names);
                 fv_delta_depths = (uu___488_16783.fv_delta_depths);
                 proof_ns = (uu___488_16783.proof_ns);
                 synth_hook = (uu___488_16783.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16783.try_solve_implicits_hook);
                 splice = (uu___488_16783.splice);
                 mpreprocess = (uu___488_16783.mpreprocess);
                 postprocess = (uu___488_16783.postprocess);
                 is_native_tactic = (uu___488_16783.is_native_tactic);
                 identifier_info = (uu___488_16783.identifier_info);
                 tc_hooks = (uu___488_16783.tc_hooks);
                 dsenv = (uu___488_16783.dsenv);
                 nbe = (uu___488_16783.nbe);
                 strict_args_tab = (uu___488_16783.strict_args_tab);
                 erasable_types_tab = (uu___488_16783.erasable_types_tab);
                 enable_defer_to_tac = (uu___488_16783.enable_defer_to_tac)
               }))
         | FStar_Pervasives_Native.Some (uu____16800,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___497_16816 = env  in
               {
                 solver = (uu___497_16816.solver);
                 range = (uu___497_16816.range);
                 curmodule = (uu___497_16816.curmodule);
                 gamma = (uu___497_16816.gamma);
                 gamma_sig = (uu___497_16816.gamma_sig);
                 gamma_cache = (uu___497_16816.gamma_cache);
                 modules = (uu___497_16816.modules);
                 expected_typ = (uu___497_16816.expected_typ);
                 sigtab = (uu___497_16816.sigtab);
                 attrtab = (uu___497_16816.attrtab);
                 instantiate_imp = (uu___497_16816.instantiate_imp);
                 effects = (uu___497_16816.effects);
                 generalize = (uu___497_16816.generalize);
                 letrecs = (uu___497_16816.letrecs);
                 top_level = (uu___497_16816.top_level);
                 check_uvars = (uu___497_16816.check_uvars);
                 use_eq = (uu___497_16816.use_eq);
                 use_eq_strict = (uu___497_16816.use_eq_strict);
                 is_iface = (uu___497_16816.is_iface);
                 admit = (uu___497_16816.admit);
                 lax = (uu___497_16816.lax);
                 lax_universes = (uu___497_16816.lax_universes);
                 phase1 = (uu___497_16816.phase1);
                 failhard = (uu___497_16816.failhard);
                 nosynth = (uu___497_16816.nosynth);
                 uvar_subtyping = (uu___497_16816.uvar_subtyping);
                 tc_term = (uu___497_16816.tc_term);
                 type_of = (uu___497_16816.type_of);
                 universe_of = (uu___497_16816.universe_of);
                 check_type_of = (uu___497_16816.check_type_of);
                 use_bv_sorts = (uu___497_16816.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16816.normalized_eff_names);
                 fv_delta_depths = (uu___497_16816.fv_delta_depths);
                 proof_ns = (uu___497_16816.proof_ns);
                 synth_hook = (uu___497_16816.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16816.try_solve_implicits_hook);
                 splice = (uu___497_16816.splice);
                 mpreprocess = (uu___497_16816.mpreprocess);
                 postprocess = (uu___497_16816.postprocess);
                 is_native_tactic = (uu___497_16816.is_native_tactic);
                 identifier_info = (uu___497_16816.identifier_info);
                 tc_hooks = (uu___497_16816.tc_hooks);
                 dsenv = (uu___497_16816.dsenv);
                 nbe = (uu___497_16816.nbe);
                 strict_args_tab = (uu___497_16816.strict_args_tab);
                 erasable_types_tab = (uu___497_16816.erasable_types_tab);
                 enable_defer_to_tac = (uu___497_16816.enable_defer_to_tac)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___504_16859 = e  in
         {
           solver = (uu___504_16859.solver);
           range = r;
           curmodule = (uu___504_16859.curmodule);
           gamma = (uu___504_16859.gamma);
           gamma_sig = (uu___504_16859.gamma_sig);
           gamma_cache = (uu___504_16859.gamma_cache);
           modules = (uu___504_16859.modules);
           expected_typ = (uu___504_16859.expected_typ);
           sigtab = (uu___504_16859.sigtab);
           attrtab = (uu___504_16859.attrtab);
           instantiate_imp = (uu___504_16859.instantiate_imp);
           effects = (uu___504_16859.effects);
           generalize = (uu___504_16859.generalize);
           letrecs = (uu___504_16859.letrecs);
           top_level = (uu___504_16859.top_level);
           check_uvars = (uu___504_16859.check_uvars);
           use_eq = (uu___504_16859.use_eq);
           use_eq_strict = (uu___504_16859.use_eq_strict);
           is_iface = (uu___504_16859.is_iface);
           admit = (uu___504_16859.admit);
           lax = (uu___504_16859.lax);
           lax_universes = (uu___504_16859.lax_universes);
           phase1 = (uu___504_16859.phase1);
           failhard = (uu___504_16859.failhard);
           nosynth = (uu___504_16859.nosynth);
           uvar_subtyping = (uu___504_16859.uvar_subtyping);
           tc_term = (uu___504_16859.tc_term);
           type_of = (uu___504_16859.type_of);
           universe_of = (uu___504_16859.universe_of);
           check_type_of = (uu___504_16859.check_type_of);
           use_bv_sorts = (uu___504_16859.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16859.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16859.normalized_eff_names);
           fv_delta_depths = (uu___504_16859.fv_delta_depths);
           proof_ns = (uu___504_16859.proof_ns);
           synth_hook = (uu___504_16859.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16859.try_solve_implicits_hook);
           splice = (uu___504_16859.splice);
           mpreprocess = (uu___504_16859.mpreprocess);
           postprocess = (uu___504_16859.postprocess);
           is_native_tactic = (uu___504_16859.is_native_tactic);
           identifier_info = (uu___504_16859.identifier_info);
           tc_hooks = (uu___504_16859.tc_hooks);
           dsenv = (uu___504_16859.dsenv);
           nbe = (uu___504_16859.nbe);
           strict_args_tab = (uu___504_16859.strict_args_tab);
           erasable_types_tab = (uu___504_16859.erasable_types_tab);
           enable_defer_to_tac = (uu___504_16859.enable_defer_to_tac)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16879 =
        let uu____16880 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16880 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16879
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16935 =
          let uu____16936 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16936 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16935
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16991 =
          let uu____16992 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16992 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16991
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____17047 =
        let uu____17048 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____17048 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____17047
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___521_17112 = env  in
      {
        solver = (uu___521_17112.solver);
        range = (uu___521_17112.range);
        curmodule = lid;
        gamma = (uu___521_17112.gamma);
        gamma_sig = (uu___521_17112.gamma_sig);
        gamma_cache = (uu___521_17112.gamma_cache);
        modules = (uu___521_17112.modules);
        expected_typ = (uu___521_17112.expected_typ);
        sigtab = (uu___521_17112.sigtab);
        attrtab = (uu___521_17112.attrtab);
        instantiate_imp = (uu___521_17112.instantiate_imp);
        effects = (uu___521_17112.effects);
        generalize = (uu___521_17112.generalize);
        letrecs = (uu___521_17112.letrecs);
        top_level = (uu___521_17112.top_level);
        check_uvars = (uu___521_17112.check_uvars);
        use_eq = (uu___521_17112.use_eq);
        use_eq_strict = (uu___521_17112.use_eq_strict);
        is_iface = (uu___521_17112.is_iface);
        admit = (uu___521_17112.admit);
        lax = (uu___521_17112.lax);
        lax_universes = (uu___521_17112.lax_universes);
        phase1 = (uu___521_17112.phase1);
        failhard = (uu___521_17112.failhard);
        nosynth = (uu___521_17112.nosynth);
        uvar_subtyping = (uu___521_17112.uvar_subtyping);
        tc_term = (uu___521_17112.tc_term);
        type_of = (uu___521_17112.type_of);
        universe_of = (uu___521_17112.universe_of);
        check_type_of = (uu___521_17112.check_type_of);
        use_bv_sorts = (uu___521_17112.use_bv_sorts);
        qtbl_name_and_index = (uu___521_17112.qtbl_name_and_index);
        normalized_eff_names = (uu___521_17112.normalized_eff_names);
        fv_delta_depths = (uu___521_17112.fv_delta_depths);
        proof_ns = (uu___521_17112.proof_ns);
        synth_hook = (uu___521_17112.synth_hook);
        try_solve_implicits_hook = (uu___521_17112.try_solve_implicits_hook);
        splice = (uu___521_17112.splice);
        mpreprocess = (uu___521_17112.mpreprocess);
        postprocess = (uu___521_17112.postprocess);
        is_native_tactic = (uu___521_17112.is_native_tactic);
        identifier_info = (uu___521_17112.identifier_info);
        tc_hooks = (uu___521_17112.tc_hooks);
        dsenv = (uu___521_17112.dsenv);
        nbe = (uu___521_17112.nbe);
        strict_args_tab = (uu___521_17112.strict_args_tab);
        erasable_types_tab = (uu___521_17112.erasable_types_tab);
        enable_defer_to_tac = (uu___521_17112.enable_defer_to_tac)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17143 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____17143
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____17156 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____17156)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____17171 =
      let uu____17173 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____17173  in
    (FStar_Errors.Fatal_VariableNotFound, uu____17171)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____17182  ->
    let uu____17183 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____17183
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - Prims.int_one  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____17283) ->
          let vs = mk_univ_subst formals us  in
          let uu____17307 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____17307)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17324  ->
    match uu___1_17324 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17350  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17370 = inst_tscheme t  in
      match uu____17370 with
      | (us,t1) ->
          let uu____17381 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17381)
  
let (check_effect_is_not_a_template :
  FStar_Syntax_Syntax.eff_decl -> FStar_Range.range -> unit) =
  fun ed  ->
    fun rng  ->
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        let msg =
          let uu____17406 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17408 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17406 uu____17408
           in
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect, msg) rng
      else ()
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____17435  ->
          match uu____17435 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17449 =
                    let uu____17451 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17455 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17459 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17461 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17451 uu____17455 uu____17459 uu____17461
                     in
                  failwith uu____17449)
               else ();
               (let uu____17466 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17466))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17484 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17495 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17506 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____17554) -> Maybe
             | (uu____17561,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____17581 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17675 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____17675 with
          | FStar_Pervasives_Native.None  ->
              let uu____17698 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17742  ->
                     match uu___2_17742 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17781 = FStar_Ident.lid_equals lid l  in
                         if uu____17781
                         then
                           let uu____17804 =
                             let uu____17823 =
                               let uu____17838 = inst_tscheme t  in
                               FStar_Util.Inl uu____17838  in
                             let uu____17853 = FStar_Ident.range_of_lid l  in
                             (uu____17823, uu____17853)  in
                           FStar_Pervasives_Native.Some uu____17804
                         else FStar_Pervasives_Native.None
                     | uu____17906 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17698
                (fun uu____17944  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17954  ->
                        match uu___3_17954 with
                        | (uu____17957,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17959);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17960;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17961;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17962;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17963;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17964;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17986 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17986
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids,s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____18038 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____18045 -> cache t  in
                            let uu____18046 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____18046 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____18052 =
                                   let uu____18053 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____18053)
                                    in
                                 maybe_cache uu____18052)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____18124 = find_in_sigtab env lid  in
         match uu____18124 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18205 = lookup_qname env lid  in
      match uu____18205 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____18226,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____18340 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____18340 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18385 =
          let uu____18388 = lookup_attr env1 attr  in se1 :: uu____18388  in
        FStar_Util.smap_add (attrtab env1) attr uu____18385  in
      FStar_List.iter
        (fun attr  ->
           let uu____18398 =
             let uu____18399 = FStar_Syntax_Subst.compress attr  in
             uu____18399.FStar_Syntax_Syntax.n  in
           match uu____18398 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18403 =
                 let uu____18405 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18405.FStar_Ident.str  in
               add_one1 env se uu____18403
           | uu____18406 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18429) ->
          add_sigelts env ses
      | uu____18438 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se)

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Range.range)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___4_18476  ->
           match uu___4_18476 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18494 -> FStar_Pervasives_Native.None)
  
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
          FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____18556,lb::[]),uu____18558) ->
            let uu____18567 =
              let uu____18576 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18585 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18576, uu____18585)  in
            FStar_Pervasives_Native.Some uu____18567
        | FStar_Syntax_Syntax.Sig_let ((uu____18598,lbs),uu____18600) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18632 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18645 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18645
                     then
                       let uu____18658 =
                         let uu____18667 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18676 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18667, uu____18676)  in
                       FStar_Pervasives_Native.Some uu____18658
                     else FStar_Pervasives_Native.None)
        | uu____18699 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Range.range ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
          FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun rng  ->
        let inst_ts us_opt1 ts =
          match us_opt1 with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_new_effect ne ->
            (check_effect_is_not_a_template ne rng;
             (match us_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some us ->
                  if
                    (FStar_List.length us) <>
                      (FStar_List.length
                         (FStar_Pervasives_Native.fst
                            ne.FStar_Syntax_Syntax.signature))
                  then
                    let uu____18791 =
                      let uu____18793 =
                        let uu____18795 =
                          let uu____18797 =
                            let uu____18799 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18805 =
                              let uu____18807 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18807  in
                            Prims.op_Hat uu____18799 uu____18805  in
                          Prims.op_Hat ", expected " uu____18797  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18795
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18793
                       in
                    failwith uu____18791
                  else ());
             (let uu____18814 =
                let uu____18823 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18823, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18814))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18843,uu____18844) ->
            let uu____18849 =
              let uu____18858 =
                let uu____18863 =
                  let uu____18864 =
                    let uu____18867 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18867  in
                  (us, uu____18864)  in
                inst_ts us_opt uu____18863  in
              (uu____18858, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18849
        | uu____18886 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____18975 =
          match uu____18975 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____19071,uvs,t,uu____19074,uu____19075,uu____19076);
                      FStar_Syntax_Syntax.sigrng = uu____19077;
                      FStar_Syntax_Syntax.sigquals = uu____19078;
                      FStar_Syntax_Syntax.sigmeta = uu____19079;
                      FStar_Syntax_Syntax.sigattrs = uu____19080;
                      FStar_Syntax_Syntax.sigopts = uu____19081;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____19106 =
                     let uu____19115 = inst_tscheme1 (uvs, t)  in
                     (uu____19115, rng)  in
                   FStar_Pervasives_Native.Some uu____19106
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____19139;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____19141;
                      FStar_Syntax_Syntax.sigattrs = uu____19142;
                      FStar_Syntax_Syntax.sigopts = uu____19143;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____19162 =
                     let uu____19164 = in_cur_mod env l  in uu____19164 = Yes
                      in
                   if uu____19162
                   then
                     let uu____19176 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____19176
                      then
                        let uu____19192 =
                          let uu____19201 = inst_tscheme1 (uvs, t)  in
                          (uu____19201, rng)  in
                        FStar_Pervasives_Native.Some uu____19192
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____19234 =
                        let uu____19243 = inst_tscheme1 (uvs, t)  in
                        (uu____19243, rng)  in
                      FStar_Pervasives_Native.Some uu____19234)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19268,uu____19269);
                      FStar_Syntax_Syntax.sigrng = uu____19270;
                      FStar_Syntax_Syntax.sigquals = uu____19271;
                      FStar_Syntax_Syntax.sigmeta = uu____19272;
                      FStar_Syntax_Syntax.sigattrs = uu____19273;
                      FStar_Syntax_Syntax.sigopts = uu____19274;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____19317 =
                          let uu____19326 = inst_tscheme1 (uvs, k)  in
                          (uu____19326, rng)  in
                        FStar_Pervasives_Native.Some uu____19317
                    | uu____19347 ->
                        let uu____19348 =
                          let uu____19357 =
                            let uu____19362 =
                              let uu____19363 =
                                let uu____19366 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19366
                                 in
                              (uvs, uu____19363)  in
                            inst_tscheme1 uu____19362  in
                          (uu____19357, rng)  in
                        FStar_Pervasives_Native.Some uu____19348)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19389,uu____19390);
                      FStar_Syntax_Syntax.sigrng = uu____19391;
                      FStar_Syntax_Syntax.sigquals = uu____19392;
                      FStar_Syntax_Syntax.sigmeta = uu____19393;
                      FStar_Syntax_Syntax.sigattrs = uu____19394;
                      FStar_Syntax_Syntax.sigopts = uu____19395;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19439 =
                          let uu____19448 = inst_tscheme_with (uvs, k) us  in
                          (uu____19448, rng)  in
                        FStar_Pervasives_Native.Some uu____19439
                    | uu____19469 ->
                        let uu____19470 =
                          let uu____19479 =
                            let uu____19484 =
                              let uu____19485 =
                                let uu____19488 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19488
                                 in
                              (uvs, uu____19485)  in
                            inst_tscheme_with uu____19484 us  in
                          (uu____19479, rng)  in
                        FStar_Pervasives_Native.Some uu____19470)
               | FStar_Util.Inr se ->
                   let uu____19524 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19545;
                          FStar_Syntax_Syntax.sigrng = uu____19546;
                          FStar_Syntax_Syntax.sigquals = uu____19547;
                          FStar_Syntax_Syntax.sigmeta = uu____19548;
                          FStar_Syntax_Syntax.sigattrs = uu____19549;
                          FStar_Syntax_Syntax.sigopts = uu____19550;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19567 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19524
                     (FStar_Util.map_option
                        (fun uu____19615  ->
                           match uu____19615 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19646 =
          let uu____19657 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19657 mapper  in
        match uu____19646 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19731 =
              let uu____19742 =
                let uu____19749 =
                  let uu___858_19752 = t  in
                  let uu____19753 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19752.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19753;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19752.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19749)  in
              (uu____19742, r)  in
            FStar_Pervasives_Native.Some uu____19731
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19802 = lookup_qname env l  in
      match uu____19802 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19823 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19877 = try_lookup_bv env bv  in
      match uu____19877 with
      | FStar_Pervasives_Native.None  ->
          let uu____19892 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19892 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19908 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19909 =
            let uu____19910 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19910  in
          (uu____19908, uu____19909)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19932 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19932 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19998 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19998  in
          let uu____19999 =
            let uu____20008 =
              let uu____20013 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____20013)  in
            (uu____20008, r1)  in
          FStar_Pervasives_Native.Some uu____19999
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____20048 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____20048 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____20081,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____20106 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____20106  in
            let uu____20107 =
              let uu____20112 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____20112, r1)  in
            FStar_Pervasives_Native.Some uu____20107
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____20136 = try_lookup_lid env l  in
      match uu____20136 with
      | FStar_Pervasives_Native.None  ->
          let uu____20163 = name_not_found l  in
          let uu____20169 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20163 uu____20169
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_20212  ->
              match uu___5_20212 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____20216 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20237 = lookup_qname env lid  in
      match uu____20237 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20246,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20249;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20251;
              FStar_Syntax_Syntax.sigattrs = uu____20252;
              FStar_Syntax_Syntax.sigopts = uu____20253;_},FStar_Pervasives_Native.None
            ),uu____20254)
          ->
          let uu____20305 =
            let uu____20312 =
              let uu____20313 =
                let uu____20316 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____20316 t  in
              (uvs, uu____20313)  in
            (uu____20312, q)  in
          FStar_Pervasives_Native.Some uu____20305
      | uu____20329 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20351 = lookup_qname env lid  in
      match uu____20351 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20356,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20359;
              FStar_Syntax_Syntax.sigquals = uu____20360;
              FStar_Syntax_Syntax.sigmeta = uu____20361;
              FStar_Syntax_Syntax.sigattrs = uu____20362;
              FStar_Syntax_Syntax.sigopts = uu____20363;_},FStar_Pervasives_Native.None
            ),uu____20364)
          ->
          let uu____20415 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20415 (uvs, t)
      | uu____20420 ->
          let uu____20421 = name_not_found lid  in
          let uu____20427 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20421 uu____20427
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20447 = lookup_qname env lid  in
      match uu____20447 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20452,uvs,t,uu____20455,uu____20456,uu____20457);
              FStar_Syntax_Syntax.sigrng = uu____20458;
              FStar_Syntax_Syntax.sigquals = uu____20459;
              FStar_Syntax_Syntax.sigmeta = uu____20460;
              FStar_Syntax_Syntax.sigattrs = uu____20461;
              FStar_Syntax_Syntax.sigopts = uu____20462;_},FStar_Pervasives_Native.None
            ),uu____20463)
          ->
          let uu____20520 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20520 (uvs, t)
      | uu____20525 ->
          let uu____20526 = name_not_found lid  in
          let uu____20532 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20526 uu____20532
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20555 = lookup_qname env lid  in
      match uu____20555 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20563,uu____20564,uu____20565,uu____20566,uu____20567,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20569;
              FStar_Syntax_Syntax.sigquals = uu____20570;
              FStar_Syntax_Syntax.sigmeta = uu____20571;
              FStar_Syntax_Syntax.sigattrs = uu____20572;
              FStar_Syntax_Syntax.sigopts = uu____20573;_},uu____20574),uu____20575)
          -> (true, dcs)
      | uu____20640 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20656 = lookup_qname env lid  in
      match uu____20656 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20657,uu____20658,uu____20659,l,uu____20661,uu____20662);
              FStar_Syntax_Syntax.sigrng = uu____20663;
              FStar_Syntax_Syntax.sigquals = uu____20664;
              FStar_Syntax_Syntax.sigmeta = uu____20665;
              FStar_Syntax_Syntax.sigattrs = uu____20666;
              FStar_Syntax_Syntax.sigopts = uu____20667;_},uu____20668),uu____20669)
          -> l
      | uu____20728 ->
          let uu____20729 =
            let uu____20731 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20731  in
          failwith uu____20729
  
let (lookup_definition_qninfo_aux :
  Prims.bool ->
    delta_level Prims.list ->
      FStar_Ident.lident ->
        qninfo ->
          (FStar_Syntax_Syntax.univ_name Prims.list *
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.option)
  =
  fun rec_ok  ->
    fun delta_levels  ->
      fun lid  ->
        fun qninfo  ->
          let visible quals =
            FStar_All.pipe_right delta_levels
              (FStar_Util.for_some
                 (fun dl  ->
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some (visible_at dl))))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20801)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20858) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20882 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20882
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20917 -> FStar_Pervasives_Native.None)
          | uu____20926 -> FStar_Pervasives_Native.None
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        lookup_definition_qninfo_aux true delta_levels lid qninfo
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____20988 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20988
  
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____21021 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____21021
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____21073,uu____21074) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____21123),uu____21124) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____21173 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____21191 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____21201 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____21218 ->
                  let uu____21225 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____21225
              | FStar_Syntax_Syntax.Sig_let ((uu____21226,lbs),uu____21228)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____21244 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____21244
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____21251 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____21267 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____21277 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____21278 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____21285 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____21286 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21287 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____21300 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____21301 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21329 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____21329
           (fun d_opt  ->
              let uu____21342 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____21342
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21352 =
                   let uu____21355 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21355  in
                 match uu____21352 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21356 =
                       let uu____21358 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21358
                        in
                     failwith uu____21356
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21363 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21363
                       then
                         let uu____21366 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21368 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21370 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21366 uu____21368 uu____21370
                       else ());
                      FStar_Util.smap_add env.fv_delta_depths
                        lid.FStar_Ident.str d;
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21395),uu____21396) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21445 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21467),uu____21468) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21517 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21539 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21539
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21572 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21572 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21594 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21603 =
                        let uu____21604 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21604.FStar_Syntax_Syntax.n  in
                      match uu____21603 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21609 -> false))
               in
            (true, uu____21594)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21632 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21632
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let cache_in_fv_tab :
  'a .
    'a FStar_Util.smap ->
      FStar_Syntax_Syntax.fv -> (unit -> (Prims.bool * 'a)) -> 'a
  =
  fun tab  ->
    fun fv  ->
      fun f  ->
        let s =
          let uu____21704 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21704.FStar_Ident.str  in
        let uu____21705 = FStar_Util.smap_try_find tab s  in
        match uu____21705 with
        | FStar_Pervasives_Native.None  ->
            let uu____21708 = f ()  in
            (match uu____21708 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21746 =
        let uu____21747 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21747 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21781 =
        let uu____21782 = FStar_Syntax_Util.unrefine t  in
        uu____21782.FStar_Syntax_Syntax.n  in
      match uu____21781 with
      | FStar_Syntax_Syntax.Tm_type uu____21786 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21790) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21816) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21821,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21843 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21876 =
        let attrs =
          let uu____21882 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21882  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21922 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21922)
               in
            (true, res)
         in
      cache_in_fv_tab env.strict_args_tab fv f
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____21967 = lookup_qname env ftv  in
      match uu____21967 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21971) ->
          let uu____22016 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____22016 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____22037,t),r) ->
               let uu____22052 =
                 let uu____22053 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____22053 t  in
               FStar_Pervasives_Native.Some uu____22052)
      | uu____22054 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____22066 = try_lookup_effect_lid env ftv  in
      match uu____22066 with
      | FStar_Pervasives_Native.None  ->
          let uu____22069 = name_not_found ftv  in
          let uu____22075 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____22069 uu____22075
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____22099 = lookup_qname env lid0  in
        match uu____22099 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____22110);
                FStar_Syntax_Syntax.sigrng = uu____22111;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____22113;
                FStar_Syntax_Syntax.sigattrs = uu____22114;
                FStar_Syntax_Syntax.sigopts = uu____22115;_},FStar_Pervasives_Native.None
              ),uu____22116)
            ->
            let lid1 =
              let uu____22172 =
                let uu____22173 = FStar_Ident.range_of_lid lid  in
                let uu____22174 =
                  let uu____22175 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____22175  in
                FStar_Range.set_use_range uu____22173 uu____22174  in
              FStar_Ident.set_lid_range lid uu____22172  in
            let uu____22176 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_22182  ->
                      match uu___6_22182 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22185 -> false))
               in
            if uu____22176
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____22204 =
                      let uu____22206 =
                        let uu____22208 = get_range env  in
                        FStar_Range.string_of_range uu____22208  in
                      let uu____22209 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____22211 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____22206 uu____22209 uu____22211
                       in
                    failwith uu____22204)
                  in
               match (binders, univs1) with
               | ([],uu____22232) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____22258,uu____22259::uu____22260::uu____22261) ->
                   let uu____22282 =
                     let uu____22284 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____22286 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____22284 uu____22286
                      in
                   failwith uu____22282
               | uu____22297 ->
                   let uu____22312 =
                     let uu____22317 =
                       let uu____22318 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____22318)  in
                     inst_tscheme_with uu____22317 insts  in
                   (match uu____22312 with
                    | (uu____22331,t) ->
                        let t1 =
                          let uu____22334 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____22334 t  in
                        let uu____22335 =
                          let uu____22336 = FStar_Syntax_Subst.compress t1
                             in
                          uu____22336.FStar_Syntax_Syntax.n  in
                        (match uu____22335 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22371 -> failwith "Impossible")))
        | uu____22379 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22403 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22403 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22416,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22423 = find1 l2  in
            (match uu____22423 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22430 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22430 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22434 = find1 l  in
            (match uu____22434 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22439 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22439
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22460 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22460 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22466) ->
            FStar_List.length bs
        | uu____22505 ->
            let uu____22506 =
              let uu____22512 =
                let uu____22514 = FStar_Ident.string_of_lid name  in
                let uu____22516 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22514 uu____22516
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22512)
               in
            FStar_Errors.raise_error uu____22506 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22535 = lookup_qname env l1  in
      match uu____22535 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22538;
              FStar_Syntax_Syntax.sigrng = uu____22539;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22541;
              FStar_Syntax_Syntax.sigattrs = uu____22542;
              FStar_Syntax_Syntax.sigopts = uu____22543;_},uu____22544),uu____22545)
          -> q
      | uu____22598 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22622 =
          let uu____22623 =
            let uu____22625 = FStar_Util.string_of_int i  in
            let uu____22627 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22625 uu____22627
             in
          failwith uu____22623  in
        let uu____22630 = lookup_datacon env lid  in
        match uu____22630 with
        | (uu____22635,t) ->
            let uu____22637 =
              let uu____22638 = FStar_Syntax_Subst.compress t  in
              uu____22638.FStar_Syntax_Syntax.n  in
            (match uu____22637 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22642) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____22686 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____22686
                      FStar_Pervasives_Native.fst)
             | uu____22697 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22711 = lookup_qname env l  in
      match uu____22711 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22713,uu____22714,uu____22715);
              FStar_Syntax_Syntax.sigrng = uu____22716;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22718;
              FStar_Syntax_Syntax.sigattrs = uu____22719;
              FStar_Syntax_Syntax.sigopts = uu____22720;_},uu____22721),uu____22722)
          ->
          FStar_Util.for_some
            (fun uu___7_22777  ->
               match uu___7_22777 with
               | FStar_Syntax_Syntax.Projector uu____22779 -> true
               | uu____22785 -> false) quals
      | uu____22787 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22801 = lookup_qname env lid  in
      match uu____22801 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22803,uu____22804,uu____22805,uu____22806,uu____22807,uu____22808);
              FStar_Syntax_Syntax.sigrng = uu____22809;
              FStar_Syntax_Syntax.sigquals = uu____22810;
              FStar_Syntax_Syntax.sigmeta = uu____22811;
              FStar_Syntax_Syntax.sigattrs = uu____22812;
              FStar_Syntax_Syntax.sigopts = uu____22813;_},uu____22814),uu____22815)
          -> true
      | uu____22875 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22889 = lookup_qname env lid  in
      match uu____22889 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22891,uu____22892,uu____22893,uu____22894,uu____22895,uu____22896);
              FStar_Syntax_Syntax.sigrng = uu____22897;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22899;
              FStar_Syntax_Syntax.sigattrs = uu____22900;
              FStar_Syntax_Syntax.sigopts = uu____22901;_},uu____22902),uu____22903)
          ->
          FStar_Util.for_some
            (fun uu___8_22966  ->
               match uu___8_22966 with
               | FStar_Syntax_Syntax.RecordType uu____22968 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22978 -> true
               | uu____22988 -> false) quals
      | uu____22990 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____23000,uu____23001);
            FStar_Syntax_Syntax.sigrng = uu____23002;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____23004;
            FStar_Syntax_Syntax.sigattrs = uu____23005;
            FStar_Syntax_Syntax.sigopts = uu____23006;_},uu____23007),uu____23008)
        ->
        FStar_Util.for_some
          (fun uu___9_23067  ->
             match uu___9_23067 with
             | FStar_Syntax_Syntax.Action uu____23069 -> true
             | uu____23071 -> false) quals
    | uu____23073 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23087 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____23087
  
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
    FStar_Parser_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____23104 =
        let uu____23105 = FStar_Syntax_Util.un_uinst head1  in
        uu____23105.FStar_Syntax_Syntax.n  in
      match uu____23104 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____23111 ->
               true
           | uu____23114 -> false)
      | uu____23116 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23130 = lookup_qname env l  in
      match uu____23130 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____23133),uu____23134) ->
          FStar_Util.for_some
            (fun uu___10_23182  ->
               match uu___10_23182 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____23185 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____23187 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____23263 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____23281) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____23299 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____23307 ->
                 FStar_Pervasives_Native.Some true
             | uu____23326 -> FStar_Pervasives_Native.Some false)
         in
      let uu____23329 =
        let uu____23333 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____23333 mapper  in
      match uu____23329 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23393 = lookup_qname env lid  in
      match uu____23393 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23397,uu____23398,tps,uu____23400,uu____23401,uu____23402);
              FStar_Syntax_Syntax.sigrng = uu____23403;
              FStar_Syntax_Syntax.sigquals = uu____23404;
              FStar_Syntax_Syntax.sigmeta = uu____23405;
              FStar_Syntax_Syntax.sigattrs = uu____23406;
              FStar_Syntax_Syntax.sigopts = uu____23407;_},uu____23408),uu____23409)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23477 -> FStar_Pervasives_Native.None
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____23523  ->
              match uu____23523 with
              | (d,uu____23532) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23548 = effect_decl_opt env l  in
      match uu____23548 with
      | FStar_Pervasives_Native.None  ->
          let uu____23563 = name_not_found l  in
          let uu____23569 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23563 uu____23569
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23597 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23597 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23604  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23618  ->
            fun uu____23619  -> fun e  -> FStar_Util.return_all e))
  } 
let (join_opt :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23653 = FStar_Ident.lid_equals l1 l2  in
        if uu____23653
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23672 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23672
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23691 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23744  ->
                        match uu____23744 with
                        | (m1,m2,uu____23758,uu____23759,uu____23760) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23691 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23785,uu____23786,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23834 = join_opt env l1 l2  in
        match uu____23834 with
        | FStar_Pervasives_Native.None  ->
            let uu____23855 =
              let uu____23861 =
                let uu____23863 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23865 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23863 uu____23865
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23861)  in
            FStar_Errors.raise_error uu____23855 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23908 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23908
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'Auu____23928 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23928) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23957 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23983  ->
                match uu____23983 with
                | (d,uu____23990) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23957 with
      | FStar_Pervasives_Native.None  ->
          let uu____24001 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____24001
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____24016 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____24016 with
           | (uu____24027,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____24045)::(wp,uu____24047)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____24103 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____24168 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____24181 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____24181 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____24198 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____24198 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____24223 =
                     let uu____24229 =
                       let uu____24231 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____24239 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____24250 =
                         let uu____24252 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____24252  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____24231 uu____24239 uu____24250
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____24229)
                      in
                   FStar_Errors.raise_error uu____24223
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____24260 =
                     let uu____24271 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____24271 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____24308  ->
                        fun uu____24309  ->
                          match (uu____24308, uu____24309) with
                          | ((x,uu____24339),(t,uu____24341)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____24260
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____24372 =
                     let uu___1614_24373 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1614_24373.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1614_24373.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1614_24373.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1614_24373.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24372
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24385 .
    'Auu____24385 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_res  ->
          let check_partial_application eff_name args =
            let r = get_range env  in
            let uu____24426 =
              let uu____24433 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24433)  in
            match uu____24426 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24457 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24459 = FStar_Util.string_of_int given  in
                     let uu____24461 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24457 uu____24459 uu____24461
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24466 = effect_decl_opt env effect_name  in
          match uu____24466 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24488) ->
              let uu____24499 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24499 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24517 =
                       let uu____24520 = get_range env  in
                       let uu____24521 =
                         let uu____24528 =
                           let uu____24529 =
                             let uu____24546 =
                               let uu____24557 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24557 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24546)  in
                           FStar_Syntax_Syntax.Tm_app uu____24529  in
                         FStar_Syntax_Syntax.mk uu____24528  in
                       uu____24521 FStar_Pervasives_Native.None uu____24520
                        in
                     FStar_Pervasives_Native.Some uu____24517)))
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_res  -> effect_repr_aux false env c u_res 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_All.pipe_right quals
        (FStar_List.existsb
           (fun uu___11_24657  ->
              match uu___11_24657 with
              | FStar_Syntax_Syntax.Reflectable uu____24659 -> true
              | uu____24661 -> false))
  
let (is_total_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      (is_user_reifiable_effect env effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
  
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____24721 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24736 =
        let uu____24737 = FStar_Syntax_Subst.compress t  in
        uu____24737.FStar_Syntax_Syntax.n  in
      match uu____24736 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24741,c) ->
          is_reifiable_comp env c
      | uu____24763 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24783 =
           let uu____24785 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24785  in
         if uu____24783
         then
           let uu____24788 =
             let uu____24794 =
               let uu____24796 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24796
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24794)  in
           let uu____24800 = get_range env  in
           FStar_Errors.raise_error uu____24788 uu____24800
         else ());
        (let uu____24803 = effect_repr_aux true env c u_c  in
         match uu____24803 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1691_24839 = env  in
        {
          solver = (uu___1691_24839.solver);
          range = (uu___1691_24839.range);
          curmodule = (uu___1691_24839.curmodule);
          gamma = (uu___1691_24839.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1691_24839.gamma_cache);
          modules = (uu___1691_24839.modules);
          expected_typ = (uu___1691_24839.expected_typ);
          sigtab = (uu___1691_24839.sigtab);
          attrtab = (uu___1691_24839.attrtab);
          instantiate_imp = (uu___1691_24839.instantiate_imp);
          effects = (uu___1691_24839.effects);
          generalize = (uu___1691_24839.generalize);
          letrecs = (uu___1691_24839.letrecs);
          top_level = (uu___1691_24839.top_level);
          check_uvars = (uu___1691_24839.check_uvars);
          use_eq = (uu___1691_24839.use_eq);
          use_eq_strict = (uu___1691_24839.use_eq_strict);
          is_iface = (uu___1691_24839.is_iface);
          admit = (uu___1691_24839.admit);
          lax = (uu___1691_24839.lax);
          lax_universes = (uu___1691_24839.lax_universes);
          phase1 = (uu___1691_24839.phase1);
          failhard = (uu___1691_24839.failhard);
          nosynth = (uu___1691_24839.nosynth);
          uvar_subtyping = (uu___1691_24839.uvar_subtyping);
          tc_term = (uu___1691_24839.tc_term);
          type_of = (uu___1691_24839.type_of);
          universe_of = (uu___1691_24839.universe_of);
          check_type_of = (uu___1691_24839.check_type_of);
          use_bv_sorts = (uu___1691_24839.use_bv_sorts);
          qtbl_name_and_index = (uu___1691_24839.qtbl_name_and_index);
          normalized_eff_names = (uu___1691_24839.normalized_eff_names);
          fv_delta_depths = (uu___1691_24839.fv_delta_depths);
          proof_ns = (uu___1691_24839.proof_ns);
          synth_hook = (uu___1691_24839.synth_hook);
          try_solve_implicits_hook =
            (uu___1691_24839.try_solve_implicits_hook);
          splice = (uu___1691_24839.splice);
          mpreprocess = (uu___1691_24839.mpreprocess);
          postprocess = (uu___1691_24839.postprocess);
          is_native_tactic = (uu___1691_24839.is_native_tactic);
          identifier_info = (uu___1691_24839.identifier_info);
          tc_hooks = (uu___1691_24839.tc_hooks);
          dsenv = (uu___1691_24839.dsenv);
          nbe = (uu___1691_24839.nbe);
          strict_args_tab = (uu___1691_24839.strict_args_tab);
          erasable_types_tab = (uu___1691_24839.erasable_types_tab);
          enable_defer_to_tac = (uu___1691_24839.enable_defer_to_tac)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      env1
  
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env  ->
    fun uu____24858  ->
      match uu____24858 with
      | (ed,quals) ->
          let effects =
            let uu___1700_24872 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1700_24872.order);
              joins = (uu___1700_24872.joins);
              polymonadic_binds = (uu___1700_24872.polymonadic_binds)
            }  in
          let uu___1703_24881 = env  in
          {
            solver = (uu___1703_24881.solver);
            range = (uu___1703_24881.range);
            curmodule = (uu___1703_24881.curmodule);
            gamma = (uu___1703_24881.gamma);
            gamma_sig = (uu___1703_24881.gamma_sig);
            gamma_cache = (uu___1703_24881.gamma_cache);
            modules = (uu___1703_24881.modules);
            expected_typ = (uu___1703_24881.expected_typ);
            sigtab = (uu___1703_24881.sigtab);
            attrtab = (uu___1703_24881.attrtab);
            instantiate_imp = (uu___1703_24881.instantiate_imp);
            effects;
            generalize = (uu___1703_24881.generalize);
            letrecs = (uu___1703_24881.letrecs);
            top_level = (uu___1703_24881.top_level);
            check_uvars = (uu___1703_24881.check_uvars);
            use_eq = (uu___1703_24881.use_eq);
            use_eq_strict = (uu___1703_24881.use_eq_strict);
            is_iface = (uu___1703_24881.is_iface);
            admit = (uu___1703_24881.admit);
            lax = (uu___1703_24881.lax);
            lax_universes = (uu___1703_24881.lax_universes);
            phase1 = (uu___1703_24881.phase1);
            failhard = (uu___1703_24881.failhard);
            nosynth = (uu___1703_24881.nosynth);
            uvar_subtyping = (uu___1703_24881.uvar_subtyping);
            tc_term = (uu___1703_24881.tc_term);
            type_of = (uu___1703_24881.type_of);
            universe_of = (uu___1703_24881.universe_of);
            check_type_of = (uu___1703_24881.check_type_of);
            use_bv_sorts = (uu___1703_24881.use_bv_sorts);
            qtbl_name_and_index = (uu___1703_24881.qtbl_name_and_index);
            normalized_eff_names = (uu___1703_24881.normalized_eff_names);
            fv_delta_depths = (uu___1703_24881.fv_delta_depths);
            proof_ns = (uu___1703_24881.proof_ns);
            synth_hook = (uu___1703_24881.synth_hook);
            try_solve_implicits_hook =
              (uu___1703_24881.try_solve_implicits_hook);
            splice = (uu___1703_24881.splice);
            mpreprocess = (uu___1703_24881.mpreprocess);
            postprocess = (uu___1703_24881.postprocess);
            is_native_tactic = (uu___1703_24881.is_native_tactic);
            identifier_info = (uu___1703_24881.identifier_info);
            tc_hooks = (uu___1703_24881.tc_hooks);
            dsenv = (uu___1703_24881.dsenv);
            nbe = (uu___1703_24881.nbe);
            strict_args_tab = (uu___1703_24881.strict_args_tab);
            erasable_types_tab = (uu___1703_24881.erasable_types_tab);
            enable_defer_to_tac = (uu___1703_24881.enable_defer_to_tac)
          }
  
let (exists_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * polymonadic_bind_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        let uu____24910 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24978  ->
                  match uu____24978 with
                  | (m1,n11,uu____24996,uu____24997) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24910 with
        | FStar_Pervasives_Native.Some (uu____25022,uu____25023,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____25068 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____25143 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____25143
                  (fun uu____25164  ->
                     match uu____25164 with
                     | (c1,g1) ->
                         let uu____25175 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____25175
                           (fun uu____25196  ->
                              match uu____25196 with
                              | (c2,g2) ->
                                  let uu____25207 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____25207)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____25329 = l1 u t e  in
                              l2 u t uu____25329))
                | uu____25330 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let edge = { msource = src; mtarget = tgt; mlift = st_mlift }  in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift }  in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____25398  ->
                    match uu____25398 with
                    | (e,uu____25406) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25429 =
            match uu____25429 with
            | (i,j) ->
                let uu____25440 = FStar_Ident.lid_equals i j  in
                if uu____25440
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25447  -> FStar_Pervasives_Native.Some _25447)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25476 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25486 = FStar_Ident.lid_equals i k  in
                        if uu____25486
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25500 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25500
                                  then []
                                  else
                                    (let uu____25507 =
                                       let uu____25516 =
                                         find_edge order1 (i, k)  in
                                       let uu____25519 =
                                         find_edge order1 (k, j)  in
                                       (uu____25516, uu____25519)  in
                                     match uu____25507 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25534 =
                                           compose_edges e1 e2  in
                                         [uu____25534]
                                     | uu____25535 -> [])))))
                 in
              FStar_List.append order1 uu____25476  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          FStar_All.pipe_right order2
            (FStar_List.iter
               (fun edge1  ->
                  let uu____25565 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25568 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25568
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25565
                  then
                    let uu____25575 =
                      let uu____25581 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25581)
                       in
                    let uu____25585 = get_range env  in
                    FStar_Errors.raise_error uu____25575 uu____25585
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25663 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25663
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25715 =
                                             let uu____25724 =
                                               find_edge order2 (i, k)  in
                                             let uu____25727 =
                                               find_edge order2 (j, k)  in
                                             (uu____25724, uu____25727)  in
                                           match uu____25715 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25769,uu____25770)
                                                    ->
                                                    let uu____25777 =
                                                      let uu____25784 =
                                                        let uu____25786 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25786
                                                         in
                                                      let uu____25789 =
                                                        let uu____25791 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25791
                                                         in
                                                      (uu____25784,
                                                        uu____25789)
                                                       in
                                                    (match uu____25777 with
                                                     | (true ,true ) ->
                                                         let uu____25808 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25808
                                                         then
                                                           (FStar_Errors.log_issue
                                                              FStar_Range.dummyRange
                                                              (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                "Looking multiple times at the same upper bound candidate");
                                                            bopt)
                                                         else
                                                           failwith
                                                             "Found a cycle in the lattice"
                                                     | (false ,false ) ->
                                                         bopt
                                                     | (true ,false ) ->
                                                         FStar_Pervasives_Native.Some
                                                           (k, ik, jk)
                                                     | (false ,true ) -> bopt))
                                           | uu____25851 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25903 =
                                   let uu____25905 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25905
                                     FStar_Util.is_some
                                    in
                                 if uu____25903
                                 then
                                   let uu____25954 =
                                     let uu____25960 =
                                       let uu____25962 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25964 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25966 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25968 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25962 uu____25964 uu____25966
                                         uu____25968
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25960)
                                      in
                                   FStar_Errors.raise_error uu____25954
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1824_26007 = env.effects  in
             {
               decls = (uu___1824_26007.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1824_26007.polymonadic_binds)
             }  in
           let uu___1827_26008 = env  in
           {
             solver = (uu___1827_26008.solver);
             range = (uu___1827_26008.range);
             curmodule = (uu___1827_26008.curmodule);
             gamma = (uu___1827_26008.gamma);
             gamma_sig = (uu___1827_26008.gamma_sig);
             gamma_cache = (uu___1827_26008.gamma_cache);
             modules = (uu___1827_26008.modules);
             expected_typ = (uu___1827_26008.expected_typ);
             sigtab = (uu___1827_26008.sigtab);
             attrtab = (uu___1827_26008.attrtab);
             instantiate_imp = (uu___1827_26008.instantiate_imp);
             effects;
             generalize = (uu___1827_26008.generalize);
             letrecs = (uu___1827_26008.letrecs);
             top_level = (uu___1827_26008.top_level);
             check_uvars = (uu___1827_26008.check_uvars);
             use_eq = (uu___1827_26008.use_eq);
             use_eq_strict = (uu___1827_26008.use_eq_strict);
             is_iface = (uu___1827_26008.is_iface);
             admit = (uu___1827_26008.admit);
             lax = (uu___1827_26008.lax);
             lax_universes = (uu___1827_26008.lax_universes);
             phase1 = (uu___1827_26008.phase1);
             failhard = (uu___1827_26008.failhard);
             nosynth = (uu___1827_26008.nosynth);
             uvar_subtyping = (uu___1827_26008.uvar_subtyping);
             tc_term = (uu___1827_26008.tc_term);
             type_of = (uu___1827_26008.type_of);
             universe_of = (uu___1827_26008.universe_of);
             check_type_of = (uu___1827_26008.check_type_of);
             use_bv_sorts = (uu___1827_26008.use_bv_sorts);
             qtbl_name_and_index = (uu___1827_26008.qtbl_name_and_index);
             normalized_eff_names = (uu___1827_26008.normalized_eff_names);
             fv_delta_depths = (uu___1827_26008.fv_delta_depths);
             proof_ns = (uu___1827_26008.proof_ns);
             synth_hook = (uu___1827_26008.synth_hook);
             try_solve_implicits_hook =
               (uu___1827_26008.try_solve_implicits_hook);
             splice = (uu___1827_26008.splice);
             mpreprocess = (uu___1827_26008.mpreprocess);
             postprocess = (uu___1827_26008.postprocess);
             is_native_tactic = (uu___1827_26008.is_native_tactic);
             identifier_info = (uu___1827_26008.identifier_info);
             tc_hooks = (uu___1827_26008.tc_hooks);
             dsenv = (uu___1827_26008.dsenv);
             nbe = (uu___1827_26008.nbe);
             strict_args_tab = (uu___1827_26008.strict_args_tab);
             erasable_types_tab = (uu___1827_26008.erasable_types_tab);
             enable_defer_to_tac = (uu___1827_26008.enable_defer_to_tac)
           })
  
let (add_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Ident.lident -> polymonadic_bind_t -> env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            let err_msg poly =
              let uu____26056 = FStar_Ident.string_of_lid m  in
              let uu____26058 = FStar_Ident.string_of_lid n1  in
              let uu____26060 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____26056 uu____26058 uu____26060
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____26069 =
              let uu____26071 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____26071 FStar_Util.is_some  in
            if uu____26069
            then
              let uu____26108 =
                let uu____26114 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26114)
                 in
              FStar_Errors.raise_error uu____26108 env.range
            else
              (let uu____26120 =
                 let uu____26122 = join_opt env m n1  in
                 FStar_All.pipe_right uu____26122 FStar_Util.is_some  in
               if uu____26120
               then
                 let uu____26147 =
                   let uu____26153 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26153)
                    in
                 FStar_Errors.raise_error uu____26147 env.range
               else
                 (let uu___1842_26159 = env  in
                  {
                    solver = (uu___1842_26159.solver);
                    range = (uu___1842_26159.range);
                    curmodule = (uu___1842_26159.curmodule);
                    gamma = (uu___1842_26159.gamma);
                    gamma_sig = (uu___1842_26159.gamma_sig);
                    gamma_cache = (uu___1842_26159.gamma_cache);
                    modules = (uu___1842_26159.modules);
                    expected_typ = (uu___1842_26159.expected_typ);
                    sigtab = (uu___1842_26159.sigtab);
                    attrtab = (uu___1842_26159.attrtab);
                    instantiate_imp = (uu___1842_26159.instantiate_imp);
                    effects =
                      (let uu___1844_26161 = env.effects  in
                       {
                         decls = (uu___1844_26161.decls);
                         order = (uu___1844_26161.order);
                         joins = (uu___1844_26161.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1842_26159.generalize);
                    letrecs = (uu___1842_26159.letrecs);
                    top_level = (uu___1842_26159.top_level);
                    check_uvars = (uu___1842_26159.check_uvars);
                    use_eq = (uu___1842_26159.use_eq);
                    use_eq_strict = (uu___1842_26159.use_eq_strict);
                    is_iface = (uu___1842_26159.is_iface);
                    admit = (uu___1842_26159.admit);
                    lax = (uu___1842_26159.lax);
                    lax_universes = (uu___1842_26159.lax_universes);
                    phase1 = (uu___1842_26159.phase1);
                    failhard = (uu___1842_26159.failhard);
                    nosynth = (uu___1842_26159.nosynth);
                    uvar_subtyping = (uu___1842_26159.uvar_subtyping);
                    tc_term = (uu___1842_26159.tc_term);
                    type_of = (uu___1842_26159.type_of);
                    universe_of = (uu___1842_26159.universe_of);
                    check_type_of = (uu___1842_26159.check_type_of);
                    use_bv_sorts = (uu___1842_26159.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1842_26159.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1842_26159.normalized_eff_names);
                    fv_delta_depths = (uu___1842_26159.fv_delta_depths);
                    proof_ns = (uu___1842_26159.proof_ns);
                    synth_hook = (uu___1842_26159.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1842_26159.try_solve_implicits_hook);
                    splice = (uu___1842_26159.splice);
                    mpreprocess = (uu___1842_26159.mpreprocess);
                    postprocess = (uu___1842_26159.postprocess);
                    is_native_tactic = (uu___1842_26159.is_native_tactic);
                    identifier_info = (uu___1842_26159.identifier_info);
                    tc_hooks = (uu___1842_26159.tc_hooks);
                    dsenv = (uu___1842_26159.dsenv);
                    nbe = (uu___1842_26159.nbe);
                    strict_args_tab = (uu___1842_26159.strict_args_tab);
                    erasable_types_tab = (uu___1842_26159.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1842_26159.enable_defer_to_tac)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1848_26233 = env  in
      {
        solver = (uu___1848_26233.solver);
        range = (uu___1848_26233.range);
        curmodule = (uu___1848_26233.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1848_26233.gamma_sig);
        gamma_cache = (uu___1848_26233.gamma_cache);
        modules = (uu___1848_26233.modules);
        expected_typ = (uu___1848_26233.expected_typ);
        sigtab = (uu___1848_26233.sigtab);
        attrtab = (uu___1848_26233.attrtab);
        instantiate_imp = (uu___1848_26233.instantiate_imp);
        effects = (uu___1848_26233.effects);
        generalize = (uu___1848_26233.generalize);
        letrecs = (uu___1848_26233.letrecs);
        top_level = (uu___1848_26233.top_level);
        check_uvars = (uu___1848_26233.check_uvars);
        use_eq = (uu___1848_26233.use_eq);
        use_eq_strict = (uu___1848_26233.use_eq_strict);
        is_iface = (uu___1848_26233.is_iface);
        admit = (uu___1848_26233.admit);
        lax = (uu___1848_26233.lax);
        lax_universes = (uu___1848_26233.lax_universes);
        phase1 = (uu___1848_26233.phase1);
        failhard = (uu___1848_26233.failhard);
        nosynth = (uu___1848_26233.nosynth);
        uvar_subtyping = (uu___1848_26233.uvar_subtyping);
        tc_term = (uu___1848_26233.tc_term);
        type_of = (uu___1848_26233.type_of);
        universe_of = (uu___1848_26233.universe_of);
        check_type_of = (uu___1848_26233.check_type_of);
        use_bv_sorts = (uu___1848_26233.use_bv_sorts);
        qtbl_name_and_index = (uu___1848_26233.qtbl_name_and_index);
        normalized_eff_names = (uu___1848_26233.normalized_eff_names);
        fv_delta_depths = (uu___1848_26233.fv_delta_depths);
        proof_ns = (uu___1848_26233.proof_ns);
        synth_hook = (uu___1848_26233.synth_hook);
        try_solve_implicits_hook = (uu___1848_26233.try_solve_implicits_hook);
        splice = (uu___1848_26233.splice);
        mpreprocess = (uu___1848_26233.mpreprocess);
        postprocess = (uu___1848_26233.postprocess);
        is_native_tactic = (uu___1848_26233.is_native_tactic);
        identifier_info = (uu___1848_26233.identifier_info);
        tc_hooks = (uu___1848_26233.tc_hooks);
        dsenv = (uu___1848_26233.dsenv);
        nbe = (uu___1848_26233.nbe);
        strict_args_tab = (uu___1848_26233.strict_args_tab);
        erasable_types_tab = (uu___1848_26233.erasable_types_tab);
        enable_defer_to_tac = (uu___1848_26233.enable_defer_to_tac)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env -> (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option) =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___1861_26291 = env  in
             {
               solver = (uu___1861_26291.solver);
               range = (uu___1861_26291.range);
               curmodule = (uu___1861_26291.curmodule);
               gamma = rest;
               gamma_sig = (uu___1861_26291.gamma_sig);
               gamma_cache = (uu___1861_26291.gamma_cache);
               modules = (uu___1861_26291.modules);
               expected_typ = (uu___1861_26291.expected_typ);
               sigtab = (uu___1861_26291.sigtab);
               attrtab = (uu___1861_26291.attrtab);
               instantiate_imp = (uu___1861_26291.instantiate_imp);
               effects = (uu___1861_26291.effects);
               generalize = (uu___1861_26291.generalize);
               letrecs = (uu___1861_26291.letrecs);
               top_level = (uu___1861_26291.top_level);
               check_uvars = (uu___1861_26291.check_uvars);
               use_eq = (uu___1861_26291.use_eq);
               use_eq_strict = (uu___1861_26291.use_eq_strict);
               is_iface = (uu___1861_26291.is_iface);
               admit = (uu___1861_26291.admit);
               lax = (uu___1861_26291.lax);
               lax_universes = (uu___1861_26291.lax_universes);
               phase1 = (uu___1861_26291.phase1);
               failhard = (uu___1861_26291.failhard);
               nosynth = (uu___1861_26291.nosynth);
               uvar_subtyping = (uu___1861_26291.uvar_subtyping);
               tc_term = (uu___1861_26291.tc_term);
               type_of = (uu___1861_26291.type_of);
               universe_of = (uu___1861_26291.universe_of);
               check_type_of = (uu___1861_26291.check_type_of);
               use_bv_sorts = (uu___1861_26291.use_bv_sorts);
               qtbl_name_and_index = (uu___1861_26291.qtbl_name_and_index);
               normalized_eff_names = (uu___1861_26291.normalized_eff_names);
               fv_delta_depths = (uu___1861_26291.fv_delta_depths);
               proof_ns = (uu___1861_26291.proof_ns);
               synth_hook = (uu___1861_26291.synth_hook);
               try_solve_implicits_hook =
                 (uu___1861_26291.try_solve_implicits_hook);
               splice = (uu___1861_26291.splice);
               mpreprocess = (uu___1861_26291.mpreprocess);
               postprocess = (uu___1861_26291.postprocess);
               is_native_tactic = (uu___1861_26291.is_native_tactic);
               identifier_info = (uu___1861_26291.identifier_info);
               tc_hooks = (uu___1861_26291.tc_hooks);
               dsenv = (uu___1861_26291.dsenv);
               nbe = (uu___1861_26291.nbe);
               strict_args_tab = (uu___1861_26291.strict_args_tab);
               erasable_types_tab = (uu___1861_26291.erasable_types_tab);
               enable_defer_to_tac = (uu___1861_26291.enable_defer_to_tac)
             }))
    | uu____26292 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____26321  ->
             match uu____26321 with | (x,uu____26329) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___1875_26364 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1875_26364.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1875_26364.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list))
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____26437 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26437 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26465 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26465)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1896_26481 = env  in
      {
        solver = (uu___1896_26481.solver);
        range = (uu___1896_26481.range);
        curmodule = (uu___1896_26481.curmodule);
        gamma = (uu___1896_26481.gamma);
        gamma_sig = (uu___1896_26481.gamma_sig);
        gamma_cache = (uu___1896_26481.gamma_cache);
        modules = (uu___1896_26481.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1896_26481.sigtab);
        attrtab = (uu___1896_26481.attrtab);
        instantiate_imp = (uu___1896_26481.instantiate_imp);
        effects = (uu___1896_26481.effects);
        generalize = (uu___1896_26481.generalize);
        letrecs = (uu___1896_26481.letrecs);
        top_level = (uu___1896_26481.top_level);
        check_uvars = (uu___1896_26481.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1896_26481.use_eq_strict);
        is_iface = (uu___1896_26481.is_iface);
        admit = (uu___1896_26481.admit);
        lax = (uu___1896_26481.lax);
        lax_universes = (uu___1896_26481.lax_universes);
        phase1 = (uu___1896_26481.phase1);
        failhard = (uu___1896_26481.failhard);
        nosynth = (uu___1896_26481.nosynth);
        uvar_subtyping = (uu___1896_26481.uvar_subtyping);
        tc_term = (uu___1896_26481.tc_term);
        type_of = (uu___1896_26481.type_of);
        universe_of = (uu___1896_26481.universe_of);
        check_type_of = (uu___1896_26481.check_type_of);
        use_bv_sorts = (uu___1896_26481.use_bv_sorts);
        qtbl_name_and_index = (uu___1896_26481.qtbl_name_and_index);
        normalized_eff_names = (uu___1896_26481.normalized_eff_names);
        fv_delta_depths = (uu___1896_26481.fv_delta_depths);
        proof_ns = (uu___1896_26481.proof_ns);
        synth_hook = (uu___1896_26481.synth_hook);
        try_solve_implicits_hook = (uu___1896_26481.try_solve_implicits_hook);
        splice = (uu___1896_26481.splice);
        mpreprocess = (uu___1896_26481.mpreprocess);
        postprocess = (uu___1896_26481.postprocess);
        is_native_tactic = (uu___1896_26481.is_native_tactic);
        identifier_info = (uu___1896_26481.identifier_info);
        tc_hooks = (uu___1896_26481.tc_hooks);
        dsenv = (uu___1896_26481.dsenv);
        nbe = (uu___1896_26481.nbe);
        strict_args_tab = (uu___1896_26481.strict_args_tab);
        erasable_types_tab = (uu___1896_26481.erasable_types_tab);
        enable_defer_to_tac = (uu___1896_26481.enable_defer_to_tac)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env -> (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)) =
  fun env_  ->
    let uu____26512 = expected_typ env_  in
    ((let uu___1903_26518 = env_  in
      {
        solver = (uu___1903_26518.solver);
        range = (uu___1903_26518.range);
        curmodule = (uu___1903_26518.curmodule);
        gamma = (uu___1903_26518.gamma);
        gamma_sig = (uu___1903_26518.gamma_sig);
        gamma_cache = (uu___1903_26518.gamma_cache);
        modules = (uu___1903_26518.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1903_26518.sigtab);
        attrtab = (uu___1903_26518.attrtab);
        instantiate_imp = (uu___1903_26518.instantiate_imp);
        effects = (uu___1903_26518.effects);
        generalize = (uu___1903_26518.generalize);
        letrecs = (uu___1903_26518.letrecs);
        top_level = (uu___1903_26518.top_level);
        check_uvars = (uu___1903_26518.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1903_26518.use_eq_strict);
        is_iface = (uu___1903_26518.is_iface);
        admit = (uu___1903_26518.admit);
        lax = (uu___1903_26518.lax);
        lax_universes = (uu___1903_26518.lax_universes);
        phase1 = (uu___1903_26518.phase1);
        failhard = (uu___1903_26518.failhard);
        nosynth = (uu___1903_26518.nosynth);
        uvar_subtyping = (uu___1903_26518.uvar_subtyping);
        tc_term = (uu___1903_26518.tc_term);
        type_of = (uu___1903_26518.type_of);
        universe_of = (uu___1903_26518.universe_of);
        check_type_of = (uu___1903_26518.check_type_of);
        use_bv_sorts = (uu___1903_26518.use_bv_sorts);
        qtbl_name_and_index = (uu___1903_26518.qtbl_name_and_index);
        normalized_eff_names = (uu___1903_26518.normalized_eff_names);
        fv_delta_depths = (uu___1903_26518.fv_delta_depths);
        proof_ns = (uu___1903_26518.proof_ns);
        synth_hook = (uu___1903_26518.synth_hook);
        try_solve_implicits_hook = (uu___1903_26518.try_solve_implicits_hook);
        splice = (uu___1903_26518.splice);
        mpreprocess = (uu___1903_26518.mpreprocess);
        postprocess = (uu___1903_26518.postprocess);
        is_native_tactic = (uu___1903_26518.is_native_tactic);
        identifier_info = (uu___1903_26518.identifier_info);
        tc_hooks = (uu___1903_26518.tc_hooks);
        dsenv = (uu___1903_26518.dsenv);
        nbe = (uu___1903_26518.nbe);
        strict_args_tab = (uu___1903_26518.strict_args_tab);
        erasable_types_tab = (uu___1903_26518.erasable_types_tab);
        enable_defer_to_tac = (uu___1903_26518.enable_defer_to_tac)
      }), uu____26512)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26530 =
      let uu____26533 = FStar_Ident.id_of_text ""  in [uu____26533]  in
    FStar_Ident.lid_of_ids uu____26530  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26540 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26540
        then
          let uu____26545 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26545 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1911_26573 = env  in
       {
         solver = (uu___1911_26573.solver);
         range = (uu___1911_26573.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1911_26573.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1911_26573.expected_typ);
         sigtab = (uu___1911_26573.sigtab);
         attrtab = (uu___1911_26573.attrtab);
         instantiate_imp = (uu___1911_26573.instantiate_imp);
         effects = (uu___1911_26573.effects);
         generalize = (uu___1911_26573.generalize);
         letrecs = (uu___1911_26573.letrecs);
         top_level = (uu___1911_26573.top_level);
         check_uvars = (uu___1911_26573.check_uvars);
         use_eq = (uu___1911_26573.use_eq);
         use_eq_strict = (uu___1911_26573.use_eq_strict);
         is_iface = (uu___1911_26573.is_iface);
         admit = (uu___1911_26573.admit);
         lax = (uu___1911_26573.lax);
         lax_universes = (uu___1911_26573.lax_universes);
         phase1 = (uu___1911_26573.phase1);
         failhard = (uu___1911_26573.failhard);
         nosynth = (uu___1911_26573.nosynth);
         uvar_subtyping = (uu___1911_26573.uvar_subtyping);
         tc_term = (uu___1911_26573.tc_term);
         type_of = (uu___1911_26573.type_of);
         universe_of = (uu___1911_26573.universe_of);
         check_type_of = (uu___1911_26573.check_type_of);
         use_bv_sorts = (uu___1911_26573.use_bv_sorts);
         qtbl_name_and_index = (uu___1911_26573.qtbl_name_and_index);
         normalized_eff_names = (uu___1911_26573.normalized_eff_names);
         fv_delta_depths = (uu___1911_26573.fv_delta_depths);
         proof_ns = (uu___1911_26573.proof_ns);
         synth_hook = (uu___1911_26573.synth_hook);
         try_solve_implicits_hook =
           (uu___1911_26573.try_solve_implicits_hook);
         splice = (uu___1911_26573.splice);
         mpreprocess = (uu___1911_26573.mpreprocess);
         postprocess = (uu___1911_26573.postprocess);
         is_native_tactic = (uu___1911_26573.is_native_tactic);
         identifier_info = (uu___1911_26573.identifier_info);
         tc_hooks = (uu___1911_26573.tc_hooks);
         dsenv = (uu___1911_26573.dsenv);
         nbe = (uu___1911_26573.nbe);
         strict_args_tab = (uu___1911_26573.strict_args_tab);
         erasable_types_tab = (uu___1911_26573.erasable_types_tab);
         enable_defer_to_tac = (uu___1911_26573.enable_defer_to_tac)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26625)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26629,(uu____26630,t)))::tl1
          ->
          let uu____26651 =
            let uu____26654 = FStar_Syntax_Free.uvars t  in
            ext out uu____26654  in
          aux uu____26651 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26657;
            FStar_Syntax_Syntax.index = uu____26658;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26666 =
            let uu____26669 = FStar_Syntax_Free.uvars t  in
            ext out uu____26669  in
          aux uu____26666 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26727)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26731,(uu____26732,t)))::tl1
          ->
          let uu____26753 =
            let uu____26756 = FStar_Syntax_Free.univs t  in
            ext out uu____26756  in
          aux uu____26753 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26759;
            FStar_Syntax_Syntax.index = uu____26760;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26768 =
            let uu____26771 = FStar_Syntax_Free.univs t  in
            ext out uu____26771  in
          aux uu____26768 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____26833 = FStar_Util.set_add uname out  in
          aux uu____26833 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26836,(uu____26837,t)))::tl1
          ->
          let uu____26858 =
            let uu____26861 = FStar_Syntax_Free.univnames t  in
            ext out uu____26861  in
          aux uu____26858 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26864;
            FStar_Syntax_Syntax.index = uu____26865;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26873 =
            let uu____26876 = FStar_Syntax_Free.univnames t  in
            ext out uu____26876  in
          aux uu____26873 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26897  ->
            match uu___12_26897 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26901 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26914 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26925 =
      let uu____26934 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26934
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26925 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26982 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26995  ->
              match uu___13_26995 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26998 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26998
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____27004) ->
                  let uu____27021 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____27021))
       in
    FStar_All.pipe_right uu____26982 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_27035  ->
    match uu___14_27035 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____27041 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____27041
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____27064  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____27119) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____27152,uu____27153) -> false  in
      let uu____27167 =
        FStar_List.tryFind
          (fun uu____27189  ->
             match uu____27189 with | (p,uu____27200) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____27167 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____27219,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____27249 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____27249
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2054_27271 = e  in
        {
          solver = (uu___2054_27271.solver);
          range = (uu___2054_27271.range);
          curmodule = (uu___2054_27271.curmodule);
          gamma = (uu___2054_27271.gamma);
          gamma_sig = (uu___2054_27271.gamma_sig);
          gamma_cache = (uu___2054_27271.gamma_cache);
          modules = (uu___2054_27271.modules);
          expected_typ = (uu___2054_27271.expected_typ);
          sigtab = (uu___2054_27271.sigtab);
          attrtab = (uu___2054_27271.attrtab);
          instantiate_imp = (uu___2054_27271.instantiate_imp);
          effects = (uu___2054_27271.effects);
          generalize = (uu___2054_27271.generalize);
          letrecs = (uu___2054_27271.letrecs);
          top_level = (uu___2054_27271.top_level);
          check_uvars = (uu___2054_27271.check_uvars);
          use_eq = (uu___2054_27271.use_eq);
          use_eq_strict = (uu___2054_27271.use_eq_strict);
          is_iface = (uu___2054_27271.is_iface);
          admit = (uu___2054_27271.admit);
          lax = (uu___2054_27271.lax);
          lax_universes = (uu___2054_27271.lax_universes);
          phase1 = (uu___2054_27271.phase1);
          failhard = (uu___2054_27271.failhard);
          nosynth = (uu___2054_27271.nosynth);
          uvar_subtyping = (uu___2054_27271.uvar_subtyping);
          tc_term = (uu___2054_27271.tc_term);
          type_of = (uu___2054_27271.type_of);
          universe_of = (uu___2054_27271.universe_of);
          check_type_of = (uu___2054_27271.check_type_of);
          use_bv_sorts = (uu___2054_27271.use_bv_sorts);
          qtbl_name_and_index = (uu___2054_27271.qtbl_name_and_index);
          normalized_eff_names = (uu___2054_27271.normalized_eff_names);
          fv_delta_depths = (uu___2054_27271.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2054_27271.synth_hook);
          try_solve_implicits_hook =
            (uu___2054_27271.try_solve_implicits_hook);
          splice = (uu___2054_27271.splice);
          mpreprocess = (uu___2054_27271.mpreprocess);
          postprocess = (uu___2054_27271.postprocess);
          is_native_tactic = (uu___2054_27271.is_native_tactic);
          identifier_info = (uu___2054_27271.identifier_info);
          tc_hooks = (uu___2054_27271.tc_hooks);
          dsenv = (uu___2054_27271.dsenv);
          nbe = (uu___2054_27271.nbe);
          strict_args_tab = (uu___2054_27271.strict_args_tab);
          erasable_types_tab = (uu___2054_27271.erasable_types_tab);
          enable_defer_to_tac = (uu___2054_27271.enable_defer_to_tac)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2063_27319 = e  in
      {
        solver = (uu___2063_27319.solver);
        range = (uu___2063_27319.range);
        curmodule = (uu___2063_27319.curmodule);
        gamma = (uu___2063_27319.gamma);
        gamma_sig = (uu___2063_27319.gamma_sig);
        gamma_cache = (uu___2063_27319.gamma_cache);
        modules = (uu___2063_27319.modules);
        expected_typ = (uu___2063_27319.expected_typ);
        sigtab = (uu___2063_27319.sigtab);
        attrtab = (uu___2063_27319.attrtab);
        instantiate_imp = (uu___2063_27319.instantiate_imp);
        effects = (uu___2063_27319.effects);
        generalize = (uu___2063_27319.generalize);
        letrecs = (uu___2063_27319.letrecs);
        top_level = (uu___2063_27319.top_level);
        check_uvars = (uu___2063_27319.check_uvars);
        use_eq = (uu___2063_27319.use_eq);
        use_eq_strict = (uu___2063_27319.use_eq_strict);
        is_iface = (uu___2063_27319.is_iface);
        admit = (uu___2063_27319.admit);
        lax = (uu___2063_27319.lax);
        lax_universes = (uu___2063_27319.lax_universes);
        phase1 = (uu___2063_27319.phase1);
        failhard = (uu___2063_27319.failhard);
        nosynth = (uu___2063_27319.nosynth);
        uvar_subtyping = (uu___2063_27319.uvar_subtyping);
        tc_term = (uu___2063_27319.tc_term);
        type_of = (uu___2063_27319.type_of);
        universe_of = (uu___2063_27319.universe_of);
        check_type_of = (uu___2063_27319.check_type_of);
        use_bv_sorts = (uu___2063_27319.use_bv_sorts);
        qtbl_name_and_index = (uu___2063_27319.qtbl_name_and_index);
        normalized_eff_names = (uu___2063_27319.normalized_eff_names);
        fv_delta_depths = (uu___2063_27319.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2063_27319.synth_hook);
        try_solve_implicits_hook = (uu___2063_27319.try_solve_implicits_hook);
        splice = (uu___2063_27319.splice);
        mpreprocess = (uu___2063_27319.mpreprocess);
        postprocess = (uu___2063_27319.postprocess);
        is_native_tactic = (uu___2063_27319.is_native_tactic);
        identifier_info = (uu___2063_27319.identifier_info);
        tc_hooks = (uu___2063_27319.tc_hooks);
        dsenv = (uu___2063_27319.dsenv);
        nbe = (uu___2063_27319.nbe);
        strict_args_tab = (uu___2063_27319.strict_args_tab);
        erasable_types_tab = (uu___2063_27319.erasable_types_tab);
        enable_defer_to_tac = (uu___2063_27319.enable_defer_to_tac)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____27335 = FStar_Syntax_Free.names t  in
      let uu____27338 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____27335 uu____27338
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27361 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27361
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27371 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27371
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27392 =
      match uu____27392 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27412 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27412)
       in
    let uu____27420 =
      let uu____27424 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27424 FStar_List.rev  in
    FStar_All.pipe_right uu____27420 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Common.guard_f = g;
      FStar_TypeChecker_Common.deferred_to_tac = [];
      FStar_TypeChecker_Common.deferred = [];
      FStar_TypeChecker_Common.univ_ineqs = ([], []);
      FStar_TypeChecker_Common.implicits = []
    }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.FStar_TypeChecker_Common.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred_to_tac = uu____27480;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([],[]);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27498 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27498 with
                   | FStar_Pervasives_Native.Some uu____27502 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27505 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred_to_tac = uu____27515;
        FStar_TypeChecker_Common.deferred = uu____27516;
        FStar_TypeChecker_Common.univ_ineqs = uu____27517;
        FStar_TypeChecker_Common.implicits = uu____27518;_} -> true
    | uu____27528 -> false
  
let (trivial_guard : guard_t) = FStar_TypeChecker_Common.trivial_guard 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___2109_27550 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2109_27550.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2109_27550.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2109_27550.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2109_27550.FStar_TypeChecker_Common.implicits)
          }
  
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____27589 = FStar_Options.defensive ()  in
          if uu____27589
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27595 =
              let uu____27597 =
                let uu____27599 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27599  in
              Prims.op_Negation uu____27597  in
            (if uu____27595
             then
               let uu____27606 =
                 let uu____27612 =
                   let uu____27614 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27616 =
                     let uu____27618 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27618
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27614 uu____27616
                    in
                 (FStar_Errors.Warning_Defensive, uu____27612)  in
               FStar_Errors.log_issue rng uu____27606
             else ())
          else ()
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____27658 =
            let uu____27660 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27660  in
          if uu____27658
          then ()
          else
            (let uu____27665 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27665 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27691 =
            let uu____27693 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27693  in
          if uu____27691
          then ()
          else
            (let uu____27698 = bound_vars e  in
             def_check_closed_in rng msg uu____27698 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.FStar_TypeChecker_Common.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2146_27737 = g  in
          let uu____27738 =
            let uu____27739 =
              let uu____27740 =
                let uu____27747 =
                  let uu____27748 =
                    let uu____27765 =
                      let uu____27776 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27776]  in
                    (f, uu____27765)  in
                  FStar_Syntax_Syntax.Tm_app uu____27748  in
                FStar_Syntax_Syntax.mk uu____27747  in
              uu____27740 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27813  -> FStar_TypeChecker_Common.NonTrivial _27813)
              uu____27739
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27738;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2146_27737.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2146_27737.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2146_27737.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2146_27737.FStar_TypeChecker_Common.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2153_27831 = g  in
          let uu____27832 =
            let uu____27833 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27833  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27832;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2153_27831.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2153_27831.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2153_27831.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2153_27831.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2158_27850 = g  in
          let uu____27851 =
            let uu____27852 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27852  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27851;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2158_27850.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2158_27850.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2158_27850.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2158_27850.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2162_27854 = g  in
          let uu____27855 =
            let uu____27856 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27856  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27855;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2162_27854.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2162_27854.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2162_27854.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2162_27854.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27863 ->
        failwith "impossible"
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  -> FStar_TypeChecker_Common.check_trivial t 
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> FStar_TypeChecker_Common.conj_guard g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_TypeChecker_Common.conj_guards gs 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> FStar_TypeChecker_Common.imp_guard g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____27940 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27940
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2185_27947 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2185_27947.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2185_27947.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2185_27947.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2185_27947.FStar_TypeChecker_Common.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____27981 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27981
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2200_28008 = g  in
            let uu____28009 =
              let uu____28010 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____28010  in
            {
              FStar_TypeChecker_Common.guard_f = uu____28009;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2200_28008.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2200_28008.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2200_28008.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2200_28008.FStar_TypeChecker_Common.implicits)
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
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            fun meta  ->
              let uu____28060 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____28060 with
              | FStar_Pervasives_Native.Some
                  (uu____28085::(tm,uu____28087)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____28151 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____28169 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____28169;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    }  in
                  (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                     true gamma binders;
                   (let t =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uvar
                           (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                        FStar_Pervasives_Native.None r
                       in
                    let imp =
                      {
                        FStar_TypeChecker_Common.imp_reason = reason;
                        FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                        FStar_TypeChecker_Common.imp_tm = t;
                        FStar_TypeChecker_Common.imp_range = r
                      }  in
                    (let uu____28201 =
                       debug env (FStar_Options.Other "ImplicitTrace")  in
                     if uu____28201
                     then
                       let uu____28205 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____28205
                     else ());
                    (let g =
                       let uu___2224_28211 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2224_28211.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2224_28211.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2224_28211.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2224_28211.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits = [imp]
                       }  in
                     (t, [(ctx_uvar, r)], g))))
  
let (uvars_for_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.subst_t ->
        (FStar_Syntax_Syntax.binder -> Prims.string) ->
          FStar_Range.range ->
            (FStar_Syntax_Syntax.term Prims.list * guard_t))
  =
  fun env  ->
    fun bs  ->
      fun substs  ->
        fun reason  ->
          fun r  ->
            let uu____28265 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28323  ->
                      fun b  ->
                        match uu____28323 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let ctx_uvar_meta_t =
                              match FStar_Pervasives_Native.snd b with
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                  t)) ->
                                  let uu____28375 =
                                    let uu____28376 =
                                      let uu____28383 = FStar_Dyn.mkdyn env
                                         in
                                      (uu____28383, t)  in
                                    FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                      uu____28376
                                     in
                                  FStar_Pervasives_Native.Some uu____28375
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr t)
                              | uu____28389 -> FStar_Pervasives_Native.None
                               in
                            let uu____28392 =
                              let uu____28405 = reason b  in
                              new_implicit_var_aux uu____28405 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                ctx_uvar_meta_t
                               in
                            (match uu____28392 with
                             | (t,uu____28418,g_t) ->
                                 let uu____28432 =
                                   let uu____28435 =
                                     let uu____28438 =
                                       let uu____28439 =
                                         let uu____28446 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28446, t)  in
                                       FStar_Syntax_Syntax.NT uu____28439  in
                                     [uu____28438]  in
                                   FStar_List.append substs1 uu____28435  in
                                 let uu____28457 = conj_guard g g_t  in
                                 (uu____28432,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28457))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____28265
              (fun uu____28486  ->
                 match uu____28486 with
                 | (uu____28503,uvars1,g) -> (uvars1, g))
  
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        fun wp  ->
          fun r  ->
            let trivial_post =
              let post_ts =
                let uu____28544 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28544 FStar_Util.must  in
              let uu____28561 = inst_tscheme_with post_ts [u]  in
              match uu____28561 with
              | (uu____28566,post) ->
                  let uu____28568 =
                    let uu____28573 =
                      let uu____28574 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28574]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28573  in
                  uu____28568 FStar_Pervasives_Native.None r
               in
            let uu____28607 =
              let uu____28612 =
                let uu____28613 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28613]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28612  in
            uu____28607 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28649  -> ());
    push = (fun uu____28651  -> ());
    pop = (fun uu____28654  -> ());
    snapshot =
      (fun uu____28657  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28676  -> fun uu____28677  -> ());
    encode_sig = (fun uu____28692  -> fun uu____28693  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28699 =
             let uu____28706 = FStar_Options.peek ()  in (e, g, uu____28706)
              in
           [uu____28699]);
    solve = (fun uu____28722  -> fun uu____28723  -> fun uu____28724  -> ());
    finish = (fun uu____28731  -> ());
    refresh = (fun uu____28733  -> ())
  } 