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
  | ReduceDivLets 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____106 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____117 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____128 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____140 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____158 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____169 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____180 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____191 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____202 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____213 -> false
  
let (uu___is_ReduceDivLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReduceDivLets  -> true | uu____224 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____236 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____257 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____284 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____311 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____335 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____346 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____357 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____368 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____379 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____390 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____401 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____412 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____423 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____434 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____445 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____456 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____467 -> false
  
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
      | (ReduceDivLets ,ReduceDivLets ) -> true
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
      | uu____528 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____554 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____565 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____576 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____588 -> false
  
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
  erasable_types_tab: Prims.bool FStar_Util.smap }
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
        strict_args_tab; erasable_types_tab;_} -> solver
  
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
        strict_args_tab; erasable_types_tab;_} -> range
  
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
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
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
        strict_args_tab; erasable_types_tab;_} -> gamma
  
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
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
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
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
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
        strict_args_tab; erasable_types_tab;_} -> modules
  
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
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
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
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
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
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
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
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
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
        strict_args_tab; erasable_types_tab;_} -> effects
  
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
        strict_args_tab; erasable_types_tab;_} -> generalize
  
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
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
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
        strict_args_tab; erasable_types_tab;_} -> top_level
  
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
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
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
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
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
        strict_args_tab; erasable_types_tab;_} -> use_eq_strict
  
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
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
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
        strict_args_tab; erasable_types_tab;_} -> admit1
  
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
        strict_args_tab; erasable_types_tab;_} -> lax1
  
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
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
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
        strict_args_tab; erasable_types_tab;_} -> phase1
  
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
        strict_args_tab; erasable_types_tab;_} -> failhard
  
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
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
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
        strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
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
        strict_args_tab; erasable_types_tab;_} -> tc_term
  
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
        strict_args_tab; erasable_types_tab;_} -> type_of
  
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
        strict_args_tab; erasable_types_tab;_} -> universe_of
  
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
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
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
        strict_args_tab; erasable_types_tab;_} -> use_bv_sorts
  
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
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
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
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
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
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
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
        strict_args_tab; erasable_types_tab;_} -> proof_ns
  
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
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
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
        strict_args_tab; erasable_types_tab;_} -> try_solve_implicits_hook
  
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
        strict_args_tab; erasable_types_tab;_} -> splice1
  
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
        strict_args_tab; erasable_types_tab;_} -> mpreprocess
  
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
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
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
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
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
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
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
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
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
        strict_args_tab; erasable_types_tab;_} -> dsenv
  
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
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
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
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
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
        strict_args_tab; erasable_types_tab;_} -> erasable_types_tab
  
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
           (fun uu___0_14374  ->
              match uu___0_14374 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14377 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14377  in
                  let uu____14378 =
                    let uu____14379 = FStar_Syntax_Subst.compress y  in
                    uu____14379.FStar_Syntax_Syntax.n  in
                  (match uu____14378 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14383 =
                         let uu___327_14384 = y1  in
                         let uu____14385 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14384.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14384.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14385
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14383
                   | uu____14388 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___333_14402 = env  in
      let uu____14403 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___333_14402.solver);
        range = (uu___333_14402.range);
        curmodule = (uu___333_14402.curmodule);
        gamma = uu____14403;
        gamma_sig = (uu___333_14402.gamma_sig);
        gamma_cache = (uu___333_14402.gamma_cache);
        modules = (uu___333_14402.modules);
        expected_typ = (uu___333_14402.expected_typ);
        sigtab = (uu___333_14402.sigtab);
        attrtab = (uu___333_14402.attrtab);
        instantiate_imp = (uu___333_14402.instantiate_imp);
        effects = (uu___333_14402.effects);
        generalize = (uu___333_14402.generalize);
        letrecs = (uu___333_14402.letrecs);
        top_level = (uu___333_14402.top_level);
        check_uvars = (uu___333_14402.check_uvars);
        use_eq = (uu___333_14402.use_eq);
        use_eq_strict = (uu___333_14402.use_eq_strict);
        is_iface = (uu___333_14402.is_iface);
        admit = (uu___333_14402.admit);
        lax = (uu___333_14402.lax);
        lax_universes = (uu___333_14402.lax_universes);
        phase1 = (uu___333_14402.phase1);
        failhard = (uu___333_14402.failhard);
        nosynth = (uu___333_14402.nosynth);
        uvar_subtyping = (uu___333_14402.uvar_subtyping);
        tc_term = (uu___333_14402.tc_term);
        type_of = (uu___333_14402.type_of);
        universe_of = (uu___333_14402.universe_of);
        check_type_of = (uu___333_14402.check_type_of);
        use_bv_sorts = (uu___333_14402.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14402.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14402.normalized_eff_names);
        fv_delta_depths = (uu___333_14402.fv_delta_depths);
        proof_ns = (uu___333_14402.proof_ns);
        synth_hook = (uu___333_14402.synth_hook);
        try_solve_implicits_hook = (uu___333_14402.try_solve_implicits_hook);
        splice = (uu___333_14402.splice);
        mpreprocess = (uu___333_14402.mpreprocess);
        postprocess = (uu___333_14402.postprocess);
        is_native_tactic = (uu___333_14402.is_native_tactic);
        identifier_info = (uu___333_14402.identifier_info);
        tc_hooks = (uu___333_14402.tc_hooks);
        dsenv = (uu___333_14402.dsenv);
        nbe = (uu___333_14402.nbe);
        strict_args_tab = (uu___333_14402.strict_args_tab);
        erasable_types_tab = (uu___333_14402.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14411  -> fun uu____14412  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___340_14434 = env  in
      {
        solver = (uu___340_14434.solver);
        range = (uu___340_14434.range);
        curmodule = (uu___340_14434.curmodule);
        gamma = (uu___340_14434.gamma);
        gamma_sig = (uu___340_14434.gamma_sig);
        gamma_cache = (uu___340_14434.gamma_cache);
        modules = (uu___340_14434.modules);
        expected_typ = (uu___340_14434.expected_typ);
        sigtab = (uu___340_14434.sigtab);
        attrtab = (uu___340_14434.attrtab);
        instantiate_imp = (uu___340_14434.instantiate_imp);
        effects = (uu___340_14434.effects);
        generalize = (uu___340_14434.generalize);
        letrecs = (uu___340_14434.letrecs);
        top_level = (uu___340_14434.top_level);
        check_uvars = (uu___340_14434.check_uvars);
        use_eq = (uu___340_14434.use_eq);
        use_eq_strict = (uu___340_14434.use_eq_strict);
        is_iface = (uu___340_14434.is_iface);
        admit = (uu___340_14434.admit);
        lax = (uu___340_14434.lax);
        lax_universes = (uu___340_14434.lax_universes);
        phase1 = (uu___340_14434.phase1);
        failhard = (uu___340_14434.failhard);
        nosynth = (uu___340_14434.nosynth);
        uvar_subtyping = (uu___340_14434.uvar_subtyping);
        tc_term = (uu___340_14434.tc_term);
        type_of = (uu___340_14434.type_of);
        universe_of = (uu___340_14434.universe_of);
        check_type_of = (uu___340_14434.check_type_of);
        use_bv_sorts = (uu___340_14434.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14434.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14434.normalized_eff_names);
        fv_delta_depths = (uu___340_14434.fv_delta_depths);
        proof_ns = (uu___340_14434.proof_ns);
        synth_hook = (uu___340_14434.synth_hook);
        try_solve_implicits_hook = (uu___340_14434.try_solve_implicits_hook);
        splice = (uu___340_14434.splice);
        mpreprocess = (uu___340_14434.mpreprocess);
        postprocess = (uu___340_14434.postprocess);
        is_native_tactic = (uu___340_14434.is_native_tactic);
        identifier_info = (uu___340_14434.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14434.dsenv);
        nbe = (uu___340_14434.nbe);
        strict_args_tab = (uu___340_14434.strict_args_tab);
        erasable_types_tab = (uu___340_14434.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___344_14446 = e  in
      let uu____14447 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___344_14446.solver);
        range = (uu___344_14446.range);
        curmodule = (uu___344_14446.curmodule);
        gamma = (uu___344_14446.gamma);
        gamma_sig = (uu___344_14446.gamma_sig);
        gamma_cache = (uu___344_14446.gamma_cache);
        modules = (uu___344_14446.modules);
        expected_typ = (uu___344_14446.expected_typ);
        sigtab = (uu___344_14446.sigtab);
        attrtab = (uu___344_14446.attrtab);
        instantiate_imp = (uu___344_14446.instantiate_imp);
        effects = (uu___344_14446.effects);
        generalize = (uu___344_14446.generalize);
        letrecs = (uu___344_14446.letrecs);
        top_level = (uu___344_14446.top_level);
        check_uvars = (uu___344_14446.check_uvars);
        use_eq = (uu___344_14446.use_eq);
        use_eq_strict = (uu___344_14446.use_eq_strict);
        is_iface = (uu___344_14446.is_iface);
        admit = (uu___344_14446.admit);
        lax = (uu___344_14446.lax);
        lax_universes = (uu___344_14446.lax_universes);
        phase1 = (uu___344_14446.phase1);
        failhard = (uu___344_14446.failhard);
        nosynth = (uu___344_14446.nosynth);
        uvar_subtyping = (uu___344_14446.uvar_subtyping);
        tc_term = (uu___344_14446.tc_term);
        type_of = (uu___344_14446.type_of);
        universe_of = (uu___344_14446.universe_of);
        check_type_of = (uu___344_14446.check_type_of);
        use_bv_sorts = (uu___344_14446.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14446.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14446.normalized_eff_names);
        fv_delta_depths = (uu___344_14446.fv_delta_depths);
        proof_ns = (uu___344_14446.proof_ns);
        synth_hook = (uu___344_14446.synth_hook);
        try_solve_implicits_hook = (uu___344_14446.try_solve_implicits_hook);
        splice = (uu___344_14446.splice);
        mpreprocess = (uu___344_14446.mpreprocess);
        postprocess = (uu___344_14446.postprocess);
        is_native_tactic = (uu___344_14446.is_native_tactic);
        identifier_info = (uu___344_14446.identifier_info);
        tc_hooks = (uu___344_14446.tc_hooks);
        dsenv = uu____14447;
        nbe = (uu___344_14446.nbe);
        strict_args_tab = (uu___344_14446.strict_args_tab);
        erasable_types_tab = (uu___344_14446.erasable_types_tab)
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
      | (NoDelta ,uu____14476) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14479,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14481,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14484 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14498 . unit -> 'Auu____14498 FStar_Util.smap =
  fun uu____14505  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14511 . unit -> 'Auu____14511 FStar_Util.smap =
  fun uu____14518  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14656 = new_gamma_cache ()  in
                  let uu____14659 = new_sigtab ()  in
                  let uu____14662 = new_sigtab ()  in
                  let uu____14669 =
                    let uu____14684 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14684, FStar_Pervasives_Native.None)  in
                  let uu____14705 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14709 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14713 = FStar_Options.using_facts_from ()  in
                  let uu____14714 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14717 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14718 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14732 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14656;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14659;
                    attrtab = uu____14662;
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
                    qtbl_name_and_index = uu____14669;
                    normalized_eff_names = uu____14705;
                    fv_delta_depths = uu____14709;
                    proof_ns = uu____14713;
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
                    is_native_tactic = (fun uu____14847  -> false);
                    identifier_info = uu____14714;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14717;
                    nbe = nbe1;
                    strict_args_tab = uu____14718;
                    erasable_types_tab = uu____14732
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
  fun uu____14926  ->
    let uu____14927 = FStar_ST.op_Bang query_indices  in
    match uu____14927 with
    | [] -> failwith "Empty query indices!"
    | uu____14982 ->
        let uu____14992 =
          let uu____15002 =
            let uu____15010 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____15010  in
          let uu____15064 = FStar_ST.op_Bang query_indices  in uu____15002 ::
            uu____15064
           in
        FStar_ST.op_Colon_Equals query_indices uu____14992
  
let (pop_query_indices : unit -> unit) =
  fun uu____15160  ->
    let uu____15161 = FStar_ST.op_Bang query_indices  in
    match uu____15161 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15288  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15325  ->
    match uu____15325 with
    | (l,n1) ->
        let uu____15335 = FStar_ST.op_Bang query_indices  in
        (match uu____15335 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15457 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15480  ->
    let uu____15481 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15481
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15549 =
       let uu____15552 = FStar_ST.op_Bang stack  in env :: uu____15552  in
     FStar_ST.op_Colon_Equals stack uu____15549);
    (let uu___418_15601 = env  in
     let uu____15602 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15605 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15608 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15615 =
       let uu____15630 =
         let uu____15634 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15634  in
       let uu____15666 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15630, uu____15666)  in
     let uu____15715 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____15718 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____15721 =
       let uu____15724 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____15724  in
     let uu____15744 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15757 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___418_15601.solver);
       range = (uu___418_15601.range);
       curmodule = (uu___418_15601.curmodule);
       gamma = (uu___418_15601.gamma);
       gamma_sig = (uu___418_15601.gamma_sig);
       gamma_cache = uu____15602;
       modules = (uu___418_15601.modules);
       expected_typ = (uu___418_15601.expected_typ);
       sigtab = uu____15605;
       attrtab = uu____15608;
       instantiate_imp = (uu___418_15601.instantiate_imp);
       effects = (uu___418_15601.effects);
       generalize = (uu___418_15601.generalize);
       letrecs = (uu___418_15601.letrecs);
       top_level = (uu___418_15601.top_level);
       check_uvars = (uu___418_15601.check_uvars);
       use_eq = (uu___418_15601.use_eq);
       use_eq_strict = (uu___418_15601.use_eq_strict);
       is_iface = (uu___418_15601.is_iface);
       admit = (uu___418_15601.admit);
       lax = (uu___418_15601.lax);
       lax_universes = (uu___418_15601.lax_universes);
       phase1 = (uu___418_15601.phase1);
       failhard = (uu___418_15601.failhard);
       nosynth = (uu___418_15601.nosynth);
       uvar_subtyping = (uu___418_15601.uvar_subtyping);
       tc_term = (uu___418_15601.tc_term);
       type_of = (uu___418_15601.type_of);
       universe_of = (uu___418_15601.universe_of);
       check_type_of = (uu___418_15601.check_type_of);
       use_bv_sorts = (uu___418_15601.use_bv_sorts);
       qtbl_name_and_index = uu____15615;
       normalized_eff_names = uu____15715;
       fv_delta_depths = uu____15718;
       proof_ns = (uu___418_15601.proof_ns);
       synth_hook = (uu___418_15601.synth_hook);
       try_solve_implicits_hook = (uu___418_15601.try_solve_implicits_hook);
       splice = (uu___418_15601.splice);
       mpreprocess = (uu___418_15601.mpreprocess);
       postprocess = (uu___418_15601.postprocess);
       is_native_tactic = (uu___418_15601.is_native_tactic);
       identifier_info = uu____15721;
       tc_hooks = (uu___418_15601.tc_hooks);
       dsenv = (uu___418_15601.dsenv);
       nbe = (uu___418_15601.nbe);
       strict_args_tab = uu____15744;
       erasable_types_tab = uu____15757
     })
  
let (pop_stack : unit -> env) =
  fun uu____15767  ->
    let uu____15768 = FStar_ST.op_Bang stack  in
    match uu____15768 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15822 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15912  ->
           let uu____15913 = snapshot_stack env  in
           match uu____15913 with
           | (stack_depth,env1) ->
               let uu____15947 = snapshot_query_indices ()  in
               (match uu____15947 with
                | (query_indices_depth,()) ->
                    let uu____15980 = (env1.solver).snapshot msg  in
                    (match uu____15980 with
                     | (solver_depth,()) ->
                         let uu____16037 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____16037 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_16104 = env1  in
                                 {
                                   solver = (uu___443_16104.solver);
                                   range = (uu___443_16104.range);
                                   curmodule = (uu___443_16104.curmodule);
                                   gamma = (uu___443_16104.gamma);
                                   gamma_sig = (uu___443_16104.gamma_sig);
                                   gamma_cache = (uu___443_16104.gamma_cache);
                                   modules = (uu___443_16104.modules);
                                   expected_typ =
                                     (uu___443_16104.expected_typ);
                                   sigtab = (uu___443_16104.sigtab);
                                   attrtab = (uu___443_16104.attrtab);
                                   instantiate_imp =
                                     (uu___443_16104.instantiate_imp);
                                   effects = (uu___443_16104.effects);
                                   generalize = (uu___443_16104.generalize);
                                   letrecs = (uu___443_16104.letrecs);
                                   top_level = (uu___443_16104.top_level);
                                   check_uvars = (uu___443_16104.check_uvars);
                                   use_eq = (uu___443_16104.use_eq);
                                   use_eq_strict =
                                     (uu___443_16104.use_eq_strict);
                                   is_iface = (uu___443_16104.is_iface);
                                   admit = (uu___443_16104.admit);
                                   lax = (uu___443_16104.lax);
                                   lax_universes =
                                     (uu___443_16104.lax_universes);
                                   phase1 = (uu___443_16104.phase1);
                                   failhard = (uu___443_16104.failhard);
                                   nosynth = (uu___443_16104.nosynth);
                                   uvar_subtyping =
                                     (uu___443_16104.uvar_subtyping);
                                   tc_term = (uu___443_16104.tc_term);
                                   type_of = (uu___443_16104.type_of);
                                   universe_of = (uu___443_16104.universe_of);
                                   check_type_of =
                                     (uu___443_16104.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_16104.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_16104.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_16104.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_16104.fv_delta_depths);
                                   proof_ns = (uu___443_16104.proof_ns);
                                   synth_hook = (uu___443_16104.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_16104.try_solve_implicits_hook);
                                   splice = (uu___443_16104.splice);
                                   mpreprocess = (uu___443_16104.mpreprocess);
                                   postprocess = (uu___443_16104.postprocess);
                                   is_native_tactic =
                                     (uu___443_16104.is_native_tactic);
                                   identifier_info =
                                     (uu___443_16104.identifier_info);
                                   tc_hooks = (uu___443_16104.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_16104.nbe);
                                   strict_args_tab =
                                     (uu___443_16104.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_16104.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16138  ->
             let uu____16139 =
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
             match uu____16139 with
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
                             ((let uu____16319 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16319
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____16335 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____16335
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16367,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16409 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16439  ->
                  match uu____16439 with
                  | (m,uu____16447) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16409 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___488_16462 = env  in
               {
                 solver = (uu___488_16462.solver);
                 range = (uu___488_16462.range);
                 curmodule = (uu___488_16462.curmodule);
                 gamma = (uu___488_16462.gamma);
                 gamma_sig = (uu___488_16462.gamma_sig);
                 gamma_cache = (uu___488_16462.gamma_cache);
                 modules = (uu___488_16462.modules);
                 expected_typ = (uu___488_16462.expected_typ);
                 sigtab = (uu___488_16462.sigtab);
                 attrtab = (uu___488_16462.attrtab);
                 instantiate_imp = (uu___488_16462.instantiate_imp);
                 effects = (uu___488_16462.effects);
                 generalize = (uu___488_16462.generalize);
                 letrecs = (uu___488_16462.letrecs);
                 top_level = (uu___488_16462.top_level);
                 check_uvars = (uu___488_16462.check_uvars);
                 use_eq = (uu___488_16462.use_eq);
                 use_eq_strict = (uu___488_16462.use_eq_strict);
                 is_iface = (uu___488_16462.is_iface);
                 admit = (uu___488_16462.admit);
                 lax = (uu___488_16462.lax);
                 lax_universes = (uu___488_16462.lax_universes);
                 phase1 = (uu___488_16462.phase1);
                 failhard = (uu___488_16462.failhard);
                 nosynth = (uu___488_16462.nosynth);
                 uvar_subtyping = (uu___488_16462.uvar_subtyping);
                 tc_term = (uu___488_16462.tc_term);
                 type_of = (uu___488_16462.type_of);
                 universe_of = (uu___488_16462.universe_of);
                 check_type_of = (uu___488_16462.check_type_of);
                 use_bv_sorts = (uu___488_16462.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16462.normalized_eff_names);
                 fv_delta_depths = (uu___488_16462.fv_delta_depths);
                 proof_ns = (uu___488_16462.proof_ns);
                 synth_hook = (uu___488_16462.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16462.try_solve_implicits_hook);
                 splice = (uu___488_16462.splice);
                 mpreprocess = (uu___488_16462.mpreprocess);
                 postprocess = (uu___488_16462.postprocess);
                 is_native_tactic = (uu___488_16462.is_native_tactic);
                 identifier_info = (uu___488_16462.identifier_info);
                 tc_hooks = (uu___488_16462.tc_hooks);
                 dsenv = (uu___488_16462.dsenv);
                 nbe = (uu___488_16462.nbe);
                 strict_args_tab = (uu___488_16462.strict_args_tab);
                 erasable_types_tab = (uu___488_16462.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16479,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___497_16495 = env  in
               {
                 solver = (uu___497_16495.solver);
                 range = (uu___497_16495.range);
                 curmodule = (uu___497_16495.curmodule);
                 gamma = (uu___497_16495.gamma);
                 gamma_sig = (uu___497_16495.gamma_sig);
                 gamma_cache = (uu___497_16495.gamma_cache);
                 modules = (uu___497_16495.modules);
                 expected_typ = (uu___497_16495.expected_typ);
                 sigtab = (uu___497_16495.sigtab);
                 attrtab = (uu___497_16495.attrtab);
                 instantiate_imp = (uu___497_16495.instantiate_imp);
                 effects = (uu___497_16495.effects);
                 generalize = (uu___497_16495.generalize);
                 letrecs = (uu___497_16495.letrecs);
                 top_level = (uu___497_16495.top_level);
                 check_uvars = (uu___497_16495.check_uvars);
                 use_eq = (uu___497_16495.use_eq);
                 use_eq_strict = (uu___497_16495.use_eq_strict);
                 is_iface = (uu___497_16495.is_iface);
                 admit = (uu___497_16495.admit);
                 lax = (uu___497_16495.lax);
                 lax_universes = (uu___497_16495.lax_universes);
                 phase1 = (uu___497_16495.phase1);
                 failhard = (uu___497_16495.failhard);
                 nosynth = (uu___497_16495.nosynth);
                 uvar_subtyping = (uu___497_16495.uvar_subtyping);
                 tc_term = (uu___497_16495.tc_term);
                 type_of = (uu___497_16495.type_of);
                 universe_of = (uu___497_16495.universe_of);
                 check_type_of = (uu___497_16495.check_type_of);
                 use_bv_sorts = (uu___497_16495.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16495.normalized_eff_names);
                 fv_delta_depths = (uu___497_16495.fv_delta_depths);
                 proof_ns = (uu___497_16495.proof_ns);
                 synth_hook = (uu___497_16495.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16495.try_solve_implicits_hook);
                 splice = (uu___497_16495.splice);
                 mpreprocess = (uu___497_16495.mpreprocess);
                 postprocess = (uu___497_16495.postprocess);
                 is_native_tactic = (uu___497_16495.is_native_tactic);
                 identifier_info = (uu___497_16495.identifier_info);
                 tc_hooks = (uu___497_16495.tc_hooks);
                 dsenv = (uu___497_16495.dsenv);
                 nbe = (uu___497_16495.nbe);
                 strict_args_tab = (uu___497_16495.strict_args_tab);
                 erasable_types_tab = (uu___497_16495.erasable_types_tab)
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
        (let uu___504_16538 = e  in
         {
           solver = (uu___504_16538.solver);
           range = r;
           curmodule = (uu___504_16538.curmodule);
           gamma = (uu___504_16538.gamma);
           gamma_sig = (uu___504_16538.gamma_sig);
           gamma_cache = (uu___504_16538.gamma_cache);
           modules = (uu___504_16538.modules);
           expected_typ = (uu___504_16538.expected_typ);
           sigtab = (uu___504_16538.sigtab);
           attrtab = (uu___504_16538.attrtab);
           instantiate_imp = (uu___504_16538.instantiate_imp);
           effects = (uu___504_16538.effects);
           generalize = (uu___504_16538.generalize);
           letrecs = (uu___504_16538.letrecs);
           top_level = (uu___504_16538.top_level);
           check_uvars = (uu___504_16538.check_uvars);
           use_eq = (uu___504_16538.use_eq);
           use_eq_strict = (uu___504_16538.use_eq_strict);
           is_iface = (uu___504_16538.is_iface);
           admit = (uu___504_16538.admit);
           lax = (uu___504_16538.lax);
           lax_universes = (uu___504_16538.lax_universes);
           phase1 = (uu___504_16538.phase1);
           failhard = (uu___504_16538.failhard);
           nosynth = (uu___504_16538.nosynth);
           uvar_subtyping = (uu___504_16538.uvar_subtyping);
           tc_term = (uu___504_16538.tc_term);
           type_of = (uu___504_16538.type_of);
           universe_of = (uu___504_16538.universe_of);
           check_type_of = (uu___504_16538.check_type_of);
           use_bv_sorts = (uu___504_16538.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16538.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16538.normalized_eff_names);
           fv_delta_depths = (uu___504_16538.fv_delta_depths);
           proof_ns = (uu___504_16538.proof_ns);
           synth_hook = (uu___504_16538.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16538.try_solve_implicits_hook);
           splice = (uu___504_16538.splice);
           mpreprocess = (uu___504_16538.mpreprocess);
           postprocess = (uu___504_16538.postprocess);
           is_native_tactic = (uu___504_16538.is_native_tactic);
           identifier_info = (uu___504_16538.identifier_info);
           tc_hooks = (uu___504_16538.tc_hooks);
           dsenv = (uu___504_16538.dsenv);
           nbe = (uu___504_16538.nbe);
           strict_args_tab = (uu___504_16538.strict_args_tab);
           erasable_types_tab = (uu___504_16538.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16558 =
        let uu____16559 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16559 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16558
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16614 =
          let uu____16615 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16615 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16614
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16670 =
          let uu____16671 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16671 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16670
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16726 =
        let uu____16727 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16727 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16726
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___521_16791 = env  in
      {
        solver = (uu___521_16791.solver);
        range = (uu___521_16791.range);
        curmodule = lid;
        gamma = (uu___521_16791.gamma);
        gamma_sig = (uu___521_16791.gamma_sig);
        gamma_cache = (uu___521_16791.gamma_cache);
        modules = (uu___521_16791.modules);
        expected_typ = (uu___521_16791.expected_typ);
        sigtab = (uu___521_16791.sigtab);
        attrtab = (uu___521_16791.attrtab);
        instantiate_imp = (uu___521_16791.instantiate_imp);
        effects = (uu___521_16791.effects);
        generalize = (uu___521_16791.generalize);
        letrecs = (uu___521_16791.letrecs);
        top_level = (uu___521_16791.top_level);
        check_uvars = (uu___521_16791.check_uvars);
        use_eq = (uu___521_16791.use_eq);
        use_eq_strict = (uu___521_16791.use_eq_strict);
        is_iface = (uu___521_16791.is_iface);
        admit = (uu___521_16791.admit);
        lax = (uu___521_16791.lax);
        lax_universes = (uu___521_16791.lax_universes);
        phase1 = (uu___521_16791.phase1);
        failhard = (uu___521_16791.failhard);
        nosynth = (uu___521_16791.nosynth);
        uvar_subtyping = (uu___521_16791.uvar_subtyping);
        tc_term = (uu___521_16791.tc_term);
        type_of = (uu___521_16791.type_of);
        universe_of = (uu___521_16791.universe_of);
        check_type_of = (uu___521_16791.check_type_of);
        use_bv_sorts = (uu___521_16791.use_bv_sorts);
        qtbl_name_and_index = (uu___521_16791.qtbl_name_and_index);
        normalized_eff_names = (uu___521_16791.normalized_eff_names);
        fv_delta_depths = (uu___521_16791.fv_delta_depths);
        proof_ns = (uu___521_16791.proof_ns);
        synth_hook = (uu___521_16791.synth_hook);
        try_solve_implicits_hook = (uu___521_16791.try_solve_implicits_hook);
        splice = (uu___521_16791.splice);
        mpreprocess = (uu___521_16791.mpreprocess);
        postprocess = (uu___521_16791.postprocess);
        is_native_tactic = (uu___521_16791.is_native_tactic);
        identifier_info = (uu___521_16791.identifier_info);
        tc_hooks = (uu___521_16791.tc_hooks);
        dsenv = (uu___521_16791.dsenv);
        nbe = (uu___521_16791.nbe);
        strict_args_tab = (uu___521_16791.strict_args_tab);
        erasable_types_tab = (uu___521_16791.erasable_types_tab)
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
      let uu____16822 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16822
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16835 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16835)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16850 =
      let uu____16852 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16852  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16850)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16861  ->
    let uu____16862 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16862
  
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
      | ((formals,t),uu____16962) ->
          let vs = mk_univ_subst formals us  in
          let uu____16986 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16986)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17003  ->
    match uu___1_17003 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17029  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17049 = inst_tscheme t  in
      match uu____17049 with
      | (us,t1) ->
          let uu____17060 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17060)
  
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
          let uu____17085 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17087 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17085 uu____17087
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
        fun uu____17114  ->
          match uu____17114 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17128 =
                    let uu____17130 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17134 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17138 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17140 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17130 uu____17134 uu____17138 uu____17140
                     in
                  failwith uu____17128)
               else ();
               (let uu____17145 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17145))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17163 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17174 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17185 -> false
  
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
             | ([],uu____17233) -> Maybe
             | (uu____17240,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____17260 -> No  in
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
          let uu____17354 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____17354 with
          | FStar_Pervasives_Native.None  ->
              let uu____17377 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17421  ->
                     match uu___2_17421 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17460 = FStar_Ident.lid_equals lid l  in
                         if uu____17460
                         then
                           let uu____17483 =
                             let uu____17502 =
                               let uu____17517 = inst_tscheme t  in
                               FStar_Util.Inl uu____17517  in
                             let uu____17532 = FStar_Ident.range_of_lid l  in
                             (uu____17502, uu____17532)  in
                           FStar_Pervasives_Native.Some uu____17483
                         else FStar_Pervasives_Native.None
                     | uu____17585 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17377
                (fun uu____17623  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17633  ->
                        match uu___3_17633 with
                        | (uu____17636,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17638);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17639;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17640;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17641;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17642;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17643;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17665 =
                                   let uu____17667 =
                                     FStar_Syntax_Util.lids_of_sigelt se  in
                                   FStar_All.pipe_right uu____17667
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17665
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
                                  uu____17720 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17727 -> cache t  in
                            let uu____17728 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17728 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17734 =
                                   let uu____17735 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17735)
                                    in
                                 maybe_cache uu____17734)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17806 = find_in_sigtab env lid  in
         match uu____17806 with
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
      let uu____17887 = lookup_qname env lid  in
      match uu____17887 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17908,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____18022 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____18022 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18067 =
          let uu____18070 = lookup_attr env1 attr  in se1 :: uu____18070  in
        FStar_Util.smap_add (attrtab env1) attr uu____18067  in
      FStar_List.iter
        (fun attr  ->
           let uu____18080 =
             let uu____18081 = FStar_Syntax_Subst.compress attr  in
             uu____18081.FStar_Syntax_Syntax.n  in
           match uu____18080 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18085 =
                 let uu____18087 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18087.FStar_Ident.str  in
               add_one1 env se uu____18085
           | uu____18088 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18111) ->
          add_sigelts env ses
      | uu____18120 ->
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
        (fun uu___4_18158  ->
           match uu___4_18158 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18176 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18238,lb::[]),uu____18240) ->
            let uu____18249 =
              let uu____18258 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18267 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18258, uu____18267)  in
            FStar_Pervasives_Native.Some uu____18249
        | FStar_Syntax_Syntax.Sig_let ((uu____18280,lbs),uu____18282) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18314 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18327 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18327
                     then
                       let uu____18340 =
                         let uu____18349 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18358 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18349, uu____18358)  in
                       FStar_Pervasives_Native.Some uu____18340
                     else FStar_Pervasives_Native.None)
        | uu____18381 -> FStar_Pervasives_Native.None
  
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
                    let uu____18473 =
                      let uu____18475 =
                        let uu____18477 =
                          let uu____18479 =
                            let uu____18481 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18487 =
                              let uu____18489 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18489  in
                            Prims.op_Hat uu____18481 uu____18487  in
                          Prims.op_Hat ", expected " uu____18479  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18477
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18475
                       in
                    failwith uu____18473
                  else ());
             (let uu____18496 =
                let uu____18505 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18505, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18496))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18525,uu____18526) ->
            let uu____18531 =
              let uu____18540 =
                let uu____18545 =
                  let uu____18546 =
                    let uu____18549 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18549  in
                  (us, uu____18546)  in
                inst_ts us_opt uu____18545  in
              (uu____18540, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18531
        | uu____18568 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18657 =
          match uu____18657 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18753,uvs,t,uu____18756,uu____18757,uu____18758);
                      FStar_Syntax_Syntax.sigrng = uu____18759;
                      FStar_Syntax_Syntax.sigquals = uu____18760;
                      FStar_Syntax_Syntax.sigmeta = uu____18761;
                      FStar_Syntax_Syntax.sigattrs = uu____18762;
                      FStar_Syntax_Syntax.sigopts = uu____18763;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18788 =
                     let uu____18797 = inst_tscheme1 (uvs, t)  in
                     (uu____18797, rng)  in
                   FStar_Pervasives_Native.Some uu____18788
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18821;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18823;
                      FStar_Syntax_Syntax.sigattrs = uu____18824;
                      FStar_Syntax_Syntax.sigopts = uu____18825;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18844 =
                     let uu____18846 = in_cur_mod env l  in uu____18846 = Yes
                      in
                   if uu____18844
                   then
                     let uu____18858 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18858
                      then
                        let uu____18874 =
                          let uu____18883 = inst_tscheme1 (uvs, t)  in
                          (uu____18883, rng)  in
                        FStar_Pervasives_Native.Some uu____18874
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18916 =
                        let uu____18925 = inst_tscheme1 (uvs, t)  in
                        (uu____18925, rng)  in
                      FStar_Pervasives_Native.Some uu____18916)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18950,uu____18951);
                      FStar_Syntax_Syntax.sigrng = uu____18952;
                      FStar_Syntax_Syntax.sigquals = uu____18953;
                      FStar_Syntax_Syntax.sigmeta = uu____18954;
                      FStar_Syntax_Syntax.sigattrs = uu____18955;
                      FStar_Syntax_Syntax.sigopts = uu____18956;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18999 =
                          let uu____19008 = inst_tscheme1 (uvs, k)  in
                          (uu____19008, rng)  in
                        FStar_Pervasives_Native.Some uu____18999
                    | uu____19029 ->
                        let uu____19030 =
                          let uu____19039 =
                            let uu____19044 =
                              let uu____19045 =
                                let uu____19048 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19048
                                 in
                              (uvs, uu____19045)  in
                            inst_tscheme1 uu____19044  in
                          (uu____19039, rng)  in
                        FStar_Pervasives_Native.Some uu____19030)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19071,uu____19072);
                      FStar_Syntax_Syntax.sigrng = uu____19073;
                      FStar_Syntax_Syntax.sigquals = uu____19074;
                      FStar_Syntax_Syntax.sigmeta = uu____19075;
                      FStar_Syntax_Syntax.sigattrs = uu____19076;
                      FStar_Syntax_Syntax.sigopts = uu____19077;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19121 =
                          let uu____19130 = inst_tscheme_with (uvs, k) us  in
                          (uu____19130, rng)  in
                        FStar_Pervasives_Native.Some uu____19121
                    | uu____19151 ->
                        let uu____19152 =
                          let uu____19161 =
                            let uu____19166 =
                              let uu____19167 =
                                let uu____19170 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19170
                                 in
                              (uvs, uu____19167)  in
                            inst_tscheme_with uu____19166 us  in
                          (uu____19161, rng)  in
                        FStar_Pervasives_Native.Some uu____19152)
               | FStar_Util.Inr se ->
                   let uu____19206 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19227;
                          FStar_Syntax_Syntax.sigrng = uu____19228;
                          FStar_Syntax_Syntax.sigquals = uu____19229;
                          FStar_Syntax_Syntax.sigmeta = uu____19230;
                          FStar_Syntax_Syntax.sigattrs = uu____19231;
                          FStar_Syntax_Syntax.sigopts = uu____19232;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19249 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19206
                     (FStar_Util.map_option
                        (fun uu____19297  ->
                           match uu____19297 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19328 =
          let uu____19339 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19339 mapper  in
        match uu____19328 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19413 =
              let uu____19424 =
                let uu____19431 =
                  let uu___858_19434 = t  in
                  let uu____19435 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19434.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19435;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19434.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19431)  in
              (uu____19424, r)  in
            FStar_Pervasives_Native.Some uu____19413
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19484 = lookup_qname env l  in
      match uu____19484 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19505 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19559 = try_lookup_bv env bv  in
      match uu____19559 with
      | FStar_Pervasives_Native.None  ->
          let uu____19574 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19574 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19590 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19591 =
            let uu____19592 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19592  in
          (uu____19590, uu____19591)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19614 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19614 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19680 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19680  in
          let uu____19681 =
            let uu____19690 =
              let uu____19695 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19695)  in
            (uu____19690, r1)  in
          FStar_Pervasives_Native.Some uu____19681
  
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
        let uu____19730 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19730 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19763,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19788 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19788  in
            let uu____19789 =
              let uu____19794 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19794, r1)  in
            FStar_Pervasives_Native.Some uu____19789
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19818 = try_lookup_lid env l  in
      match uu____19818 with
      | FStar_Pervasives_Native.None  ->
          let uu____19845 = name_not_found l  in
          let uu____19851 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19845 uu____19851
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19894  ->
              match uu___5_19894 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19898 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19919 = lookup_qname env lid  in
      match uu____19919 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19928,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19931;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19933;
              FStar_Syntax_Syntax.sigattrs = uu____19934;
              FStar_Syntax_Syntax.sigopts = uu____19935;_},FStar_Pervasives_Native.None
            ),uu____19936)
          ->
          let uu____19987 =
            let uu____19994 =
              let uu____19995 =
                let uu____19998 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19998 t  in
              (uvs, uu____19995)  in
            (uu____19994, q)  in
          FStar_Pervasives_Native.Some uu____19987
      | uu____20011 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20033 = lookup_qname env lid  in
      match uu____20033 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20038,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20041;
              FStar_Syntax_Syntax.sigquals = uu____20042;
              FStar_Syntax_Syntax.sigmeta = uu____20043;
              FStar_Syntax_Syntax.sigattrs = uu____20044;
              FStar_Syntax_Syntax.sigopts = uu____20045;_},FStar_Pervasives_Native.None
            ),uu____20046)
          ->
          let uu____20097 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20097 (uvs, t)
      | uu____20102 ->
          let uu____20103 = name_not_found lid  in
          let uu____20109 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20103 uu____20109
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20129 = lookup_qname env lid  in
      match uu____20129 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20134,uvs,t,uu____20137,uu____20138,uu____20139);
              FStar_Syntax_Syntax.sigrng = uu____20140;
              FStar_Syntax_Syntax.sigquals = uu____20141;
              FStar_Syntax_Syntax.sigmeta = uu____20142;
              FStar_Syntax_Syntax.sigattrs = uu____20143;
              FStar_Syntax_Syntax.sigopts = uu____20144;_},FStar_Pervasives_Native.None
            ),uu____20145)
          ->
          let uu____20202 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20202 (uvs, t)
      | uu____20207 ->
          let uu____20208 = name_not_found lid  in
          let uu____20214 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20208 uu____20214
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20237 = lookup_qname env lid  in
      match uu____20237 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20245,uu____20246,uu____20247,uu____20248,uu____20249,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20251;
              FStar_Syntax_Syntax.sigquals = uu____20252;
              FStar_Syntax_Syntax.sigmeta = uu____20253;
              FStar_Syntax_Syntax.sigattrs = uu____20254;
              FStar_Syntax_Syntax.sigopts = uu____20255;_},uu____20256),uu____20257)
          -> (true, dcs)
      | uu____20322 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20338 = lookup_qname env lid  in
      match uu____20338 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20339,uu____20340,uu____20341,l,uu____20343,uu____20344);
              FStar_Syntax_Syntax.sigrng = uu____20345;
              FStar_Syntax_Syntax.sigquals = uu____20346;
              FStar_Syntax_Syntax.sigmeta = uu____20347;
              FStar_Syntax_Syntax.sigattrs = uu____20348;
              FStar_Syntax_Syntax.sigopts = uu____20349;_},uu____20350),uu____20351)
          -> l
      | uu____20410 ->
          let uu____20411 =
            let uu____20413 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20413  in
          failwith uu____20411
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20483)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20540) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20564 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20564
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20599 -> FStar_Pervasives_Native.None)
          | uu____20608 -> FStar_Pervasives_Native.None
  
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
        let uu____20670 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20670
  
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
        let uu____20703 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20703
  
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
             (FStar_Util.Inl uu____20755,uu____20756) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20805),uu____20806) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20855 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20873 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20883 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20900 ->
                  let uu____20907 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20907
              | FStar_Syntax_Syntax.Sig_let ((uu____20908,lbs),uu____20910)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20926 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20926
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20933 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20949 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20959 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20960 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20967 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20968 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20969 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20982 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20983 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21011 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____21011
           (fun d_opt  ->
              let uu____21024 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____21024
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21034 =
                   let uu____21037 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21037  in
                 match uu____21034 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21038 =
                       let uu____21040 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21040
                        in
                     failwith uu____21038
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21045 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21045
                       then
                         let uu____21048 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21050 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21052 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21048 uu____21050 uu____21052
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
        (FStar_Util.Inr (se,uu____21077),uu____21078) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21127 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21149),uu____21150) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21199 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21221 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21221
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21254 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21254 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21276 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21285 =
                        let uu____21286 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21286.FStar_Syntax_Syntax.n  in
                      match uu____21285 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21291 -> false))
               in
            (true, uu____21276)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21314 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21314
  
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
          let uu____21386 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21386.FStar_Ident.str  in
        let uu____21387 = FStar_Util.smap_try_find tab s  in
        match uu____21387 with
        | FStar_Pervasives_Native.None  ->
            let uu____21390 = f ()  in
            (match uu____21390 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21428 =
        let uu____21429 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21429 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21463 =
        let uu____21464 = FStar_Syntax_Util.unrefine t  in
        uu____21464.FStar_Syntax_Syntax.n  in
      match uu____21463 with
      | FStar_Syntax_Syntax.Tm_type uu____21468 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21472) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21498) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21503,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21525 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21558 =
        let attrs =
          let uu____21564 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21564  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21604 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21604)
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
      let uu____21649 = lookup_qname env ftv  in
      match uu____21649 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21653) ->
          let uu____21698 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21698 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21719,t),r) ->
               let uu____21734 =
                 let uu____21735 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21735 t  in
               FStar_Pervasives_Native.Some uu____21734)
      | uu____21736 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21748 = try_lookup_effect_lid env ftv  in
      match uu____21748 with
      | FStar_Pervasives_Native.None  ->
          let uu____21751 = name_not_found ftv  in
          let uu____21757 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21751 uu____21757
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
        let uu____21781 = lookup_qname env lid0  in
        match uu____21781 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21792);
                FStar_Syntax_Syntax.sigrng = uu____21793;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21795;
                FStar_Syntax_Syntax.sigattrs = uu____21796;
                FStar_Syntax_Syntax.sigopts = uu____21797;_},FStar_Pervasives_Native.None
              ),uu____21798)
            ->
            let lid1 =
              let uu____21854 =
                let uu____21855 = FStar_Ident.range_of_lid lid  in
                let uu____21856 =
                  let uu____21857 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21857  in
                FStar_Range.set_use_range uu____21855 uu____21856  in
              FStar_Ident.set_lid_range lid uu____21854  in
            let uu____21858 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21864  ->
                      match uu___6_21864 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21867 -> false))
               in
            if uu____21858
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21886 =
                      let uu____21888 =
                        let uu____21890 = get_range env  in
                        FStar_Range.string_of_range uu____21890  in
                      let uu____21891 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21893 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21888 uu____21891 uu____21893
                       in
                    failwith uu____21886)
                  in
               match (binders, univs1) with
               | ([],uu____21914) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21940,uu____21941::uu____21942::uu____21943) ->
                   let uu____21964 =
                     let uu____21966 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21968 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21966 uu____21968
                      in
                   failwith uu____21964
               | uu____21979 ->
                   let uu____21994 =
                     let uu____21999 =
                       let uu____22000 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____22000)  in
                     inst_tscheme_with uu____21999 insts  in
                   (match uu____21994 with
                    | (uu____22013,t) ->
                        let t1 =
                          let uu____22016 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____22016 t  in
                        let uu____22017 =
                          let uu____22018 = FStar_Syntax_Subst.compress t1
                             in
                          uu____22018.FStar_Syntax_Syntax.n  in
                        (match uu____22017 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22053 -> failwith "Impossible")))
        | uu____22061 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22085 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22085 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22098,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22105 = find1 l2  in
            (match uu____22105 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22112 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22112 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22116 = find1 l  in
            (match uu____22116 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22121 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22121
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22142 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22142 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22148) ->
            FStar_List.length bs
        | uu____22187 ->
            let uu____22188 =
              let uu____22194 =
                let uu____22196 = FStar_Ident.string_of_lid name  in
                let uu____22198 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22196 uu____22198
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22194)
               in
            FStar_Errors.raise_error uu____22188 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22217 = lookup_qname env l1  in
      match uu____22217 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22220;
              FStar_Syntax_Syntax.sigrng = uu____22221;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22223;
              FStar_Syntax_Syntax.sigattrs = uu____22224;
              FStar_Syntax_Syntax.sigopts = uu____22225;_},uu____22226),uu____22227)
          -> q
      | uu____22280 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22304 =
          let uu____22305 =
            let uu____22307 = FStar_Util.string_of_int i  in
            let uu____22309 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22307 uu____22309
             in
          failwith uu____22305  in
        let uu____22312 = lookup_datacon env lid  in
        match uu____22312 with
        | (uu____22317,t) ->
            let uu____22319 =
              let uu____22320 = FStar_Syntax_Subst.compress t  in
              uu____22320.FStar_Syntax_Syntax.n  in
            (match uu____22319 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22324) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____22368 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____22368
                      FStar_Pervasives_Native.fst)
             | uu____22379 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22393 = lookup_qname env l  in
      match uu____22393 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22395,uu____22396,uu____22397);
              FStar_Syntax_Syntax.sigrng = uu____22398;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22400;
              FStar_Syntax_Syntax.sigattrs = uu____22401;
              FStar_Syntax_Syntax.sigopts = uu____22402;_},uu____22403),uu____22404)
          ->
          FStar_Util.for_some
            (fun uu___7_22459  ->
               match uu___7_22459 with
               | FStar_Syntax_Syntax.Projector uu____22461 -> true
               | uu____22467 -> false) quals
      | uu____22469 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22483 = lookup_qname env lid  in
      match uu____22483 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22485,uu____22486,uu____22487,uu____22488,uu____22489,uu____22490);
              FStar_Syntax_Syntax.sigrng = uu____22491;
              FStar_Syntax_Syntax.sigquals = uu____22492;
              FStar_Syntax_Syntax.sigmeta = uu____22493;
              FStar_Syntax_Syntax.sigattrs = uu____22494;
              FStar_Syntax_Syntax.sigopts = uu____22495;_},uu____22496),uu____22497)
          -> true
      | uu____22557 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22571 = lookup_qname env lid  in
      match uu____22571 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22573,uu____22574,uu____22575,uu____22576,uu____22577,uu____22578);
              FStar_Syntax_Syntax.sigrng = uu____22579;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22581;
              FStar_Syntax_Syntax.sigattrs = uu____22582;
              FStar_Syntax_Syntax.sigopts = uu____22583;_},uu____22584),uu____22585)
          ->
          FStar_Util.for_some
            (fun uu___8_22648  ->
               match uu___8_22648 with
               | FStar_Syntax_Syntax.RecordType uu____22650 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22660 -> true
               | uu____22670 -> false) quals
      | uu____22672 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22682,uu____22683);
            FStar_Syntax_Syntax.sigrng = uu____22684;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22686;
            FStar_Syntax_Syntax.sigattrs = uu____22687;
            FStar_Syntax_Syntax.sigopts = uu____22688;_},uu____22689),uu____22690)
        ->
        FStar_Util.for_some
          (fun uu___9_22749  ->
             match uu___9_22749 with
             | FStar_Syntax_Syntax.Action uu____22751 -> true
             | uu____22753 -> false) quals
    | uu____22755 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22769 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22769
  
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
      let uu____22786 =
        let uu____22787 = FStar_Syntax_Util.un_uinst head1  in
        uu____22787.FStar_Syntax_Syntax.n  in
      match uu____22786 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22793 ->
               true
           | uu____22796 -> false)
      | uu____22798 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22812 = lookup_qname env l  in
      match uu____22812 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22815),uu____22816) ->
          FStar_Util.for_some
            (fun uu___10_22864  ->
               match uu___10_22864 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22867 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22869 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22945 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22963) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22981 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22989 ->
                 FStar_Pervasives_Native.Some true
             | uu____23008 -> FStar_Pervasives_Native.Some false)
         in
      let uu____23011 =
        let uu____23015 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____23015 mapper  in
      match uu____23011 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23075 = lookup_qname env lid  in
      match uu____23075 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23079,uu____23080,tps,uu____23082,uu____23083,uu____23084);
              FStar_Syntax_Syntax.sigrng = uu____23085;
              FStar_Syntax_Syntax.sigquals = uu____23086;
              FStar_Syntax_Syntax.sigmeta = uu____23087;
              FStar_Syntax_Syntax.sigattrs = uu____23088;
              FStar_Syntax_Syntax.sigopts = uu____23089;_},uu____23090),uu____23091)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23159 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23205  ->
              match uu____23205 with
              | (d,uu____23214) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23230 = effect_decl_opt env l  in
      match uu____23230 with
      | FStar_Pervasives_Native.None  ->
          let uu____23245 = name_not_found l  in
          let uu____23251 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23245 uu____23251
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23279 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23279 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23286  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23300  ->
            fun uu____23301  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23335 = FStar_Ident.lid_equals l1 l2  in
        if uu____23335
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23354 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23354
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23373 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23426  ->
                        match uu____23426 with
                        | (m1,m2,uu____23440,uu____23441,uu____23442) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23373 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23467,uu____23468,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23516 = join_opt env l1 l2  in
        match uu____23516 with
        | FStar_Pervasives_Native.None  ->
            let uu____23537 =
              let uu____23543 =
                let uu____23545 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23547 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23545 uu____23547
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23543)  in
            FStar_Errors.raise_error uu____23537 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23590 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23590
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
  'Auu____23610 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23610) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23639 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23665  ->
                match uu____23665 with
                | (d,uu____23672) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23639 with
      | FStar_Pervasives_Native.None  ->
          let uu____23683 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23683
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23698 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23698 with
           | (uu____23709,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23727)::(wp,uu____23729)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23785 -> failwith "Impossible"))
  
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
        | uu____23850 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23863 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23863 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23880 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23880 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23905 =
                     let uu____23911 =
                       let uu____23913 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23921 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23932 =
                         let uu____23934 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23934  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23913 uu____23921 uu____23932
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23911)
                      in
                   FStar_Errors.raise_error uu____23905
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23942 =
                     let uu____23953 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23953 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23990  ->
                        fun uu____23991  ->
                          match (uu____23990, uu____23991) with
                          | ((x,uu____24021),(t,uu____24023)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23942
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____24054 =
                     let uu___1614_24055 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1614_24055.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1614_24055.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1614_24055.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1614_24055.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24054
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24067 .
    'Auu____24067 ->
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
            let uu____24108 =
              let uu____24115 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24115)  in
            match uu____24108 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24139 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24141 = FStar_Util.string_of_int given  in
                     let uu____24143 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24139 uu____24141 uu____24143
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24148 = effect_decl_opt env effect_name  in
          match uu____24148 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24170) ->
              let uu____24181 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24181 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24199 =
                       let uu____24202 = get_range env  in
                       let uu____24203 =
                         let uu____24210 =
                           let uu____24211 =
                             let uu____24228 =
                               let uu____24239 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24239 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24228)  in
                           FStar_Syntax_Syntax.Tm_app uu____24211  in
                         FStar_Syntax_Syntax.mk uu____24210  in
                       uu____24203 FStar_Pervasives_Native.None uu____24202
                        in
                     FStar_Pervasives_Native.Some uu____24199)))
  
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
           (fun uu___11_24339  ->
              match uu___11_24339 with
              | FStar_Syntax_Syntax.Reflectable uu____24341 -> true
              | uu____24343 -> false))
  
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
      | uu____24403 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24418 =
        let uu____24419 = FStar_Syntax_Subst.compress t  in
        uu____24419.FStar_Syntax_Syntax.n  in
      match uu____24418 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24423,c) ->
          is_reifiable_comp env c
      | uu____24445 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24465 =
           let uu____24467 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24467  in
         if uu____24465
         then
           let uu____24470 =
             let uu____24476 =
               let uu____24478 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24478
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24476)  in
           let uu____24482 = get_range env  in
           FStar_Errors.raise_error uu____24470 uu____24482
         else ());
        (let uu____24485 = effect_repr_aux true env c u_c  in
         match uu____24485 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb =
        let uu____24518 = FStar_Syntax_Util.lids_of_sigelt s  in
        (uu____24518, s)  in
      let env1 =
        let uu___1691_24524 = env  in
        {
          solver = (uu___1691_24524.solver);
          range = (uu___1691_24524.range);
          curmodule = (uu___1691_24524.curmodule);
          gamma = (uu___1691_24524.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1691_24524.gamma_cache);
          modules = (uu___1691_24524.modules);
          expected_typ = (uu___1691_24524.expected_typ);
          sigtab = (uu___1691_24524.sigtab);
          attrtab = (uu___1691_24524.attrtab);
          instantiate_imp = (uu___1691_24524.instantiate_imp);
          effects = (uu___1691_24524.effects);
          generalize = (uu___1691_24524.generalize);
          letrecs = (uu___1691_24524.letrecs);
          top_level = (uu___1691_24524.top_level);
          check_uvars = (uu___1691_24524.check_uvars);
          use_eq = (uu___1691_24524.use_eq);
          use_eq_strict = (uu___1691_24524.use_eq_strict);
          is_iface = (uu___1691_24524.is_iface);
          admit = (uu___1691_24524.admit);
          lax = (uu___1691_24524.lax);
          lax_universes = (uu___1691_24524.lax_universes);
          phase1 = (uu___1691_24524.phase1);
          failhard = (uu___1691_24524.failhard);
          nosynth = (uu___1691_24524.nosynth);
          uvar_subtyping = (uu___1691_24524.uvar_subtyping);
          tc_term = (uu___1691_24524.tc_term);
          type_of = (uu___1691_24524.type_of);
          universe_of = (uu___1691_24524.universe_of);
          check_type_of = (uu___1691_24524.check_type_of);
          use_bv_sorts = (uu___1691_24524.use_bv_sorts);
          qtbl_name_and_index = (uu___1691_24524.qtbl_name_and_index);
          normalized_eff_names = (uu___1691_24524.normalized_eff_names);
          fv_delta_depths = (uu___1691_24524.fv_delta_depths);
          proof_ns = (uu___1691_24524.proof_ns);
          synth_hook = (uu___1691_24524.synth_hook);
          try_solve_implicits_hook =
            (uu___1691_24524.try_solve_implicits_hook);
          splice = (uu___1691_24524.splice);
          mpreprocess = (uu___1691_24524.mpreprocess);
          postprocess = (uu___1691_24524.postprocess);
          is_native_tactic = (uu___1691_24524.is_native_tactic);
          identifier_info = (uu___1691_24524.identifier_info);
          tc_hooks = (uu___1691_24524.tc_hooks);
          dsenv = (uu___1691_24524.dsenv);
          nbe = (uu___1691_24524.nbe);
          strict_args_tab = (uu___1691_24524.strict_args_tab);
          erasable_types_tab = (uu___1691_24524.erasable_types_tab)
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
    fun uu____24543  ->
      match uu____24543 with
      | (ed,quals) ->
          let effects =
            let uu___1700_24557 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1700_24557.order);
              joins = (uu___1700_24557.joins);
              polymonadic_binds = (uu___1700_24557.polymonadic_binds)
            }  in
          let uu___1703_24566 = env  in
          {
            solver = (uu___1703_24566.solver);
            range = (uu___1703_24566.range);
            curmodule = (uu___1703_24566.curmodule);
            gamma = (uu___1703_24566.gamma);
            gamma_sig = (uu___1703_24566.gamma_sig);
            gamma_cache = (uu___1703_24566.gamma_cache);
            modules = (uu___1703_24566.modules);
            expected_typ = (uu___1703_24566.expected_typ);
            sigtab = (uu___1703_24566.sigtab);
            attrtab = (uu___1703_24566.attrtab);
            instantiate_imp = (uu___1703_24566.instantiate_imp);
            effects;
            generalize = (uu___1703_24566.generalize);
            letrecs = (uu___1703_24566.letrecs);
            top_level = (uu___1703_24566.top_level);
            check_uvars = (uu___1703_24566.check_uvars);
            use_eq = (uu___1703_24566.use_eq);
            use_eq_strict = (uu___1703_24566.use_eq_strict);
            is_iface = (uu___1703_24566.is_iface);
            admit = (uu___1703_24566.admit);
            lax = (uu___1703_24566.lax);
            lax_universes = (uu___1703_24566.lax_universes);
            phase1 = (uu___1703_24566.phase1);
            failhard = (uu___1703_24566.failhard);
            nosynth = (uu___1703_24566.nosynth);
            uvar_subtyping = (uu___1703_24566.uvar_subtyping);
            tc_term = (uu___1703_24566.tc_term);
            type_of = (uu___1703_24566.type_of);
            universe_of = (uu___1703_24566.universe_of);
            check_type_of = (uu___1703_24566.check_type_of);
            use_bv_sorts = (uu___1703_24566.use_bv_sorts);
            qtbl_name_and_index = (uu___1703_24566.qtbl_name_and_index);
            normalized_eff_names = (uu___1703_24566.normalized_eff_names);
            fv_delta_depths = (uu___1703_24566.fv_delta_depths);
            proof_ns = (uu___1703_24566.proof_ns);
            synth_hook = (uu___1703_24566.synth_hook);
            try_solve_implicits_hook =
              (uu___1703_24566.try_solve_implicits_hook);
            splice = (uu___1703_24566.splice);
            mpreprocess = (uu___1703_24566.mpreprocess);
            postprocess = (uu___1703_24566.postprocess);
            is_native_tactic = (uu___1703_24566.is_native_tactic);
            identifier_info = (uu___1703_24566.identifier_info);
            tc_hooks = (uu___1703_24566.tc_hooks);
            dsenv = (uu___1703_24566.dsenv);
            nbe = (uu___1703_24566.nbe);
            strict_args_tab = (uu___1703_24566.strict_args_tab);
            erasable_types_tab = (uu___1703_24566.erasable_types_tab)
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
        let uu____24595 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24663  ->
                  match uu____24663 with
                  | (m1,n11,uu____24681,uu____24682) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24595 with
        | FStar_Pervasives_Native.Some (uu____24707,uu____24708,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24753 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24828 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24828
                  (fun uu____24849  ->
                     match uu____24849 with
                     | (c1,g1) ->
                         let uu____24860 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24860
                           (fun uu____24881  ->
                              match uu____24881 with
                              | (c2,g2) ->
                                  let uu____24892 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24892)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____25014 = l1 u t e  in
                              l2 u t uu____25014))
                | uu____25015 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25083  ->
                    match uu____25083 with
                    | (e,uu____25091) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25114 =
            match uu____25114 with
            | (i,j) ->
                let uu____25125 = FStar_Ident.lid_equals i j  in
                if uu____25125
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25132  -> FStar_Pervasives_Native.Some _25132)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25161 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25171 = FStar_Ident.lid_equals i k  in
                        if uu____25171
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25185 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25185
                                  then []
                                  else
                                    (let uu____25192 =
                                       let uu____25201 =
                                         find_edge order1 (i, k)  in
                                       let uu____25204 =
                                         find_edge order1 (k, j)  in
                                       (uu____25201, uu____25204)  in
                                     match uu____25192 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25219 =
                                           compose_edges e1 e2  in
                                         [uu____25219]
                                     | uu____25220 -> [])))))
                 in
              FStar_List.append order1 uu____25161  in
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
                  let uu____25250 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25253 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25253
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25250
                  then
                    let uu____25260 =
                      let uu____25266 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25266)
                       in
                    let uu____25270 = get_range env  in
                    FStar_Errors.raise_error uu____25260 uu____25270
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25348 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25348
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25400 =
                                             let uu____25409 =
                                               find_edge order2 (i, k)  in
                                             let uu____25412 =
                                               find_edge order2 (j, k)  in
                                             (uu____25409, uu____25412)  in
                                           match uu____25400 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25454,uu____25455)
                                                    ->
                                                    let uu____25462 =
                                                      let uu____25469 =
                                                        let uu____25471 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25471
                                                         in
                                                      let uu____25474 =
                                                        let uu____25476 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25476
                                                         in
                                                      (uu____25469,
                                                        uu____25474)
                                                       in
                                                    (match uu____25462 with
                                                     | (true ,true ) ->
                                                         let uu____25493 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25493
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
                                           | uu____25536 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25588 =
                                   let uu____25590 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25590
                                     FStar_Util.is_some
                                    in
                                 if uu____25588
                                 then
                                   let uu____25639 =
                                     let uu____25645 =
                                       let uu____25647 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25649 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25651 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25653 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25647 uu____25649 uu____25651
                                         uu____25653
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25645)
                                      in
                                   FStar_Errors.raise_error uu____25639
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1824_25692 = env.effects  in
             {
               decls = (uu___1824_25692.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1824_25692.polymonadic_binds)
             }  in
           let uu___1827_25693 = env  in
           {
             solver = (uu___1827_25693.solver);
             range = (uu___1827_25693.range);
             curmodule = (uu___1827_25693.curmodule);
             gamma = (uu___1827_25693.gamma);
             gamma_sig = (uu___1827_25693.gamma_sig);
             gamma_cache = (uu___1827_25693.gamma_cache);
             modules = (uu___1827_25693.modules);
             expected_typ = (uu___1827_25693.expected_typ);
             sigtab = (uu___1827_25693.sigtab);
             attrtab = (uu___1827_25693.attrtab);
             instantiate_imp = (uu___1827_25693.instantiate_imp);
             effects;
             generalize = (uu___1827_25693.generalize);
             letrecs = (uu___1827_25693.letrecs);
             top_level = (uu___1827_25693.top_level);
             check_uvars = (uu___1827_25693.check_uvars);
             use_eq = (uu___1827_25693.use_eq);
             use_eq_strict = (uu___1827_25693.use_eq_strict);
             is_iface = (uu___1827_25693.is_iface);
             admit = (uu___1827_25693.admit);
             lax = (uu___1827_25693.lax);
             lax_universes = (uu___1827_25693.lax_universes);
             phase1 = (uu___1827_25693.phase1);
             failhard = (uu___1827_25693.failhard);
             nosynth = (uu___1827_25693.nosynth);
             uvar_subtyping = (uu___1827_25693.uvar_subtyping);
             tc_term = (uu___1827_25693.tc_term);
             type_of = (uu___1827_25693.type_of);
             universe_of = (uu___1827_25693.universe_of);
             check_type_of = (uu___1827_25693.check_type_of);
             use_bv_sorts = (uu___1827_25693.use_bv_sorts);
             qtbl_name_and_index = (uu___1827_25693.qtbl_name_and_index);
             normalized_eff_names = (uu___1827_25693.normalized_eff_names);
             fv_delta_depths = (uu___1827_25693.fv_delta_depths);
             proof_ns = (uu___1827_25693.proof_ns);
             synth_hook = (uu___1827_25693.synth_hook);
             try_solve_implicits_hook =
               (uu___1827_25693.try_solve_implicits_hook);
             splice = (uu___1827_25693.splice);
             mpreprocess = (uu___1827_25693.mpreprocess);
             postprocess = (uu___1827_25693.postprocess);
             is_native_tactic = (uu___1827_25693.is_native_tactic);
             identifier_info = (uu___1827_25693.identifier_info);
             tc_hooks = (uu___1827_25693.tc_hooks);
             dsenv = (uu___1827_25693.dsenv);
             nbe = (uu___1827_25693.nbe);
             strict_args_tab = (uu___1827_25693.strict_args_tab);
             erasable_types_tab = (uu___1827_25693.erasable_types_tab)
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
              let uu____25741 = FStar_Ident.string_of_lid m  in
              let uu____25743 = FStar_Ident.string_of_lid n1  in
              let uu____25745 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25741 uu____25743 uu____25745
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25754 =
              let uu____25756 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25756 FStar_Util.is_some  in
            if uu____25754
            then
              let uu____25793 =
                let uu____25799 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25799)
                 in
              FStar_Errors.raise_error uu____25793 env.range
            else
              (let uu____25805 =
                 let uu____25807 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25807 FStar_Util.is_some  in
               if uu____25805
               then
                 let uu____25832 =
                   let uu____25838 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25838)
                    in
                 FStar_Errors.raise_error uu____25832 env.range
               else
                 (let uu___1842_25844 = env  in
                  {
                    solver = (uu___1842_25844.solver);
                    range = (uu___1842_25844.range);
                    curmodule = (uu___1842_25844.curmodule);
                    gamma = (uu___1842_25844.gamma);
                    gamma_sig = (uu___1842_25844.gamma_sig);
                    gamma_cache = (uu___1842_25844.gamma_cache);
                    modules = (uu___1842_25844.modules);
                    expected_typ = (uu___1842_25844.expected_typ);
                    sigtab = (uu___1842_25844.sigtab);
                    attrtab = (uu___1842_25844.attrtab);
                    instantiate_imp = (uu___1842_25844.instantiate_imp);
                    effects =
                      (let uu___1844_25846 = env.effects  in
                       {
                         decls = (uu___1844_25846.decls);
                         order = (uu___1844_25846.order);
                         joins = (uu___1844_25846.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1842_25844.generalize);
                    letrecs = (uu___1842_25844.letrecs);
                    top_level = (uu___1842_25844.top_level);
                    check_uvars = (uu___1842_25844.check_uvars);
                    use_eq = (uu___1842_25844.use_eq);
                    use_eq_strict = (uu___1842_25844.use_eq_strict);
                    is_iface = (uu___1842_25844.is_iface);
                    admit = (uu___1842_25844.admit);
                    lax = (uu___1842_25844.lax);
                    lax_universes = (uu___1842_25844.lax_universes);
                    phase1 = (uu___1842_25844.phase1);
                    failhard = (uu___1842_25844.failhard);
                    nosynth = (uu___1842_25844.nosynth);
                    uvar_subtyping = (uu___1842_25844.uvar_subtyping);
                    tc_term = (uu___1842_25844.tc_term);
                    type_of = (uu___1842_25844.type_of);
                    universe_of = (uu___1842_25844.universe_of);
                    check_type_of = (uu___1842_25844.check_type_of);
                    use_bv_sorts = (uu___1842_25844.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1842_25844.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1842_25844.normalized_eff_names);
                    fv_delta_depths = (uu___1842_25844.fv_delta_depths);
                    proof_ns = (uu___1842_25844.proof_ns);
                    synth_hook = (uu___1842_25844.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1842_25844.try_solve_implicits_hook);
                    splice = (uu___1842_25844.splice);
                    mpreprocess = (uu___1842_25844.mpreprocess);
                    postprocess = (uu___1842_25844.postprocess);
                    is_native_tactic = (uu___1842_25844.is_native_tactic);
                    identifier_info = (uu___1842_25844.identifier_info);
                    tc_hooks = (uu___1842_25844.tc_hooks);
                    dsenv = (uu___1842_25844.dsenv);
                    nbe = (uu___1842_25844.nbe);
                    strict_args_tab = (uu___1842_25844.strict_args_tab);
                    erasable_types_tab = (uu___1842_25844.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1848_25918 = env  in
      {
        solver = (uu___1848_25918.solver);
        range = (uu___1848_25918.range);
        curmodule = (uu___1848_25918.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1848_25918.gamma_sig);
        gamma_cache = (uu___1848_25918.gamma_cache);
        modules = (uu___1848_25918.modules);
        expected_typ = (uu___1848_25918.expected_typ);
        sigtab = (uu___1848_25918.sigtab);
        attrtab = (uu___1848_25918.attrtab);
        instantiate_imp = (uu___1848_25918.instantiate_imp);
        effects = (uu___1848_25918.effects);
        generalize = (uu___1848_25918.generalize);
        letrecs = (uu___1848_25918.letrecs);
        top_level = (uu___1848_25918.top_level);
        check_uvars = (uu___1848_25918.check_uvars);
        use_eq = (uu___1848_25918.use_eq);
        use_eq_strict = (uu___1848_25918.use_eq_strict);
        is_iface = (uu___1848_25918.is_iface);
        admit = (uu___1848_25918.admit);
        lax = (uu___1848_25918.lax);
        lax_universes = (uu___1848_25918.lax_universes);
        phase1 = (uu___1848_25918.phase1);
        failhard = (uu___1848_25918.failhard);
        nosynth = (uu___1848_25918.nosynth);
        uvar_subtyping = (uu___1848_25918.uvar_subtyping);
        tc_term = (uu___1848_25918.tc_term);
        type_of = (uu___1848_25918.type_of);
        universe_of = (uu___1848_25918.universe_of);
        check_type_of = (uu___1848_25918.check_type_of);
        use_bv_sorts = (uu___1848_25918.use_bv_sorts);
        qtbl_name_and_index = (uu___1848_25918.qtbl_name_and_index);
        normalized_eff_names = (uu___1848_25918.normalized_eff_names);
        fv_delta_depths = (uu___1848_25918.fv_delta_depths);
        proof_ns = (uu___1848_25918.proof_ns);
        synth_hook = (uu___1848_25918.synth_hook);
        try_solve_implicits_hook = (uu___1848_25918.try_solve_implicits_hook);
        splice = (uu___1848_25918.splice);
        mpreprocess = (uu___1848_25918.mpreprocess);
        postprocess = (uu___1848_25918.postprocess);
        is_native_tactic = (uu___1848_25918.is_native_tactic);
        identifier_info = (uu___1848_25918.identifier_info);
        tc_hooks = (uu___1848_25918.tc_hooks);
        dsenv = (uu___1848_25918.dsenv);
        nbe = (uu___1848_25918.nbe);
        strict_args_tab = (uu___1848_25918.strict_args_tab);
        erasable_types_tab = (uu___1848_25918.erasable_types_tab)
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
            (let uu___1861_25976 = env  in
             {
               solver = (uu___1861_25976.solver);
               range = (uu___1861_25976.range);
               curmodule = (uu___1861_25976.curmodule);
               gamma = rest;
               gamma_sig = (uu___1861_25976.gamma_sig);
               gamma_cache = (uu___1861_25976.gamma_cache);
               modules = (uu___1861_25976.modules);
               expected_typ = (uu___1861_25976.expected_typ);
               sigtab = (uu___1861_25976.sigtab);
               attrtab = (uu___1861_25976.attrtab);
               instantiate_imp = (uu___1861_25976.instantiate_imp);
               effects = (uu___1861_25976.effects);
               generalize = (uu___1861_25976.generalize);
               letrecs = (uu___1861_25976.letrecs);
               top_level = (uu___1861_25976.top_level);
               check_uvars = (uu___1861_25976.check_uvars);
               use_eq = (uu___1861_25976.use_eq);
               use_eq_strict = (uu___1861_25976.use_eq_strict);
               is_iface = (uu___1861_25976.is_iface);
               admit = (uu___1861_25976.admit);
               lax = (uu___1861_25976.lax);
               lax_universes = (uu___1861_25976.lax_universes);
               phase1 = (uu___1861_25976.phase1);
               failhard = (uu___1861_25976.failhard);
               nosynth = (uu___1861_25976.nosynth);
               uvar_subtyping = (uu___1861_25976.uvar_subtyping);
               tc_term = (uu___1861_25976.tc_term);
               type_of = (uu___1861_25976.type_of);
               universe_of = (uu___1861_25976.universe_of);
               check_type_of = (uu___1861_25976.check_type_of);
               use_bv_sorts = (uu___1861_25976.use_bv_sorts);
               qtbl_name_and_index = (uu___1861_25976.qtbl_name_and_index);
               normalized_eff_names = (uu___1861_25976.normalized_eff_names);
               fv_delta_depths = (uu___1861_25976.fv_delta_depths);
               proof_ns = (uu___1861_25976.proof_ns);
               synth_hook = (uu___1861_25976.synth_hook);
               try_solve_implicits_hook =
                 (uu___1861_25976.try_solve_implicits_hook);
               splice = (uu___1861_25976.splice);
               mpreprocess = (uu___1861_25976.mpreprocess);
               postprocess = (uu___1861_25976.postprocess);
               is_native_tactic = (uu___1861_25976.is_native_tactic);
               identifier_info = (uu___1861_25976.identifier_info);
               tc_hooks = (uu___1861_25976.tc_hooks);
               dsenv = (uu___1861_25976.dsenv);
               nbe = (uu___1861_25976.nbe);
               strict_args_tab = (uu___1861_25976.strict_args_tab);
               erasable_types_tab = (uu___1861_25976.erasable_types_tab)
             }))
    | uu____25977 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____26006  ->
             match uu____26006 with | (x,uu____26014) -> push_bv env1 x) env
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
            let uu___1875_26049 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1875_26049.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1875_26049.FStar_Syntax_Syntax.index);
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
        let uu____26122 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26122 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26150 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26150)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1896_26166 = env  in
      {
        solver = (uu___1896_26166.solver);
        range = (uu___1896_26166.range);
        curmodule = (uu___1896_26166.curmodule);
        gamma = (uu___1896_26166.gamma);
        gamma_sig = (uu___1896_26166.gamma_sig);
        gamma_cache = (uu___1896_26166.gamma_cache);
        modules = (uu___1896_26166.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1896_26166.sigtab);
        attrtab = (uu___1896_26166.attrtab);
        instantiate_imp = (uu___1896_26166.instantiate_imp);
        effects = (uu___1896_26166.effects);
        generalize = (uu___1896_26166.generalize);
        letrecs = (uu___1896_26166.letrecs);
        top_level = (uu___1896_26166.top_level);
        check_uvars = (uu___1896_26166.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1896_26166.use_eq_strict);
        is_iface = (uu___1896_26166.is_iface);
        admit = (uu___1896_26166.admit);
        lax = (uu___1896_26166.lax);
        lax_universes = (uu___1896_26166.lax_universes);
        phase1 = (uu___1896_26166.phase1);
        failhard = (uu___1896_26166.failhard);
        nosynth = (uu___1896_26166.nosynth);
        uvar_subtyping = (uu___1896_26166.uvar_subtyping);
        tc_term = (uu___1896_26166.tc_term);
        type_of = (uu___1896_26166.type_of);
        universe_of = (uu___1896_26166.universe_of);
        check_type_of = (uu___1896_26166.check_type_of);
        use_bv_sorts = (uu___1896_26166.use_bv_sorts);
        qtbl_name_and_index = (uu___1896_26166.qtbl_name_and_index);
        normalized_eff_names = (uu___1896_26166.normalized_eff_names);
        fv_delta_depths = (uu___1896_26166.fv_delta_depths);
        proof_ns = (uu___1896_26166.proof_ns);
        synth_hook = (uu___1896_26166.synth_hook);
        try_solve_implicits_hook = (uu___1896_26166.try_solve_implicits_hook);
        splice = (uu___1896_26166.splice);
        mpreprocess = (uu___1896_26166.mpreprocess);
        postprocess = (uu___1896_26166.postprocess);
        is_native_tactic = (uu___1896_26166.is_native_tactic);
        identifier_info = (uu___1896_26166.identifier_info);
        tc_hooks = (uu___1896_26166.tc_hooks);
        dsenv = (uu___1896_26166.dsenv);
        nbe = (uu___1896_26166.nbe);
        strict_args_tab = (uu___1896_26166.strict_args_tab);
        erasable_types_tab = (uu___1896_26166.erasable_types_tab)
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
    let uu____26197 = expected_typ env_  in
    ((let uu___1903_26203 = env_  in
      {
        solver = (uu___1903_26203.solver);
        range = (uu___1903_26203.range);
        curmodule = (uu___1903_26203.curmodule);
        gamma = (uu___1903_26203.gamma);
        gamma_sig = (uu___1903_26203.gamma_sig);
        gamma_cache = (uu___1903_26203.gamma_cache);
        modules = (uu___1903_26203.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1903_26203.sigtab);
        attrtab = (uu___1903_26203.attrtab);
        instantiate_imp = (uu___1903_26203.instantiate_imp);
        effects = (uu___1903_26203.effects);
        generalize = (uu___1903_26203.generalize);
        letrecs = (uu___1903_26203.letrecs);
        top_level = (uu___1903_26203.top_level);
        check_uvars = (uu___1903_26203.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1903_26203.use_eq_strict);
        is_iface = (uu___1903_26203.is_iface);
        admit = (uu___1903_26203.admit);
        lax = (uu___1903_26203.lax);
        lax_universes = (uu___1903_26203.lax_universes);
        phase1 = (uu___1903_26203.phase1);
        failhard = (uu___1903_26203.failhard);
        nosynth = (uu___1903_26203.nosynth);
        uvar_subtyping = (uu___1903_26203.uvar_subtyping);
        tc_term = (uu___1903_26203.tc_term);
        type_of = (uu___1903_26203.type_of);
        universe_of = (uu___1903_26203.universe_of);
        check_type_of = (uu___1903_26203.check_type_of);
        use_bv_sorts = (uu___1903_26203.use_bv_sorts);
        qtbl_name_and_index = (uu___1903_26203.qtbl_name_and_index);
        normalized_eff_names = (uu___1903_26203.normalized_eff_names);
        fv_delta_depths = (uu___1903_26203.fv_delta_depths);
        proof_ns = (uu___1903_26203.proof_ns);
        synth_hook = (uu___1903_26203.synth_hook);
        try_solve_implicits_hook = (uu___1903_26203.try_solve_implicits_hook);
        splice = (uu___1903_26203.splice);
        mpreprocess = (uu___1903_26203.mpreprocess);
        postprocess = (uu___1903_26203.postprocess);
        is_native_tactic = (uu___1903_26203.is_native_tactic);
        identifier_info = (uu___1903_26203.identifier_info);
        tc_hooks = (uu___1903_26203.tc_hooks);
        dsenv = (uu___1903_26203.dsenv);
        nbe = (uu___1903_26203.nbe);
        strict_args_tab = (uu___1903_26203.strict_args_tab);
        erasable_types_tab = (uu___1903_26203.erasable_types_tab)
      }), uu____26197)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26215 =
      let uu____26218 = FStar_Ident.id_of_text ""  in [uu____26218]  in
    FStar_Ident.lid_of_ids uu____26215  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26225 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26225
        then
          let uu____26230 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26230 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1911_26258 = env  in
       {
         solver = (uu___1911_26258.solver);
         range = (uu___1911_26258.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1911_26258.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1911_26258.expected_typ);
         sigtab = (uu___1911_26258.sigtab);
         attrtab = (uu___1911_26258.attrtab);
         instantiate_imp = (uu___1911_26258.instantiate_imp);
         effects = (uu___1911_26258.effects);
         generalize = (uu___1911_26258.generalize);
         letrecs = (uu___1911_26258.letrecs);
         top_level = (uu___1911_26258.top_level);
         check_uvars = (uu___1911_26258.check_uvars);
         use_eq = (uu___1911_26258.use_eq);
         use_eq_strict = (uu___1911_26258.use_eq_strict);
         is_iface = (uu___1911_26258.is_iface);
         admit = (uu___1911_26258.admit);
         lax = (uu___1911_26258.lax);
         lax_universes = (uu___1911_26258.lax_universes);
         phase1 = (uu___1911_26258.phase1);
         failhard = (uu___1911_26258.failhard);
         nosynth = (uu___1911_26258.nosynth);
         uvar_subtyping = (uu___1911_26258.uvar_subtyping);
         tc_term = (uu___1911_26258.tc_term);
         type_of = (uu___1911_26258.type_of);
         universe_of = (uu___1911_26258.universe_of);
         check_type_of = (uu___1911_26258.check_type_of);
         use_bv_sorts = (uu___1911_26258.use_bv_sorts);
         qtbl_name_and_index = (uu___1911_26258.qtbl_name_and_index);
         normalized_eff_names = (uu___1911_26258.normalized_eff_names);
         fv_delta_depths = (uu___1911_26258.fv_delta_depths);
         proof_ns = (uu___1911_26258.proof_ns);
         synth_hook = (uu___1911_26258.synth_hook);
         try_solve_implicits_hook =
           (uu___1911_26258.try_solve_implicits_hook);
         splice = (uu___1911_26258.splice);
         mpreprocess = (uu___1911_26258.mpreprocess);
         postprocess = (uu___1911_26258.postprocess);
         is_native_tactic = (uu___1911_26258.is_native_tactic);
         identifier_info = (uu___1911_26258.identifier_info);
         tc_hooks = (uu___1911_26258.tc_hooks);
         dsenv = (uu___1911_26258.dsenv);
         nbe = (uu___1911_26258.nbe);
         strict_args_tab = (uu___1911_26258.strict_args_tab);
         erasable_types_tab = (uu___1911_26258.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26310)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26314,(uu____26315,t)))::tl1
          ->
          let uu____26336 =
            let uu____26339 = FStar_Syntax_Free.uvars t  in
            ext out uu____26339  in
          aux uu____26336 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26342;
            FStar_Syntax_Syntax.index = uu____26343;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26351 =
            let uu____26354 = FStar_Syntax_Free.uvars t  in
            ext out uu____26354  in
          aux uu____26351 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26412)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26416,(uu____26417,t)))::tl1
          ->
          let uu____26438 =
            let uu____26441 = FStar_Syntax_Free.univs t  in
            ext out uu____26441  in
          aux uu____26438 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26444;
            FStar_Syntax_Syntax.index = uu____26445;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26453 =
            let uu____26456 = FStar_Syntax_Free.univs t  in
            ext out uu____26456  in
          aux uu____26453 tl1
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
          let uu____26518 = FStar_Util.set_add uname out  in
          aux uu____26518 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26521,(uu____26522,t)))::tl1
          ->
          let uu____26543 =
            let uu____26546 = FStar_Syntax_Free.univnames t  in
            ext out uu____26546  in
          aux uu____26543 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26549;
            FStar_Syntax_Syntax.index = uu____26550;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26558 =
            let uu____26561 = FStar_Syntax_Free.univnames t  in
            ext out uu____26561  in
          aux uu____26558 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26582  ->
            match uu___12_26582 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26586 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26599 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26610 =
      let uu____26619 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26619
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26610 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26667 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26680  ->
              match uu___13_26680 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26683 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26683
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26689) ->
                  let uu____26706 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26706))
       in
    FStar_All.pipe_right uu____26667 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26720  ->
    match uu___14_26720 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26726 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26726
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26750  ->
         fun v1  ->
           fun keys1  ->
             let uu____26756 = FStar_Syntax_Util.lids_of_sigelt v1  in
             FStar_List.append uu____26756 keys1) keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26808) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26841,uu____26842) -> false  in
      let uu____26856 =
        FStar_List.tryFind
          (fun uu____26878  ->
             match uu____26878 with | (p,uu____26889) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26856 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26908,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26938 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26938
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2054_26960 = e  in
        {
          solver = (uu___2054_26960.solver);
          range = (uu___2054_26960.range);
          curmodule = (uu___2054_26960.curmodule);
          gamma = (uu___2054_26960.gamma);
          gamma_sig = (uu___2054_26960.gamma_sig);
          gamma_cache = (uu___2054_26960.gamma_cache);
          modules = (uu___2054_26960.modules);
          expected_typ = (uu___2054_26960.expected_typ);
          sigtab = (uu___2054_26960.sigtab);
          attrtab = (uu___2054_26960.attrtab);
          instantiate_imp = (uu___2054_26960.instantiate_imp);
          effects = (uu___2054_26960.effects);
          generalize = (uu___2054_26960.generalize);
          letrecs = (uu___2054_26960.letrecs);
          top_level = (uu___2054_26960.top_level);
          check_uvars = (uu___2054_26960.check_uvars);
          use_eq = (uu___2054_26960.use_eq);
          use_eq_strict = (uu___2054_26960.use_eq_strict);
          is_iface = (uu___2054_26960.is_iface);
          admit = (uu___2054_26960.admit);
          lax = (uu___2054_26960.lax);
          lax_universes = (uu___2054_26960.lax_universes);
          phase1 = (uu___2054_26960.phase1);
          failhard = (uu___2054_26960.failhard);
          nosynth = (uu___2054_26960.nosynth);
          uvar_subtyping = (uu___2054_26960.uvar_subtyping);
          tc_term = (uu___2054_26960.tc_term);
          type_of = (uu___2054_26960.type_of);
          universe_of = (uu___2054_26960.universe_of);
          check_type_of = (uu___2054_26960.check_type_of);
          use_bv_sorts = (uu___2054_26960.use_bv_sorts);
          qtbl_name_and_index = (uu___2054_26960.qtbl_name_and_index);
          normalized_eff_names = (uu___2054_26960.normalized_eff_names);
          fv_delta_depths = (uu___2054_26960.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2054_26960.synth_hook);
          try_solve_implicits_hook =
            (uu___2054_26960.try_solve_implicits_hook);
          splice = (uu___2054_26960.splice);
          mpreprocess = (uu___2054_26960.mpreprocess);
          postprocess = (uu___2054_26960.postprocess);
          is_native_tactic = (uu___2054_26960.is_native_tactic);
          identifier_info = (uu___2054_26960.identifier_info);
          tc_hooks = (uu___2054_26960.tc_hooks);
          dsenv = (uu___2054_26960.dsenv);
          nbe = (uu___2054_26960.nbe);
          strict_args_tab = (uu___2054_26960.strict_args_tab);
          erasable_types_tab = (uu___2054_26960.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2063_27008 = e  in
      {
        solver = (uu___2063_27008.solver);
        range = (uu___2063_27008.range);
        curmodule = (uu___2063_27008.curmodule);
        gamma = (uu___2063_27008.gamma);
        gamma_sig = (uu___2063_27008.gamma_sig);
        gamma_cache = (uu___2063_27008.gamma_cache);
        modules = (uu___2063_27008.modules);
        expected_typ = (uu___2063_27008.expected_typ);
        sigtab = (uu___2063_27008.sigtab);
        attrtab = (uu___2063_27008.attrtab);
        instantiate_imp = (uu___2063_27008.instantiate_imp);
        effects = (uu___2063_27008.effects);
        generalize = (uu___2063_27008.generalize);
        letrecs = (uu___2063_27008.letrecs);
        top_level = (uu___2063_27008.top_level);
        check_uvars = (uu___2063_27008.check_uvars);
        use_eq = (uu___2063_27008.use_eq);
        use_eq_strict = (uu___2063_27008.use_eq_strict);
        is_iface = (uu___2063_27008.is_iface);
        admit = (uu___2063_27008.admit);
        lax = (uu___2063_27008.lax);
        lax_universes = (uu___2063_27008.lax_universes);
        phase1 = (uu___2063_27008.phase1);
        failhard = (uu___2063_27008.failhard);
        nosynth = (uu___2063_27008.nosynth);
        uvar_subtyping = (uu___2063_27008.uvar_subtyping);
        tc_term = (uu___2063_27008.tc_term);
        type_of = (uu___2063_27008.type_of);
        universe_of = (uu___2063_27008.universe_of);
        check_type_of = (uu___2063_27008.check_type_of);
        use_bv_sorts = (uu___2063_27008.use_bv_sorts);
        qtbl_name_and_index = (uu___2063_27008.qtbl_name_and_index);
        normalized_eff_names = (uu___2063_27008.normalized_eff_names);
        fv_delta_depths = (uu___2063_27008.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2063_27008.synth_hook);
        try_solve_implicits_hook = (uu___2063_27008.try_solve_implicits_hook);
        splice = (uu___2063_27008.splice);
        mpreprocess = (uu___2063_27008.mpreprocess);
        postprocess = (uu___2063_27008.postprocess);
        is_native_tactic = (uu___2063_27008.is_native_tactic);
        identifier_info = (uu___2063_27008.identifier_info);
        tc_hooks = (uu___2063_27008.tc_hooks);
        dsenv = (uu___2063_27008.dsenv);
        nbe = (uu___2063_27008.nbe);
        strict_args_tab = (uu___2063_27008.strict_args_tab);
        erasable_types_tab = (uu___2063_27008.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____27024 = FStar_Syntax_Free.names t  in
      let uu____27027 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____27024 uu____27027
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27050 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27050
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27060 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27060
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27081 =
      match uu____27081 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27101 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27101)
       in
    let uu____27109 =
      let uu____27113 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27113 FStar_List.rev  in
    FStar_All.pipe_right uu____27109 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Common.guard_f = g;
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
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([],[]);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27181 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27181 with
                   | FStar_Pervasives_Native.Some uu____27185 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27188 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27198;
        FStar_TypeChecker_Common.univ_ineqs = uu____27199;
        FStar_TypeChecker_Common.implicits = uu____27200;_} -> true
    | uu____27210 -> false
  
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
          let uu___2107_27232 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2107_27232.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2107_27232.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2107_27232.FStar_TypeChecker_Common.implicits)
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
          let uu____27271 = FStar_Options.defensive ()  in
          if uu____27271
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27277 =
              let uu____27279 =
                let uu____27281 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27281  in
              Prims.op_Negation uu____27279  in
            (if uu____27277
             then
               let uu____27288 =
                 let uu____27294 =
                   let uu____27296 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27298 =
                     let uu____27300 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27300
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27296 uu____27298
                    in
                 (FStar_Errors.Warning_Defensive, uu____27294)  in
               FStar_Errors.log_issue rng uu____27288
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
          let uu____27340 =
            let uu____27342 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27342  in
          if uu____27340
          then ()
          else
            (let uu____27347 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27347 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27373 =
            let uu____27375 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27375  in
          if uu____27373
          then ()
          else
            (let uu____27380 = bound_vars e  in
             def_check_closed_in rng msg uu____27380 t)
  
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
          let uu___2144_27419 = g  in
          let uu____27420 =
            let uu____27421 =
              let uu____27422 =
                let uu____27429 =
                  let uu____27430 =
                    let uu____27447 =
                      let uu____27458 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27458]  in
                    (f, uu____27447)  in
                  FStar_Syntax_Syntax.Tm_app uu____27430  in
                FStar_Syntax_Syntax.mk uu____27429  in
              uu____27422 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27495  -> FStar_TypeChecker_Common.NonTrivial _27495)
              uu____27421
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27420;
            FStar_TypeChecker_Common.deferred =
              (uu___2144_27419.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2144_27419.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2144_27419.FStar_TypeChecker_Common.implicits)
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
          let uu___2151_27513 = g  in
          let uu____27514 =
            let uu____27515 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27515  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27514;
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27513.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27513.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27513.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2156_27532 = g  in
          let uu____27533 =
            let uu____27534 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27534  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27533;
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27532.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27532.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27532.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2160_27536 = g  in
          let uu____27537 =
            let uu____27538 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27538  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27537;
            FStar_TypeChecker_Common.deferred =
              (uu___2160_27536.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2160_27536.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2160_27536.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27545 ->
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
                       let uu____27622 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27622
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2183_27629 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2183_27629.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2183_27629.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2183_27629.FStar_TypeChecker_Common.implicits)
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
               let uu____27663 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27663
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
            let uu___2198_27690 = g  in
            let uu____27691 =
              let uu____27692 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27692  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27691;
              FStar_TypeChecker_Common.deferred =
                (uu___2198_27690.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2198_27690.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2198_27690.FStar_TypeChecker_Common.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Dyn.dyn * FStar_Syntax_Syntax.term)
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
              let uu____27750 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27750 with
              | FStar_Pervasives_Native.Some
                  (uu____27775::(tm,uu____27777)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27841 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27859 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27859;
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
                    (let uu____27891 =
                       debug env (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27891
                     then
                       let uu____27895 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27895
                     else ());
                    (let g =
                       let uu___2222_27901 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2222_27901.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2222_27901.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2222_27901.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27955 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28012  ->
                      fun b  ->
                        match uu____28012 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____28054 =
                              let uu____28067 = reason b  in
                              new_implicit_var_aux uu____28067 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____28054 with
                             | (t,uu____28084,g_t) ->
                                 let uu____28098 =
                                   let uu____28101 =
                                     let uu____28104 =
                                       let uu____28105 =
                                         let uu____28112 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28112, t)  in
                                       FStar_Syntax_Syntax.NT uu____28105  in
                                     [uu____28104]  in
                                   FStar_List.append substs1 uu____28101  in
                                 let uu____28123 = conj_guard g g_t  in
                                 (uu____28098,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28123))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27955
              (fun uu____28152  ->
                 match uu____28152 with
                 | (uu____28169,uvars1,g) -> (uvars1, g))
  
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
                let uu____28210 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28210 FStar_Util.must  in
              let uu____28227 = inst_tscheme_with post_ts [u]  in
              match uu____28227 with
              | (uu____28232,post) ->
                  let uu____28234 =
                    let uu____28239 =
                      let uu____28240 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28240]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28239  in
                  uu____28234 FStar_Pervasives_Native.None r
               in
            let uu____28273 =
              let uu____28278 =
                let uu____28279 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28279]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28278  in
            uu____28273 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28315  -> ());
    push = (fun uu____28317  -> ());
    pop = (fun uu____28320  -> ());
    snapshot =
      (fun uu____28323  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28342  -> fun uu____28343  -> ());
    encode_sig = (fun uu____28358  -> fun uu____28359  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28365 =
             let uu____28372 = FStar_Options.peek ()  in (e, g, uu____28372)
              in
           [uu____28365]);
    solve = (fun uu____28388  -> fun uu____28389  -> fun uu____28390  -> ());
    finish = (fun uu____28397  -> ());
    refresh = (fun uu____28399  -> ())
  } 