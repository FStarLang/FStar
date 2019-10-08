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
  fun projectee  -> match projectee with | Beta  -> true | uu____112 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____123 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____134 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____146 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____164 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____175 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____186 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____197 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____208 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____219 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____231 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____252 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____279 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____306 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____330 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____341 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____352 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____363 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____374 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____385 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____396 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____407 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____418 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____429 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____440 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____451 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____462 -> false
  
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
      | uu____522 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____548 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____559 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____570 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____582 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_term
  
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mlift
  
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
    }
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list)
  =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> decls 
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> order 
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> joins 
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type env =
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
  is_pattern: Prims.bool ;
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
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t)
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
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
    env -> FStar_Syntax_Syntax.term -> implicit Prims.list -> unit ;
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
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
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list)
    ;
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env -> env -> FStar_Syntax_Syntax.term -> implicit Prims.list -> unit) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> splice1
  
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
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
  
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> guard_f
  
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> implicits
  
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
  
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicits = implicit Prims.list
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
           (fun uu___0_13575  ->
              match uu___0_13575 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13578 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13578  in
                  let uu____13579 =
                    let uu____13580 = FStar_Syntax_Subst.compress y  in
                    uu____13580.FStar_Syntax_Syntax.n  in
                  (match uu____13579 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13584 =
                         let uu___338_13585 = y1  in
                         let uu____13586 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___338_13585.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___338_13585.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13586
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13584
                   | uu____13589 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___344_13603 = env  in
      let uu____13604 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___344_13603.solver);
        range = (uu___344_13603.range);
        curmodule = (uu___344_13603.curmodule);
        gamma = uu____13604;
        gamma_sig = (uu___344_13603.gamma_sig);
        gamma_cache = (uu___344_13603.gamma_cache);
        modules = (uu___344_13603.modules);
        expected_typ = (uu___344_13603.expected_typ);
        sigtab = (uu___344_13603.sigtab);
        attrtab = (uu___344_13603.attrtab);
        is_pattern = (uu___344_13603.is_pattern);
        instantiate_imp = (uu___344_13603.instantiate_imp);
        effects = (uu___344_13603.effects);
        generalize = (uu___344_13603.generalize);
        letrecs = (uu___344_13603.letrecs);
        top_level = (uu___344_13603.top_level);
        check_uvars = (uu___344_13603.check_uvars);
        use_eq = (uu___344_13603.use_eq);
        is_iface = (uu___344_13603.is_iface);
        admit = (uu___344_13603.admit);
        lax = (uu___344_13603.lax);
        lax_universes = (uu___344_13603.lax_universes);
        phase1 = (uu___344_13603.phase1);
        failhard = (uu___344_13603.failhard);
        nosynth = (uu___344_13603.nosynth);
        uvar_subtyping = (uu___344_13603.uvar_subtyping);
        tc_term = (uu___344_13603.tc_term);
        type_of = (uu___344_13603.type_of);
        universe_of = (uu___344_13603.universe_of);
        check_type_of = (uu___344_13603.check_type_of);
        use_bv_sorts = (uu___344_13603.use_bv_sorts);
        qtbl_name_and_index = (uu___344_13603.qtbl_name_and_index);
        normalized_eff_names = (uu___344_13603.normalized_eff_names);
        fv_delta_depths = (uu___344_13603.fv_delta_depths);
        proof_ns = (uu___344_13603.proof_ns);
        synth_hook = (uu___344_13603.synth_hook);
        try_solve_implicits_hook = (uu___344_13603.try_solve_implicits_hook);
        splice = (uu___344_13603.splice);
        postprocess = (uu___344_13603.postprocess);
        is_native_tactic = (uu___344_13603.is_native_tactic);
        identifier_info = (uu___344_13603.identifier_info);
        tc_hooks = (uu___344_13603.tc_hooks);
        dsenv = (uu___344_13603.dsenv);
        nbe = (uu___344_13603.nbe);
        strict_args_tab = (uu___344_13603.strict_args_tab);
        erasable_types_tab = (uu___344_13603.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13612  -> fun uu____13613  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___351_13635 = env  in
      {
        solver = (uu___351_13635.solver);
        range = (uu___351_13635.range);
        curmodule = (uu___351_13635.curmodule);
        gamma = (uu___351_13635.gamma);
        gamma_sig = (uu___351_13635.gamma_sig);
        gamma_cache = (uu___351_13635.gamma_cache);
        modules = (uu___351_13635.modules);
        expected_typ = (uu___351_13635.expected_typ);
        sigtab = (uu___351_13635.sigtab);
        attrtab = (uu___351_13635.attrtab);
        is_pattern = (uu___351_13635.is_pattern);
        instantiate_imp = (uu___351_13635.instantiate_imp);
        effects = (uu___351_13635.effects);
        generalize = (uu___351_13635.generalize);
        letrecs = (uu___351_13635.letrecs);
        top_level = (uu___351_13635.top_level);
        check_uvars = (uu___351_13635.check_uvars);
        use_eq = (uu___351_13635.use_eq);
        is_iface = (uu___351_13635.is_iface);
        admit = (uu___351_13635.admit);
        lax = (uu___351_13635.lax);
        lax_universes = (uu___351_13635.lax_universes);
        phase1 = (uu___351_13635.phase1);
        failhard = (uu___351_13635.failhard);
        nosynth = (uu___351_13635.nosynth);
        uvar_subtyping = (uu___351_13635.uvar_subtyping);
        tc_term = (uu___351_13635.tc_term);
        type_of = (uu___351_13635.type_of);
        universe_of = (uu___351_13635.universe_of);
        check_type_of = (uu___351_13635.check_type_of);
        use_bv_sorts = (uu___351_13635.use_bv_sorts);
        qtbl_name_and_index = (uu___351_13635.qtbl_name_and_index);
        normalized_eff_names = (uu___351_13635.normalized_eff_names);
        fv_delta_depths = (uu___351_13635.fv_delta_depths);
        proof_ns = (uu___351_13635.proof_ns);
        synth_hook = (uu___351_13635.synth_hook);
        try_solve_implicits_hook = (uu___351_13635.try_solve_implicits_hook);
        splice = (uu___351_13635.splice);
        postprocess = (uu___351_13635.postprocess);
        is_native_tactic = (uu___351_13635.is_native_tactic);
        identifier_info = (uu___351_13635.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___351_13635.dsenv);
        nbe = (uu___351_13635.nbe);
        strict_args_tab = (uu___351_13635.strict_args_tab);
        erasable_types_tab = (uu___351_13635.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___355_13647 = e  in
      let uu____13648 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___355_13647.solver);
        range = (uu___355_13647.range);
        curmodule = (uu___355_13647.curmodule);
        gamma = (uu___355_13647.gamma);
        gamma_sig = (uu___355_13647.gamma_sig);
        gamma_cache = (uu___355_13647.gamma_cache);
        modules = (uu___355_13647.modules);
        expected_typ = (uu___355_13647.expected_typ);
        sigtab = (uu___355_13647.sigtab);
        attrtab = (uu___355_13647.attrtab);
        is_pattern = (uu___355_13647.is_pattern);
        instantiate_imp = (uu___355_13647.instantiate_imp);
        effects = (uu___355_13647.effects);
        generalize = (uu___355_13647.generalize);
        letrecs = (uu___355_13647.letrecs);
        top_level = (uu___355_13647.top_level);
        check_uvars = (uu___355_13647.check_uvars);
        use_eq = (uu___355_13647.use_eq);
        is_iface = (uu___355_13647.is_iface);
        admit = (uu___355_13647.admit);
        lax = (uu___355_13647.lax);
        lax_universes = (uu___355_13647.lax_universes);
        phase1 = (uu___355_13647.phase1);
        failhard = (uu___355_13647.failhard);
        nosynth = (uu___355_13647.nosynth);
        uvar_subtyping = (uu___355_13647.uvar_subtyping);
        tc_term = (uu___355_13647.tc_term);
        type_of = (uu___355_13647.type_of);
        universe_of = (uu___355_13647.universe_of);
        check_type_of = (uu___355_13647.check_type_of);
        use_bv_sorts = (uu___355_13647.use_bv_sorts);
        qtbl_name_and_index = (uu___355_13647.qtbl_name_and_index);
        normalized_eff_names = (uu___355_13647.normalized_eff_names);
        fv_delta_depths = (uu___355_13647.fv_delta_depths);
        proof_ns = (uu___355_13647.proof_ns);
        synth_hook = (uu___355_13647.synth_hook);
        try_solve_implicits_hook = (uu___355_13647.try_solve_implicits_hook);
        splice = (uu___355_13647.splice);
        postprocess = (uu___355_13647.postprocess);
        is_native_tactic = (uu___355_13647.is_native_tactic);
        identifier_info = (uu___355_13647.identifier_info);
        tc_hooks = (uu___355_13647.tc_hooks);
        dsenv = uu____13648;
        nbe = (uu___355_13647.nbe);
        strict_args_tab = (uu___355_13647.strict_args_tab);
        erasable_types_tab = (uu___355_13647.erasable_types_tab)
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
      | (NoDelta ,uu____13677) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13680,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13682,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13685 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13699 . unit -> 'Auu____13699 FStar_Util.smap =
  fun uu____13706  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13712 . unit -> 'Auu____13712 FStar_Util.smap =
  fun uu____13719  -> FStar_Util.smap_create (Prims.of_int (100)) 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))
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
                  let uu____13857 = new_gamma_cache ()  in
                  let uu____13860 = new_sigtab ()  in
                  let uu____13863 = new_sigtab ()  in
                  let uu____13870 =
                    let uu____13885 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13885, FStar_Pervasives_Native.None)  in
                  let uu____13906 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13910 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13914 = FStar_Options.using_facts_from ()  in
                  let uu____13915 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13918 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13919 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13933 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13857;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13860;
                    attrtab = uu____13863;
                    is_pattern = false;
                    instantiate_imp = true;
                    effects = { decls = []; order = []; joins = [] };
                    generalize = true;
                    letrecs = [];
                    top_level = false;
                    check_uvars = false;
                    use_eq = false;
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
                    qtbl_name_and_index = uu____13870;
                    normalized_eff_names = uu____13906;
                    fv_delta_depths = uu____13910;
                    proof_ns = uu____13914;
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
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____14009  -> false);
                    identifier_info = uu____13915;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13918;
                    nbe = nbe1;
                    strict_args_tab = uu____13919;
                    erasable_types_tab = uu____13933
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
  fun uu____14088  ->
    let uu____14089 = FStar_ST.op_Bang query_indices  in
    match uu____14089 with
    | [] -> failwith "Empty query indices!"
    | uu____14144 ->
        let uu____14154 =
          let uu____14164 =
            let uu____14172 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14172  in
          let uu____14226 = FStar_ST.op_Bang query_indices  in uu____14164 ::
            uu____14226
           in
        FStar_ST.op_Colon_Equals query_indices uu____14154
  
let (pop_query_indices : unit -> unit) =
  fun uu____14322  ->
    let uu____14323 = FStar_ST.op_Bang query_indices  in
    match uu____14323 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14450  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14487  ->
    match uu____14487 with
    | (l,n1) ->
        let uu____14497 = FStar_ST.op_Bang query_indices  in
        (match uu____14497 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14619 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14642  ->
    let uu____14643 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14643
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14711 =
       let uu____14714 = FStar_ST.op_Bang stack  in env :: uu____14714  in
     FStar_ST.op_Colon_Equals stack uu____14711);
    (let uu___426_14763 = env  in
     let uu____14764 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14767 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14770 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14777 =
       let uu____14792 =
         let uu____14796 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14796  in
       let uu____14828 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14792, uu____14828)  in
     let uu____14877 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14880 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14883 =
       let uu____14886 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14886  in
     let uu____14906 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14919 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___426_14763.solver);
       range = (uu___426_14763.range);
       curmodule = (uu___426_14763.curmodule);
       gamma = (uu___426_14763.gamma);
       gamma_sig = (uu___426_14763.gamma_sig);
       gamma_cache = uu____14764;
       modules = (uu___426_14763.modules);
       expected_typ = (uu___426_14763.expected_typ);
       sigtab = uu____14767;
       attrtab = uu____14770;
       is_pattern = (uu___426_14763.is_pattern);
       instantiate_imp = (uu___426_14763.instantiate_imp);
       effects = (uu___426_14763.effects);
       generalize = (uu___426_14763.generalize);
       letrecs = (uu___426_14763.letrecs);
       top_level = (uu___426_14763.top_level);
       check_uvars = (uu___426_14763.check_uvars);
       use_eq = (uu___426_14763.use_eq);
       is_iface = (uu___426_14763.is_iface);
       admit = (uu___426_14763.admit);
       lax = (uu___426_14763.lax);
       lax_universes = (uu___426_14763.lax_universes);
       phase1 = (uu___426_14763.phase1);
       failhard = (uu___426_14763.failhard);
       nosynth = (uu___426_14763.nosynth);
       uvar_subtyping = (uu___426_14763.uvar_subtyping);
       tc_term = (uu___426_14763.tc_term);
       type_of = (uu___426_14763.type_of);
       universe_of = (uu___426_14763.universe_of);
       check_type_of = (uu___426_14763.check_type_of);
       use_bv_sorts = (uu___426_14763.use_bv_sorts);
       qtbl_name_and_index = uu____14777;
       normalized_eff_names = uu____14877;
       fv_delta_depths = uu____14880;
       proof_ns = (uu___426_14763.proof_ns);
       synth_hook = (uu___426_14763.synth_hook);
       try_solve_implicits_hook = (uu___426_14763.try_solve_implicits_hook);
       splice = (uu___426_14763.splice);
       postprocess = (uu___426_14763.postprocess);
       is_native_tactic = (uu___426_14763.is_native_tactic);
       identifier_info = uu____14883;
       tc_hooks = (uu___426_14763.tc_hooks);
       dsenv = (uu___426_14763.dsenv);
       nbe = (uu___426_14763.nbe);
       strict_args_tab = uu____14906;
       erasable_types_tab = uu____14919
     })
  
let (pop_stack : unit -> env) =
  fun uu____14929  ->
    let uu____14930 = FStar_ST.op_Bang stack  in
    match uu____14930 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14984 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15074  ->
           let uu____15075 = snapshot_stack env  in
           match uu____15075 with
           | (stack_depth,env1) ->
               let uu____15109 = snapshot_query_indices ()  in
               (match uu____15109 with
                | (query_indices_depth,()) ->
                    let uu____15142 = (env1.solver).snapshot msg  in
                    (match uu____15142 with
                     | (solver_depth,()) ->
                         let uu____15199 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____15199 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___451_15266 = env1  in
                                 {
                                   solver = (uu___451_15266.solver);
                                   range = (uu___451_15266.range);
                                   curmodule = (uu___451_15266.curmodule);
                                   gamma = (uu___451_15266.gamma);
                                   gamma_sig = (uu___451_15266.gamma_sig);
                                   gamma_cache = (uu___451_15266.gamma_cache);
                                   modules = (uu___451_15266.modules);
                                   expected_typ =
                                     (uu___451_15266.expected_typ);
                                   sigtab = (uu___451_15266.sigtab);
                                   attrtab = (uu___451_15266.attrtab);
                                   is_pattern = (uu___451_15266.is_pattern);
                                   instantiate_imp =
                                     (uu___451_15266.instantiate_imp);
                                   effects = (uu___451_15266.effects);
                                   generalize = (uu___451_15266.generalize);
                                   letrecs = (uu___451_15266.letrecs);
                                   top_level = (uu___451_15266.top_level);
                                   check_uvars = (uu___451_15266.check_uvars);
                                   use_eq = (uu___451_15266.use_eq);
                                   is_iface = (uu___451_15266.is_iface);
                                   admit = (uu___451_15266.admit);
                                   lax = (uu___451_15266.lax);
                                   lax_universes =
                                     (uu___451_15266.lax_universes);
                                   phase1 = (uu___451_15266.phase1);
                                   failhard = (uu___451_15266.failhard);
                                   nosynth = (uu___451_15266.nosynth);
                                   uvar_subtyping =
                                     (uu___451_15266.uvar_subtyping);
                                   tc_term = (uu___451_15266.tc_term);
                                   type_of = (uu___451_15266.type_of);
                                   universe_of = (uu___451_15266.universe_of);
                                   check_type_of =
                                     (uu___451_15266.check_type_of);
                                   use_bv_sorts =
                                     (uu___451_15266.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___451_15266.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___451_15266.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___451_15266.fv_delta_depths);
                                   proof_ns = (uu___451_15266.proof_ns);
                                   synth_hook = (uu___451_15266.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___451_15266.try_solve_implicits_hook);
                                   splice = (uu___451_15266.splice);
                                   postprocess = (uu___451_15266.postprocess);
                                   is_native_tactic =
                                     (uu___451_15266.is_native_tactic);
                                   identifier_info =
                                     (uu___451_15266.identifier_info);
                                   tc_hooks = (uu___451_15266.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___451_15266.nbe);
                                   strict_args_tab =
                                     (uu___451_15266.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___451_15266.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15300  ->
             let uu____15301 =
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
             match uu____15301 with
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
                             ((let uu____15481 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15481
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15497 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15497
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15529,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15571 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15601  ->
                  match uu____15601 with
                  | (m,uu____15609) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15571 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___496_15624 = env  in
               {
                 solver = (uu___496_15624.solver);
                 range = (uu___496_15624.range);
                 curmodule = (uu___496_15624.curmodule);
                 gamma = (uu___496_15624.gamma);
                 gamma_sig = (uu___496_15624.gamma_sig);
                 gamma_cache = (uu___496_15624.gamma_cache);
                 modules = (uu___496_15624.modules);
                 expected_typ = (uu___496_15624.expected_typ);
                 sigtab = (uu___496_15624.sigtab);
                 attrtab = (uu___496_15624.attrtab);
                 is_pattern = (uu___496_15624.is_pattern);
                 instantiate_imp = (uu___496_15624.instantiate_imp);
                 effects = (uu___496_15624.effects);
                 generalize = (uu___496_15624.generalize);
                 letrecs = (uu___496_15624.letrecs);
                 top_level = (uu___496_15624.top_level);
                 check_uvars = (uu___496_15624.check_uvars);
                 use_eq = (uu___496_15624.use_eq);
                 is_iface = (uu___496_15624.is_iface);
                 admit = (uu___496_15624.admit);
                 lax = (uu___496_15624.lax);
                 lax_universes = (uu___496_15624.lax_universes);
                 phase1 = (uu___496_15624.phase1);
                 failhard = (uu___496_15624.failhard);
                 nosynth = (uu___496_15624.nosynth);
                 uvar_subtyping = (uu___496_15624.uvar_subtyping);
                 tc_term = (uu___496_15624.tc_term);
                 type_of = (uu___496_15624.type_of);
                 universe_of = (uu___496_15624.universe_of);
                 check_type_of = (uu___496_15624.check_type_of);
                 use_bv_sorts = (uu___496_15624.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___496_15624.normalized_eff_names);
                 fv_delta_depths = (uu___496_15624.fv_delta_depths);
                 proof_ns = (uu___496_15624.proof_ns);
                 synth_hook = (uu___496_15624.synth_hook);
                 try_solve_implicits_hook =
                   (uu___496_15624.try_solve_implicits_hook);
                 splice = (uu___496_15624.splice);
                 postprocess = (uu___496_15624.postprocess);
                 is_native_tactic = (uu___496_15624.is_native_tactic);
                 identifier_info = (uu___496_15624.identifier_info);
                 tc_hooks = (uu___496_15624.tc_hooks);
                 dsenv = (uu___496_15624.dsenv);
                 nbe = (uu___496_15624.nbe);
                 strict_args_tab = (uu___496_15624.strict_args_tab);
                 erasable_types_tab = (uu___496_15624.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15641,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___505_15657 = env  in
               {
                 solver = (uu___505_15657.solver);
                 range = (uu___505_15657.range);
                 curmodule = (uu___505_15657.curmodule);
                 gamma = (uu___505_15657.gamma);
                 gamma_sig = (uu___505_15657.gamma_sig);
                 gamma_cache = (uu___505_15657.gamma_cache);
                 modules = (uu___505_15657.modules);
                 expected_typ = (uu___505_15657.expected_typ);
                 sigtab = (uu___505_15657.sigtab);
                 attrtab = (uu___505_15657.attrtab);
                 is_pattern = (uu___505_15657.is_pattern);
                 instantiate_imp = (uu___505_15657.instantiate_imp);
                 effects = (uu___505_15657.effects);
                 generalize = (uu___505_15657.generalize);
                 letrecs = (uu___505_15657.letrecs);
                 top_level = (uu___505_15657.top_level);
                 check_uvars = (uu___505_15657.check_uvars);
                 use_eq = (uu___505_15657.use_eq);
                 is_iface = (uu___505_15657.is_iface);
                 admit = (uu___505_15657.admit);
                 lax = (uu___505_15657.lax);
                 lax_universes = (uu___505_15657.lax_universes);
                 phase1 = (uu___505_15657.phase1);
                 failhard = (uu___505_15657.failhard);
                 nosynth = (uu___505_15657.nosynth);
                 uvar_subtyping = (uu___505_15657.uvar_subtyping);
                 tc_term = (uu___505_15657.tc_term);
                 type_of = (uu___505_15657.type_of);
                 universe_of = (uu___505_15657.universe_of);
                 check_type_of = (uu___505_15657.check_type_of);
                 use_bv_sorts = (uu___505_15657.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___505_15657.normalized_eff_names);
                 fv_delta_depths = (uu___505_15657.fv_delta_depths);
                 proof_ns = (uu___505_15657.proof_ns);
                 synth_hook = (uu___505_15657.synth_hook);
                 try_solve_implicits_hook =
                   (uu___505_15657.try_solve_implicits_hook);
                 splice = (uu___505_15657.splice);
                 postprocess = (uu___505_15657.postprocess);
                 is_native_tactic = (uu___505_15657.is_native_tactic);
                 identifier_info = (uu___505_15657.identifier_info);
                 tc_hooks = (uu___505_15657.tc_hooks);
                 dsenv = (uu___505_15657.dsenv);
                 nbe = (uu___505_15657.nbe);
                 strict_args_tab = (uu___505_15657.strict_args_tab);
                 erasable_types_tab = (uu___505_15657.erasable_types_tab)
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
        (let uu___512_15700 = e  in
         {
           solver = (uu___512_15700.solver);
           range = r;
           curmodule = (uu___512_15700.curmodule);
           gamma = (uu___512_15700.gamma);
           gamma_sig = (uu___512_15700.gamma_sig);
           gamma_cache = (uu___512_15700.gamma_cache);
           modules = (uu___512_15700.modules);
           expected_typ = (uu___512_15700.expected_typ);
           sigtab = (uu___512_15700.sigtab);
           attrtab = (uu___512_15700.attrtab);
           is_pattern = (uu___512_15700.is_pattern);
           instantiate_imp = (uu___512_15700.instantiate_imp);
           effects = (uu___512_15700.effects);
           generalize = (uu___512_15700.generalize);
           letrecs = (uu___512_15700.letrecs);
           top_level = (uu___512_15700.top_level);
           check_uvars = (uu___512_15700.check_uvars);
           use_eq = (uu___512_15700.use_eq);
           is_iface = (uu___512_15700.is_iface);
           admit = (uu___512_15700.admit);
           lax = (uu___512_15700.lax);
           lax_universes = (uu___512_15700.lax_universes);
           phase1 = (uu___512_15700.phase1);
           failhard = (uu___512_15700.failhard);
           nosynth = (uu___512_15700.nosynth);
           uvar_subtyping = (uu___512_15700.uvar_subtyping);
           tc_term = (uu___512_15700.tc_term);
           type_of = (uu___512_15700.type_of);
           universe_of = (uu___512_15700.universe_of);
           check_type_of = (uu___512_15700.check_type_of);
           use_bv_sorts = (uu___512_15700.use_bv_sorts);
           qtbl_name_and_index = (uu___512_15700.qtbl_name_and_index);
           normalized_eff_names = (uu___512_15700.normalized_eff_names);
           fv_delta_depths = (uu___512_15700.fv_delta_depths);
           proof_ns = (uu___512_15700.proof_ns);
           synth_hook = (uu___512_15700.synth_hook);
           try_solve_implicits_hook =
             (uu___512_15700.try_solve_implicits_hook);
           splice = (uu___512_15700.splice);
           postprocess = (uu___512_15700.postprocess);
           is_native_tactic = (uu___512_15700.is_native_tactic);
           identifier_info = (uu___512_15700.identifier_info);
           tc_hooks = (uu___512_15700.tc_hooks);
           dsenv = (uu___512_15700.dsenv);
           nbe = (uu___512_15700.nbe);
           strict_args_tab = (uu___512_15700.strict_args_tab);
           erasable_types_tab = (uu___512_15700.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15720 =
        let uu____15721 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15721 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15720
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15776 =
          let uu____15777 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15777 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15776
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15832 =
          let uu____15833 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15833 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15832
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15888 =
        let uu____15889 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15889 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15888
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___529_15953 = env  in
      {
        solver = (uu___529_15953.solver);
        range = (uu___529_15953.range);
        curmodule = lid;
        gamma = (uu___529_15953.gamma);
        gamma_sig = (uu___529_15953.gamma_sig);
        gamma_cache = (uu___529_15953.gamma_cache);
        modules = (uu___529_15953.modules);
        expected_typ = (uu___529_15953.expected_typ);
        sigtab = (uu___529_15953.sigtab);
        attrtab = (uu___529_15953.attrtab);
        is_pattern = (uu___529_15953.is_pattern);
        instantiate_imp = (uu___529_15953.instantiate_imp);
        effects = (uu___529_15953.effects);
        generalize = (uu___529_15953.generalize);
        letrecs = (uu___529_15953.letrecs);
        top_level = (uu___529_15953.top_level);
        check_uvars = (uu___529_15953.check_uvars);
        use_eq = (uu___529_15953.use_eq);
        is_iface = (uu___529_15953.is_iface);
        admit = (uu___529_15953.admit);
        lax = (uu___529_15953.lax);
        lax_universes = (uu___529_15953.lax_universes);
        phase1 = (uu___529_15953.phase1);
        failhard = (uu___529_15953.failhard);
        nosynth = (uu___529_15953.nosynth);
        uvar_subtyping = (uu___529_15953.uvar_subtyping);
        tc_term = (uu___529_15953.tc_term);
        type_of = (uu___529_15953.type_of);
        universe_of = (uu___529_15953.universe_of);
        check_type_of = (uu___529_15953.check_type_of);
        use_bv_sorts = (uu___529_15953.use_bv_sorts);
        qtbl_name_and_index = (uu___529_15953.qtbl_name_and_index);
        normalized_eff_names = (uu___529_15953.normalized_eff_names);
        fv_delta_depths = (uu___529_15953.fv_delta_depths);
        proof_ns = (uu___529_15953.proof_ns);
        synth_hook = (uu___529_15953.synth_hook);
        try_solve_implicits_hook = (uu___529_15953.try_solve_implicits_hook);
        splice = (uu___529_15953.splice);
        postprocess = (uu___529_15953.postprocess);
        is_native_tactic = (uu___529_15953.is_native_tactic);
        identifier_info = (uu___529_15953.identifier_info);
        tc_hooks = (uu___529_15953.tc_hooks);
        dsenv = (uu___529_15953.dsenv);
        nbe = (uu___529_15953.nbe);
        strict_args_tab = (uu___529_15953.strict_args_tab);
        erasable_types_tab = (uu___529_15953.erasable_types_tab)
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
      let uu____15984 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15984
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15997 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15997)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16012 =
      let uu____16014 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16014  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16012)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16023  ->
    let uu____16024 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16024
  
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
      | ((formals,t),uu____16124) ->
          let vs = mk_univ_subst formals us  in
          let uu____16148 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16148)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16165  ->
    match uu___1_16165 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16191  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16211 = inst_tscheme t  in
      match uu____16211 with
      | (us,t1) ->
          let uu____16222 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16222)
  
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
          let uu____16247 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16249 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16247 uu____16249
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
        fun uu____16276  ->
          match uu____16276 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16290 =
                    let uu____16292 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16296 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16300 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16302 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16292 uu____16296 uu____16300 uu____16302
                     in
                  failwith uu____16290)
               else ();
               (let uu____16307 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16307))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16325 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16336 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16347 -> false
  
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
             | ([],uu____16395) -> Maybe
             | (uu____16402,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16422 -> No  in
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
          let uu____16516 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16516 with
          | FStar_Pervasives_Native.None  ->
              let uu____16539 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16583  ->
                     match uu___2_16583 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16622 = FStar_Ident.lid_equals lid l  in
                         if uu____16622
                         then
                           let uu____16645 =
                             let uu____16664 =
                               let uu____16679 = inst_tscheme t  in
                               FStar_Util.Inl uu____16679  in
                             let uu____16694 = FStar_Ident.range_of_lid l  in
                             (uu____16664, uu____16694)  in
                           FStar_Pervasives_Native.Some uu____16645
                         else FStar_Pervasives_Native.None
                     | uu____16747 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16539
                (fun uu____16785  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16795  ->
                        match uu___3_16795 with
                        | (uu____16798,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16800);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16801;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16802;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16803;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16804;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16805;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16827 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16827
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
                                  uu____16879 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16886 -> cache t  in
                            let uu____16887 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16887 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16893 =
                                   let uu____16894 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16894)
                                    in
                                 maybe_cache uu____16893)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16965 = find_in_sigtab env lid  in
         match uu____16965 with
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
      let uu____17046 = lookup_qname env lid  in
      match uu____17046 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17067,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17181 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17181 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____17226 =
          let uu____17229 = lookup_attr env1 attr  in se1 :: uu____17229  in
        FStar_Util.smap_add (attrtab env1) attr uu____17226  in
      FStar_List.iter
        (fun attr  ->
           let uu____17239 =
             let uu____17240 = FStar_Syntax_Subst.compress attr  in
             uu____17240.FStar_Syntax_Syntax.n  in
           match uu____17239 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17244 =
                 let uu____17246 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____17246.FStar_Ident.str  in
               add_one1 env se uu____17244
           | uu____17247 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17270) ->
          add_sigelts env ses
      | uu____17279 ->
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
        (fun uu___4_17317  ->
           match uu___4_17317 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17335 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17397,lb::[]),uu____17399) ->
            let uu____17408 =
              let uu____17417 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17426 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17417, uu____17426)  in
            FStar_Pervasives_Native.Some uu____17408
        | FStar_Syntax_Syntax.Sig_let ((uu____17439,lbs),uu____17441) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17473 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17486 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17486
                     then
                       let uu____17499 =
                         let uu____17508 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17517 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17508, uu____17517)  in
                       FStar_Pervasives_Native.Some uu____17499
                     else FStar_Pervasives_Native.None)
        | uu____17540 -> FStar_Pervasives_Native.None
  
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
                    let uu____17632 =
                      let uu____17634 =
                        let uu____17636 =
                          let uu____17638 =
                            let uu____17640 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17646 =
                              let uu____17648 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17648  in
                            Prims.op_Hat uu____17640 uu____17646  in
                          Prims.op_Hat ", expected " uu____17638  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17636
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17634
                       in
                    failwith uu____17632
                  else ());
             (let uu____17655 =
                let uu____17664 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17664, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17655))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17684,uu____17685) ->
            let uu____17690 =
              let uu____17699 =
                let uu____17704 =
                  let uu____17705 =
                    let uu____17708 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17708  in
                  (us, uu____17705)  in
                inst_ts us_opt uu____17704  in
              (uu____17699, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17690
        | uu____17727 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17816 =
          match uu____17816 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17912,uvs,t,uu____17915,uu____17916,uu____17917);
                      FStar_Syntax_Syntax.sigrng = uu____17918;
                      FStar_Syntax_Syntax.sigquals = uu____17919;
                      FStar_Syntax_Syntax.sigmeta = uu____17920;
                      FStar_Syntax_Syntax.sigattrs = uu____17921;
                      FStar_Syntax_Syntax.sigopts = uu____17922;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17947 =
                     let uu____17956 = inst_tscheme1 (uvs, t)  in
                     (uu____17956, rng)  in
                   FStar_Pervasives_Native.Some uu____17947
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17980;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17982;
                      FStar_Syntax_Syntax.sigattrs = uu____17983;
                      FStar_Syntax_Syntax.sigopts = uu____17984;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18003 =
                     let uu____18005 = in_cur_mod env l  in uu____18005 = Yes
                      in
                   if uu____18003
                   then
                     let uu____18017 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18017
                      then
                        let uu____18033 =
                          let uu____18042 = inst_tscheme1 (uvs, t)  in
                          (uu____18042, rng)  in
                        FStar_Pervasives_Native.Some uu____18033
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18075 =
                        let uu____18084 = inst_tscheme1 (uvs, t)  in
                        (uu____18084, rng)  in
                      FStar_Pervasives_Native.Some uu____18075)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18109,uu____18110);
                      FStar_Syntax_Syntax.sigrng = uu____18111;
                      FStar_Syntax_Syntax.sigquals = uu____18112;
                      FStar_Syntax_Syntax.sigmeta = uu____18113;
                      FStar_Syntax_Syntax.sigattrs = uu____18114;
                      FStar_Syntax_Syntax.sigopts = uu____18115;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18158 =
                          let uu____18167 = inst_tscheme1 (uvs, k)  in
                          (uu____18167, rng)  in
                        FStar_Pervasives_Native.Some uu____18158
                    | uu____18188 ->
                        let uu____18189 =
                          let uu____18198 =
                            let uu____18203 =
                              let uu____18204 =
                                let uu____18207 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18207
                                 in
                              (uvs, uu____18204)  in
                            inst_tscheme1 uu____18203  in
                          (uu____18198, rng)  in
                        FStar_Pervasives_Native.Some uu____18189)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18230,uu____18231);
                      FStar_Syntax_Syntax.sigrng = uu____18232;
                      FStar_Syntax_Syntax.sigquals = uu____18233;
                      FStar_Syntax_Syntax.sigmeta = uu____18234;
                      FStar_Syntax_Syntax.sigattrs = uu____18235;
                      FStar_Syntax_Syntax.sigopts = uu____18236;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18280 =
                          let uu____18289 = inst_tscheme_with (uvs, k) us  in
                          (uu____18289, rng)  in
                        FStar_Pervasives_Native.Some uu____18280
                    | uu____18310 ->
                        let uu____18311 =
                          let uu____18320 =
                            let uu____18325 =
                              let uu____18326 =
                                let uu____18329 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18329
                                 in
                              (uvs, uu____18326)  in
                            inst_tscheme_with uu____18325 us  in
                          (uu____18320, rng)  in
                        FStar_Pervasives_Native.Some uu____18311)
               | FStar_Util.Inr se ->
                   let uu____18365 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18386;
                          FStar_Syntax_Syntax.sigrng = uu____18387;
                          FStar_Syntax_Syntax.sigquals = uu____18388;
                          FStar_Syntax_Syntax.sigmeta = uu____18389;
                          FStar_Syntax_Syntax.sigattrs = uu____18390;
                          FStar_Syntax_Syntax.sigopts = uu____18391;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18408 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18365
                     (FStar_Util.map_option
                        (fun uu____18456  ->
                           match uu____18456 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18487 =
          let uu____18498 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18498 mapper  in
        match uu____18487 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18572 =
              let uu____18583 =
                let uu____18590 =
                  let uu___866_18593 = t  in
                  let uu____18594 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___866_18593.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18594;
                    FStar_Syntax_Syntax.vars =
                      (uu___866_18593.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18590)  in
              (uu____18583, r)  in
            FStar_Pervasives_Native.Some uu____18572
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18643 = lookup_qname env l  in
      match uu____18643 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18664 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18718 = try_lookup_bv env bv  in
      match uu____18718 with
      | FStar_Pervasives_Native.None  ->
          let uu____18733 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18733 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18749 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18750 =
            let uu____18751 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18751  in
          (uu____18749, uu____18750)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18773 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18773 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18839 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18839  in
          let uu____18840 =
            let uu____18849 =
              let uu____18854 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18854)  in
            (uu____18849, r1)  in
          FStar_Pervasives_Native.Some uu____18840
  
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
        let uu____18889 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18889 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18922,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18947 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18947  in
            let uu____18948 =
              let uu____18953 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18953, r1)  in
            FStar_Pervasives_Native.Some uu____18948
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18977 = try_lookup_lid env l  in
      match uu____18977 with
      | FStar_Pervasives_Native.None  ->
          let uu____19004 = name_not_found l  in
          let uu____19010 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19004 uu____19010
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19053  ->
              match uu___5_19053 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19057 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19078 = lookup_qname env lid  in
      match uu____19078 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19087,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19090;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19092;
              FStar_Syntax_Syntax.sigattrs = uu____19093;
              FStar_Syntax_Syntax.sigopts = uu____19094;_},FStar_Pervasives_Native.None
            ),uu____19095)
          ->
          let uu____19146 =
            let uu____19153 =
              let uu____19154 =
                let uu____19157 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19157 t  in
              (uvs, uu____19154)  in
            (uu____19153, q)  in
          FStar_Pervasives_Native.Some uu____19146
      | uu____19170 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19192 = lookup_qname env lid  in
      match uu____19192 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19197,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19200;
              FStar_Syntax_Syntax.sigquals = uu____19201;
              FStar_Syntax_Syntax.sigmeta = uu____19202;
              FStar_Syntax_Syntax.sigattrs = uu____19203;
              FStar_Syntax_Syntax.sigopts = uu____19204;_},FStar_Pervasives_Native.None
            ),uu____19205)
          ->
          let uu____19256 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19256 (uvs, t)
      | uu____19261 ->
          let uu____19262 = name_not_found lid  in
          let uu____19268 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19262 uu____19268
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19288 = lookup_qname env lid  in
      match uu____19288 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19293,uvs,t,uu____19296,uu____19297,uu____19298);
              FStar_Syntax_Syntax.sigrng = uu____19299;
              FStar_Syntax_Syntax.sigquals = uu____19300;
              FStar_Syntax_Syntax.sigmeta = uu____19301;
              FStar_Syntax_Syntax.sigattrs = uu____19302;
              FStar_Syntax_Syntax.sigopts = uu____19303;_},FStar_Pervasives_Native.None
            ),uu____19304)
          ->
          let uu____19361 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19361 (uvs, t)
      | uu____19366 ->
          let uu____19367 = name_not_found lid  in
          let uu____19373 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19367 uu____19373
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19396 = lookup_qname env lid  in
      match uu____19396 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19404,uu____19405,uu____19406,uu____19407,uu____19408,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19410;
              FStar_Syntax_Syntax.sigquals = uu____19411;
              FStar_Syntax_Syntax.sigmeta = uu____19412;
              FStar_Syntax_Syntax.sigattrs = uu____19413;
              FStar_Syntax_Syntax.sigopts = uu____19414;_},uu____19415),uu____19416)
          -> (true, dcs)
      | uu____19481 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19497 = lookup_qname env lid  in
      match uu____19497 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19498,uu____19499,uu____19500,l,uu____19502,uu____19503);
              FStar_Syntax_Syntax.sigrng = uu____19504;
              FStar_Syntax_Syntax.sigquals = uu____19505;
              FStar_Syntax_Syntax.sigmeta = uu____19506;
              FStar_Syntax_Syntax.sigattrs = uu____19507;
              FStar_Syntax_Syntax.sigopts = uu____19508;_},uu____19509),uu____19510)
          -> l
      | uu____19569 ->
          let uu____19570 =
            let uu____19572 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19572  in
          failwith uu____19570
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19642)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19699) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19723 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19723
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19758 -> FStar_Pervasives_Native.None)
          | uu____19767 -> FStar_Pervasives_Native.None
  
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
        let uu____19829 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19829
  
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
        let uu____19862 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19862
  
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
             (FStar_Util.Inl uu____19914,uu____19915) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19964),uu____19965) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20014 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20032 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20042 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20059 ->
                  let uu____20066 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20066
              | FStar_Syntax_Syntax.Sig_let ((uu____20067,lbs),uu____20069)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20085 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20085
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____20092 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____20100 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20101 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20108 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20109 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20110 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20111 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20124 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20142 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20142
           (fun d_opt  ->
              let uu____20155 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20155
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20165 =
                   let uu____20168 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20168  in
                 match uu____20165 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20169 =
                       let uu____20171 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20171
                        in
                     failwith uu____20169
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20176 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20176
                       then
                         let uu____20179 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20181 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20183 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20179 uu____20181 uu____20183
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
        (FStar_Util.Inr (se,uu____20208),uu____20209) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20258 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20280),uu____20281) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20330 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20352 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20352
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20385 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20385 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20407 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20416 =
                        let uu____20417 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20417.FStar_Syntax_Syntax.n  in
                      match uu____20416 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20422 -> false))
               in
            (true, uu____20407)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20445 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20445
  
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
          let uu____20517 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20517.FStar_Ident.str  in
        let uu____20518 = FStar_Util.smap_try_find tab s  in
        match uu____20518 with
        | FStar_Pervasives_Native.None  ->
            let uu____20521 = f ()  in
            (match uu____20521 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20559 =
        let uu____20560 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20560 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20594 =
        let uu____20595 = FStar_Syntax_Util.unrefine t  in
        uu____20595.FStar_Syntax_Syntax.n  in
      match uu____20594 with
      | FStar_Syntax_Syntax.Tm_type uu____20599 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20603) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20629) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20634,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20656 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20689 =
        let attrs =
          let uu____20695 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20695  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20735 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20735)
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
      let uu____20780 = lookup_qname env ftv  in
      match uu____20780 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20784) ->
          let uu____20829 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20829 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20850,t),r) ->
               let uu____20865 =
                 let uu____20866 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20866 t  in
               FStar_Pervasives_Native.Some uu____20865)
      | uu____20867 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20879 = try_lookup_effect_lid env ftv  in
      match uu____20879 with
      | FStar_Pervasives_Native.None  ->
          let uu____20882 = name_not_found ftv  in
          let uu____20888 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20882 uu____20888
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
        let uu____20912 = lookup_qname env lid0  in
        match uu____20912 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20923);
                FStar_Syntax_Syntax.sigrng = uu____20924;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20926;
                FStar_Syntax_Syntax.sigattrs = uu____20927;
                FStar_Syntax_Syntax.sigopts = uu____20928;_},FStar_Pervasives_Native.None
              ),uu____20929)
            ->
            let lid1 =
              let uu____20985 =
                let uu____20986 = FStar_Ident.range_of_lid lid  in
                let uu____20987 =
                  let uu____20988 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20988  in
                FStar_Range.set_use_range uu____20986 uu____20987  in
              FStar_Ident.set_lid_range lid uu____20985  in
            let uu____20989 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20995  ->
                      match uu___6_20995 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20998 -> false))
               in
            if uu____20989
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21017 =
                      let uu____21019 =
                        let uu____21021 = get_range env  in
                        FStar_Range.string_of_range uu____21021  in
                      let uu____21022 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21024 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21019 uu____21022 uu____21024
                       in
                    failwith uu____21017)
                  in
               match (binders, univs1) with
               | ([],uu____21045) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21071,uu____21072::uu____21073::uu____21074) ->
                   let uu____21095 =
                     let uu____21097 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21099 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21097 uu____21099
                      in
                   failwith uu____21095
               | uu____21110 ->
                   let uu____21125 =
                     let uu____21130 =
                       let uu____21131 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21131)  in
                     inst_tscheme_with uu____21130 insts  in
                   (match uu____21125 with
                    | (uu____21144,t) ->
                        let t1 =
                          let uu____21147 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21147 t  in
                        let uu____21148 =
                          let uu____21149 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21149.FStar_Syntax_Syntax.n  in
                        (match uu____21148 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21184 -> failwith "Impossible")))
        | uu____21192 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____21216 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21216 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21229,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21236 = find1 l2  in
            (match uu____21236 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21243 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____21243 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21247 = find1 l  in
            (match uu____21247 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____21252 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21252
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21267 = lookup_qname env l1  in
      match uu____21267 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21270;
              FStar_Syntax_Syntax.sigrng = uu____21271;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21273;
              FStar_Syntax_Syntax.sigattrs = uu____21274;
              FStar_Syntax_Syntax.sigopts = uu____21275;_},uu____21276),uu____21277)
          -> q
      | uu____21330 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21354 =
          let uu____21355 =
            let uu____21357 = FStar_Util.string_of_int i  in
            let uu____21359 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21357 uu____21359
             in
          failwith uu____21355  in
        let uu____21362 = lookup_datacon env lid  in
        match uu____21362 with
        | (uu____21367,t) ->
            let uu____21369 =
              let uu____21370 = FStar_Syntax_Subst.compress t  in
              uu____21370.FStar_Syntax_Syntax.n  in
            (match uu____21369 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21374) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21418 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21418
                      FStar_Pervasives_Native.fst)
             | uu____21429 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21443 = lookup_qname env l  in
      match uu____21443 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21445,uu____21446,uu____21447);
              FStar_Syntax_Syntax.sigrng = uu____21448;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21450;
              FStar_Syntax_Syntax.sigattrs = uu____21451;
              FStar_Syntax_Syntax.sigopts = uu____21452;_},uu____21453),uu____21454)
          ->
          FStar_Util.for_some
            (fun uu___7_21509  ->
               match uu___7_21509 with
               | FStar_Syntax_Syntax.Projector uu____21511 -> true
               | uu____21517 -> false) quals
      | uu____21519 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21533 = lookup_qname env lid  in
      match uu____21533 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21535,uu____21536,uu____21537,uu____21538,uu____21539,uu____21540);
              FStar_Syntax_Syntax.sigrng = uu____21541;
              FStar_Syntax_Syntax.sigquals = uu____21542;
              FStar_Syntax_Syntax.sigmeta = uu____21543;
              FStar_Syntax_Syntax.sigattrs = uu____21544;
              FStar_Syntax_Syntax.sigopts = uu____21545;_},uu____21546),uu____21547)
          -> true
      | uu____21607 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21621 = lookup_qname env lid  in
      match uu____21621 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21623,uu____21624,uu____21625,uu____21626,uu____21627,uu____21628);
              FStar_Syntax_Syntax.sigrng = uu____21629;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21631;
              FStar_Syntax_Syntax.sigattrs = uu____21632;
              FStar_Syntax_Syntax.sigopts = uu____21633;_},uu____21634),uu____21635)
          ->
          FStar_Util.for_some
            (fun uu___8_21698  ->
               match uu___8_21698 with
               | FStar_Syntax_Syntax.RecordType uu____21700 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21710 -> true
               | uu____21720 -> false) quals
      | uu____21722 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21732,uu____21733);
            FStar_Syntax_Syntax.sigrng = uu____21734;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21736;
            FStar_Syntax_Syntax.sigattrs = uu____21737;
            FStar_Syntax_Syntax.sigopts = uu____21738;_},uu____21739),uu____21740)
        ->
        FStar_Util.for_some
          (fun uu___9_21799  ->
             match uu___9_21799 with
             | FStar_Syntax_Syntax.Action uu____21801 -> true
             | uu____21803 -> false) quals
    | uu____21805 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21819 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21819
  
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
      let uu____21836 =
        let uu____21837 = FStar_Syntax_Util.un_uinst head1  in
        uu____21837.FStar_Syntax_Syntax.n  in
      match uu____21836 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21843 ->
               true
           | uu____21846 -> false)
      | uu____21848 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21862 = lookup_qname env l  in
      match uu____21862 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21865),uu____21866) ->
          FStar_Util.for_some
            (fun uu___10_21914  ->
               match uu___10_21914 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21917 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21919 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21995 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22013) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22031 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22039 ->
                 FStar_Pervasives_Native.Some true
             | uu____22058 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22061 =
        let uu____22065 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22065 mapper  in
      match uu____22061 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____22125 = lookup_qname env lid  in
      match uu____22125 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22129,uu____22130,tps,uu____22132,uu____22133,uu____22134);
              FStar_Syntax_Syntax.sigrng = uu____22135;
              FStar_Syntax_Syntax.sigquals = uu____22136;
              FStar_Syntax_Syntax.sigmeta = uu____22137;
              FStar_Syntax_Syntax.sigattrs = uu____22138;
              FStar_Syntax_Syntax.sigopts = uu____22139;_},uu____22140),uu____22141)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22209 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22255  ->
              match uu____22255 with
              | (d,uu____22264) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____22280 = effect_decl_opt env l  in
      match uu____22280 with
      | FStar_Pervasives_Native.None  ->
          let uu____22295 = name_not_found l  in
          let uu____22301 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22295 uu____22301
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____22324  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22343  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22375 = FStar_Ident.lid_equals l1 l2  in
        if uu____22375
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____22386 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22386
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____22397 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22450  ->
                        match uu____22450 with
                        | (m1,m2,uu____22464,uu____22465,uu____22466) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22397 with
              | FStar_Pervasives_Native.None  ->
                  let uu____22483 =
                    let uu____22489 =
                      let uu____22491 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____22493 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____22491
                        uu____22493
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22489)
                     in
                  FStar_Errors.raise_error uu____22483 env.range
              | FStar_Pervasives_Native.Some
                  (uu____22503,uu____22504,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22538 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22538
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
  'Auu____22558 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22558) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22587 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22613  ->
                match uu____22613 with
                | (d,uu____22620) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22587 with
      | FStar_Pervasives_Native.None  ->
          let uu____22631 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22631
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22646 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22646 with
           | (uu____22657,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22675)::(wp,uu____22677)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22733 -> failwith "Impossible"))
  
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
        | uu____22798 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22811 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22811 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22828 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22828 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22853 =
                     let uu____22859 =
                       let uu____22861 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22869 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22880 =
                         let uu____22882 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22882  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22861 uu____22869 uu____22880
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22859)
                      in
                   FStar_Errors.raise_error uu____22853
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22890 =
                     let uu____22901 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22901 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22938  ->
                        fun uu____22939  ->
                          match (uu____22938, uu____22939) with
                          | ((x,uu____22969),(t,uu____22971)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22890
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23002 =
                     let uu___1603_23003 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1603_23003.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1603_23003.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1603_23003.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1603_23003.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23002
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23015 .
    'Auu____23015 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23045 = effect_decl_opt env effect_name  in
          match uu____23045 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____23088 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____23111 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____23150 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____23150
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____23155 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____23155
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____23166 =
                     let uu____23169 = get_range env  in
                     let uu____23170 =
                       let uu____23177 =
                         let uu____23178 =
                           let uu____23195 =
                             let uu____23206 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23206; wp]  in
                           (repr, uu____23195)  in
                         FStar_Syntax_Syntax.Tm_app uu____23178  in
                       FStar_Syntax_Syntax.mk uu____23177  in
                     uu____23170 FStar_Pervasives_Native.None uu____23169  in
                   FStar_Pervasives_Native.Some uu____23166)
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
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
      | uu____23350 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23365 =
        let uu____23366 = FStar_Syntax_Subst.compress t  in
        uu____23366.FStar_Syntax_Syntax.n  in
      match uu____23365 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23370,c) ->
          is_reifiable_comp env c
      | uu____23392 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23412 =
           let uu____23414 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23414  in
         if uu____23412
         then
           let uu____23417 =
             let uu____23423 =
               let uu____23425 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23425
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23423)  in
           let uu____23429 = get_range env  in
           FStar_Errors.raise_error uu____23417 uu____23429
         else ());
        (let uu____23432 = effect_repr_aux true env c u_c  in
         match uu____23432 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1668_23468 = env  in
        {
          solver = (uu___1668_23468.solver);
          range = (uu___1668_23468.range);
          curmodule = (uu___1668_23468.curmodule);
          gamma = (uu___1668_23468.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1668_23468.gamma_cache);
          modules = (uu___1668_23468.modules);
          expected_typ = (uu___1668_23468.expected_typ);
          sigtab = (uu___1668_23468.sigtab);
          attrtab = (uu___1668_23468.attrtab);
          is_pattern = (uu___1668_23468.is_pattern);
          instantiate_imp = (uu___1668_23468.instantiate_imp);
          effects = (uu___1668_23468.effects);
          generalize = (uu___1668_23468.generalize);
          letrecs = (uu___1668_23468.letrecs);
          top_level = (uu___1668_23468.top_level);
          check_uvars = (uu___1668_23468.check_uvars);
          use_eq = (uu___1668_23468.use_eq);
          is_iface = (uu___1668_23468.is_iface);
          admit = (uu___1668_23468.admit);
          lax = (uu___1668_23468.lax);
          lax_universes = (uu___1668_23468.lax_universes);
          phase1 = (uu___1668_23468.phase1);
          failhard = (uu___1668_23468.failhard);
          nosynth = (uu___1668_23468.nosynth);
          uvar_subtyping = (uu___1668_23468.uvar_subtyping);
          tc_term = (uu___1668_23468.tc_term);
          type_of = (uu___1668_23468.type_of);
          universe_of = (uu___1668_23468.universe_of);
          check_type_of = (uu___1668_23468.check_type_of);
          use_bv_sorts = (uu___1668_23468.use_bv_sorts);
          qtbl_name_and_index = (uu___1668_23468.qtbl_name_and_index);
          normalized_eff_names = (uu___1668_23468.normalized_eff_names);
          fv_delta_depths = (uu___1668_23468.fv_delta_depths);
          proof_ns = (uu___1668_23468.proof_ns);
          synth_hook = (uu___1668_23468.synth_hook);
          try_solve_implicits_hook =
            (uu___1668_23468.try_solve_implicits_hook);
          splice = (uu___1668_23468.splice);
          postprocess = (uu___1668_23468.postprocess);
          is_native_tactic = (uu___1668_23468.is_native_tactic);
          identifier_info = (uu___1668_23468.identifier_info);
          tc_hooks = (uu___1668_23468.tc_hooks);
          dsenv = (uu___1668_23468.dsenv);
          nbe = (uu___1668_23468.nbe);
          strict_args_tab = (uu___1668_23468.strict_args_tab);
          erasable_types_tab = (uu___1668_23468.erasable_types_tab)
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
    fun uu____23487  ->
      match uu____23487 with
      | (ed,quals) ->
          let effects =
            let uu___1677_23501 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1677_23501.order);
              joins = (uu___1677_23501.joins)
            }  in
          let uu___1680_23510 = env  in
          {
            solver = (uu___1680_23510.solver);
            range = (uu___1680_23510.range);
            curmodule = (uu___1680_23510.curmodule);
            gamma = (uu___1680_23510.gamma);
            gamma_sig = (uu___1680_23510.gamma_sig);
            gamma_cache = (uu___1680_23510.gamma_cache);
            modules = (uu___1680_23510.modules);
            expected_typ = (uu___1680_23510.expected_typ);
            sigtab = (uu___1680_23510.sigtab);
            attrtab = (uu___1680_23510.attrtab);
            is_pattern = (uu___1680_23510.is_pattern);
            instantiate_imp = (uu___1680_23510.instantiate_imp);
            effects;
            generalize = (uu___1680_23510.generalize);
            letrecs = (uu___1680_23510.letrecs);
            top_level = (uu___1680_23510.top_level);
            check_uvars = (uu___1680_23510.check_uvars);
            use_eq = (uu___1680_23510.use_eq);
            is_iface = (uu___1680_23510.is_iface);
            admit = (uu___1680_23510.admit);
            lax = (uu___1680_23510.lax);
            lax_universes = (uu___1680_23510.lax_universes);
            phase1 = (uu___1680_23510.phase1);
            failhard = (uu___1680_23510.failhard);
            nosynth = (uu___1680_23510.nosynth);
            uvar_subtyping = (uu___1680_23510.uvar_subtyping);
            tc_term = (uu___1680_23510.tc_term);
            type_of = (uu___1680_23510.type_of);
            universe_of = (uu___1680_23510.universe_of);
            check_type_of = (uu___1680_23510.check_type_of);
            use_bv_sorts = (uu___1680_23510.use_bv_sorts);
            qtbl_name_and_index = (uu___1680_23510.qtbl_name_and_index);
            normalized_eff_names = (uu___1680_23510.normalized_eff_names);
            fv_delta_depths = (uu___1680_23510.fv_delta_depths);
            proof_ns = (uu___1680_23510.proof_ns);
            synth_hook = (uu___1680_23510.synth_hook);
            try_solve_implicits_hook =
              (uu___1680_23510.try_solve_implicits_hook);
            splice = (uu___1680_23510.splice);
            postprocess = (uu___1680_23510.postprocess);
            is_native_tactic = (uu___1680_23510.is_native_tactic);
            identifier_info = (uu___1680_23510.identifier_info);
            tc_hooks = (uu___1680_23510.tc_hooks);
            dsenv = (uu___1680_23510.dsenv);
            nbe = (uu___1680_23510.nbe);
            strict_args_tab = (uu___1680_23510.strict_args_tab);
            erasable_types_tab = (uu___1680_23510.erasable_types_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____23550 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____23550  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____23708 = (e1.mlift).mlift_wp u t wp  in
                            let uu____23709 = l1 u t wp e  in
                            l2 u t uu____23708 uu____23709))
            | uu____23710 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____23782 = inst_tscheme_with lift_t [u]  in
        match uu____23782 with
        | (uu____23789,lift_t1) ->
            let uu____23791 =
              let uu____23798 =
                let uu____23799 =
                  let uu____23816 =
                    let uu____23827 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____23836 =
                      let uu____23847 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____23847]  in
                    uu____23827 :: uu____23836  in
                  (lift_t1, uu____23816)  in
                FStar_Syntax_Syntax.Tm_app uu____23799  in
              FStar_Syntax_Syntax.mk uu____23798  in
            uu____23791 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____23957 = inst_tscheme_with lift_t [u]  in
        match uu____23957 with
        | (uu____23964,lift_t1) ->
            let uu____23966 =
              let uu____23973 =
                let uu____23974 =
                  let uu____23991 =
                    let uu____24002 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____24011 =
                      let uu____24022 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____24031 =
                        let uu____24042 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____24042]  in
                      uu____24022 :: uu____24031  in
                    uu____24002 :: uu____24011  in
                  (lift_t1, uu____23991)  in
                FStar_Syntax_Syntax.Tm_app uu____23974  in
              FStar_Syntax_Syntax.mk uu____23973  in
            uu____23966 FStar_Pervasives_Native.None
              e.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_term =
        FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term  in
      let edge =
        {
          msource = (sub1.FStar_Syntax_Syntax.source);
          mtarget = (sub1.FStar_Syntax_Syntax.target);
          mlift = { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
        }  in
      let id_edge l =
        {
          msource = (sub1.FStar_Syntax_Syntax.source);
          mtarget = (sub1.FStar_Syntax_Syntax.target);
          mlift = identity_mlift
        }  in
      let print_mlift l =
        let bogus_term s =
          let uu____24144 =
            let uu____24145 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____24145
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____24144  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____24154 =
          let uu____24156 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____24156  in
        let uu____24157 =
          let uu____24159 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____24187 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____24187)
             in
          FStar_Util.dflt "none" uu____24159  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____24154 uu____24157
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____24216  ->
                match uu____24216 with
                | (e,uu____24224) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____24247 =
        match uu____24247 with
        | (i,j) ->
            let uu____24258 = FStar_Ident.lid_equals i j  in
            if uu____24258
            then
              FStar_All.pipe_right (id_edge i)
                (fun _24265  -> FStar_Pervasives_Native.Some _24265)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____24294 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____24304 = FStar_Ident.lid_equals i k  in
                    if uu____24304
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____24318 = FStar_Ident.lid_equals j k
                                 in
                              if uu____24318
                              then []
                              else
                                (let uu____24325 =
                                   let uu____24334 = find_edge order1 (i, k)
                                      in
                                   let uu____24337 = find_edge order1 (k, j)
                                      in
                                   (uu____24334, uu____24337)  in
                                 match uu____24325 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____24352 = compose_edges e1 e2
                                        in
                                     [uu____24352]
                                 | uu____24353 -> [])))))
             in
          FStar_List.append order1 uu____24294  in
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
              let uu____24383 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____24386 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____24386
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____24383
              then
                let uu____24393 =
                  let uu____24399 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____24399)
                   in
                let uu____24403 = get_range env  in
                FStar_Errors.raise_error uu____24393 uu____24403
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____24481 = FStar_Ident.lid_equals i j  in
                           if uu____24481
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____24533 =
                                         let uu____24542 =
                                           find_edge order2 (i, k)  in
                                         let uu____24545 =
                                           find_edge order2 (j, k)  in
                                         (uu____24542, uu____24545)  in
                                       match uu____24533 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____24587,uu____24588)
                                                ->
                                                let uu____24595 =
                                                  let uu____24602 =
                                                    let uu____24604 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____24604
                                                     in
                                                  let uu____24607 =
                                                    let uu____24609 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____24609
                                                     in
                                                  (uu____24602, uu____24607)
                                                   in
                                                (match uu____24595 with
                                                 | (true ,true ) ->
                                                     let uu____24626 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____24626
                                                     then
                                                       (FStar_Errors.log_issue
                                                          FStar_Range.dummyRange
                                                          (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                            "Looking multiple times at the same upper bound candidate");
                                                        bopt)
                                                     else
                                                       failwith
                                                         "Found a cycle in the lattice"
                                                 | (false ,false ) -> bopt
                                                 | (true ,false ) ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | (false ,true ) -> bopt))
                                       | uu____24669 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1807_24742 = env.effects  in
         { decls = (uu___1807_24742.decls); order = order2; joins }  in
       let uu___1810_24743 = env  in
       {
         solver = (uu___1810_24743.solver);
         range = (uu___1810_24743.range);
         curmodule = (uu___1810_24743.curmodule);
         gamma = (uu___1810_24743.gamma);
         gamma_sig = (uu___1810_24743.gamma_sig);
         gamma_cache = (uu___1810_24743.gamma_cache);
         modules = (uu___1810_24743.modules);
         expected_typ = (uu___1810_24743.expected_typ);
         sigtab = (uu___1810_24743.sigtab);
         attrtab = (uu___1810_24743.attrtab);
         is_pattern = (uu___1810_24743.is_pattern);
         instantiate_imp = (uu___1810_24743.instantiate_imp);
         effects;
         generalize = (uu___1810_24743.generalize);
         letrecs = (uu___1810_24743.letrecs);
         top_level = (uu___1810_24743.top_level);
         check_uvars = (uu___1810_24743.check_uvars);
         use_eq = (uu___1810_24743.use_eq);
         is_iface = (uu___1810_24743.is_iface);
         admit = (uu___1810_24743.admit);
         lax = (uu___1810_24743.lax);
         lax_universes = (uu___1810_24743.lax_universes);
         phase1 = (uu___1810_24743.phase1);
         failhard = (uu___1810_24743.failhard);
         nosynth = (uu___1810_24743.nosynth);
         uvar_subtyping = (uu___1810_24743.uvar_subtyping);
         tc_term = (uu___1810_24743.tc_term);
         type_of = (uu___1810_24743.type_of);
         universe_of = (uu___1810_24743.universe_of);
         check_type_of = (uu___1810_24743.check_type_of);
         use_bv_sorts = (uu___1810_24743.use_bv_sorts);
         qtbl_name_and_index = (uu___1810_24743.qtbl_name_and_index);
         normalized_eff_names = (uu___1810_24743.normalized_eff_names);
         fv_delta_depths = (uu___1810_24743.fv_delta_depths);
         proof_ns = (uu___1810_24743.proof_ns);
         synth_hook = (uu___1810_24743.synth_hook);
         try_solve_implicits_hook =
           (uu___1810_24743.try_solve_implicits_hook);
         splice = (uu___1810_24743.splice);
         postprocess = (uu___1810_24743.postprocess);
         is_native_tactic = (uu___1810_24743.is_native_tactic);
         identifier_info = (uu___1810_24743.identifier_info);
         tc_hooks = (uu___1810_24743.tc_hooks);
         dsenv = (uu___1810_24743.dsenv);
         nbe = (uu___1810_24743.nbe);
         strict_args_tab = (uu___1810_24743.strict_args_tab);
         erasable_types_tab = (uu___1810_24743.erasable_types_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1814_24755 = env  in
      {
        solver = (uu___1814_24755.solver);
        range = (uu___1814_24755.range);
        curmodule = (uu___1814_24755.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1814_24755.gamma_sig);
        gamma_cache = (uu___1814_24755.gamma_cache);
        modules = (uu___1814_24755.modules);
        expected_typ = (uu___1814_24755.expected_typ);
        sigtab = (uu___1814_24755.sigtab);
        attrtab = (uu___1814_24755.attrtab);
        is_pattern = (uu___1814_24755.is_pattern);
        instantiate_imp = (uu___1814_24755.instantiate_imp);
        effects = (uu___1814_24755.effects);
        generalize = (uu___1814_24755.generalize);
        letrecs = (uu___1814_24755.letrecs);
        top_level = (uu___1814_24755.top_level);
        check_uvars = (uu___1814_24755.check_uvars);
        use_eq = (uu___1814_24755.use_eq);
        is_iface = (uu___1814_24755.is_iface);
        admit = (uu___1814_24755.admit);
        lax = (uu___1814_24755.lax);
        lax_universes = (uu___1814_24755.lax_universes);
        phase1 = (uu___1814_24755.phase1);
        failhard = (uu___1814_24755.failhard);
        nosynth = (uu___1814_24755.nosynth);
        uvar_subtyping = (uu___1814_24755.uvar_subtyping);
        tc_term = (uu___1814_24755.tc_term);
        type_of = (uu___1814_24755.type_of);
        universe_of = (uu___1814_24755.universe_of);
        check_type_of = (uu___1814_24755.check_type_of);
        use_bv_sorts = (uu___1814_24755.use_bv_sorts);
        qtbl_name_and_index = (uu___1814_24755.qtbl_name_and_index);
        normalized_eff_names = (uu___1814_24755.normalized_eff_names);
        fv_delta_depths = (uu___1814_24755.fv_delta_depths);
        proof_ns = (uu___1814_24755.proof_ns);
        synth_hook = (uu___1814_24755.synth_hook);
        try_solve_implicits_hook = (uu___1814_24755.try_solve_implicits_hook);
        splice = (uu___1814_24755.splice);
        postprocess = (uu___1814_24755.postprocess);
        is_native_tactic = (uu___1814_24755.is_native_tactic);
        identifier_info = (uu___1814_24755.identifier_info);
        tc_hooks = (uu___1814_24755.tc_hooks);
        dsenv = (uu___1814_24755.dsenv);
        nbe = (uu___1814_24755.nbe);
        strict_args_tab = (uu___1814_24755.strict_args_tab);
        erasable_types_tab = (uu___1814_24755.erasable_types_tab)
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
            (let uu___1827_24813 = env  in
             {
               solver = (uu___1827_24813.solver);
               range = (uu___1827_24813.range);
               curmodule = (uu___1827_24813.curmodule);
               gamma = rest;
               gamma_sig = (uu___1827_24813.gamma_sig);
               gamma_cache = (uu___1827_24813.gamma_cache);
               modules = (uu___1827_24813.modules);
               expected_typ = (uu___1827_24813.expected_typ);
               sigtab = (uu___1827_24813.sigtab);
               attrtab = (uu___1827_24813.attrtab);
               is_pattern = (uu___1827_24813.is_pattern);
               instantiate_imp = (uu___1827_24813.instantiate_imp);
               effects = (uu___1827_24813.effects);
               generalize = (uu___1827_24813.generalize);
               letrecs = (uu___1827_24813.letrecs);
               top_level = (uu___1827_24813.top_level);
               check_uvars = (uu___1827_24813.check_uvars);
               use_eq = (uu___1827_24813.use_eq);
               is_iface = (uu___1827_24813.is_iface);
               admit = (uu___1827_24813.admit);
               lax = (uu___1827_24813.lax);
               lax_universes = (uu___1827_24813.lax_universes);
               phase1 = (uu___1827_24813.phase1);
               failhard = (uu___1827_24813.failhard);
               nosynth = (uu___1827_24813.nosynth);
               uvar_subtyping = (uu___1827_24813.uvar_subtyping);
               tc_term = (uu___1827_24813.tc_term);
               type_of = (uu___1827_24813.type_of);
               universe_of = (uu___1827_24813.universe_of);
               check_type_of = (uu___1827_24813.check_type_of);
               use_bv_sorts = (uu___1827_24813.use_bv_sorts);
               qtbl_name_and_index = (uu___1827_24813.qtbl_name_and_index);
               normalized_eff_names = (uu___1827_24813.normalized_eff_names);
               fv_delta_depths = (uu___1827_24813.fv_delta_depths);
               proof_ns = (uu___1827_24813.proof_ns);
               synth_hook = (uu___1827_24813.synth_hook);
               try_solve_implicits_hook =
                 (uu___1827_24813.try_solve_implicits_hook);
               splice = (uu___1827_24813.splice);
               postprocess = (uu___1827_24813.postprocess);
               is_native_tactic = (uu___1827_24813.is_native_tactic);
               identifier_info = (uu___1827_24813.identifier_info);
               tc_hooks = (uu___1827_24813.tc_hooks);
               dsenv = (uu___1827_24813.dsenv);
               nbe = (uu___1827_24813.nbe);
               strict_args_tab = (uu___1827_24813.strict_args_tab);
               erasable_types_tab = (uu___1827_24813.erasable_types_tab)
             }))
    | uu____24814 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24843  ->
             match uu____24843 with | (x,uu____24851) -> push_bv env1 x) env
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
            let uu___1841_24886 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1841_24886.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1841_24886.FStar_Syntax_Syntax.index);
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
        let uu____24959 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24959 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24987 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24987)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1862_25003 = env  in
      {
        solver = (uu___1862_25003.solver);
        range = (uu___1862_25003.range);
        curmodule = (uu___1862_25003.curmodule);
        gamma = (uu___1862_25003.gamma);
        gamma_sig = (uu___1862_25003.gamma_sig);
        gamma_cache = (uu___1862_25003.gamma_cache);
        modules = (uu___1862_25003.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1862_25003.sigtab);
        attrtab = (uu___1862_25003.attrtab);
        is_pattern = (uu___1862_25003.is_pattern);
        instantiate_imp = (uu___1862_25003.instantiate_imp);
        effects = (uu___1862_25003.effects);
        generalize = (uu___1862_25003.generalize);
        letrecs = (uu___1862_25003.letrecs);
        top_level = (uu___1862_25003.top_level);
        check_uvars = (uu___1862_25003.check_uvars);
        use_eq = false;
        is_iface = (uu___1862_25003.is_iface);
        admit = (uu___1862_25003.admit);
        lax = (uu___1862_25003.lax);
        lax_universes = (uu___1862_25003.lax_universes);
        phase1 = (uu___1862_25003.phase1);
        failhard = (uu___1862_25003.failhard);
        nosynth = (uu___1862_25003.nosynth);
        uvar_subtyping = (uu___1862_25003.uvar_subtyping);
        tc_term = (uu___1862_25003.tc_term);
        type_of = (uu___1862_25003.type_of);
        universe_of = (uu___1862_25003.universe_of);
        check_type_of = (uu___1862_25003.check_type_of);
        use_bv_sorts = (uu___1862_25003.use_bv_sorts);
        qtbl_name_and_index = (uu___1862_25003.qtbl_name_and_index);
        normalized_eff_names = (uu___1862_25003.normalized_eff_names);
        fv_delta_depths = (uu___1862_25003.fv_delta_depths);
        proof_ns = (uu___1862_25003.proof_ns);
        synth_hook = (uu___1862_25003.synth_hook);
        try_solve_implicits_hook = (uu___1862_25003.try_solve_implicits_hook);
        splice = (uu___1862_25003.splice);
        postprocess = (uu___1862_25003.postprocess);
        is_native_tactic = (uu___1862_25003.is_native_tactic);
        identifier_info = (uu___1862_25003.identifier_info);
        tc_hooks = (uu___1862_25003.tc_hooks);
        dsenv = (uu___1862_25003.dsenv);
        nbe = (uu___1862_25003.nbe);
        strict_args_tab = (uu___1862_25003.strict_args_tab);
        erasable_types_tab = (uu___1862_25003.erasable_types_tab)
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
    let uu____25034 = expected_typ env_  in
    ((let uu___1869_25040 = env_  in
      {
        solver = (uu___1869_25040.solver);
        range = (uu___1869_25040.range);
        curmodule = (uu___1869_25040.curmodule);
        gamma = (uu___1869_25040.gamma);
        gamma_sig = (uu___1869_25040.gamma_sig);
        gamma_cache = (uu___1869_25040.gamma_cache);
        modules = (uu___1869_25040.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1869_25040.sigtab);
        attrtab = (uu___1869_25040.attrtab);
        is_pattern = (uu___1869_25040.is_pattern);
        instantiate_imp = (uu___1869_25040.instantiate_imp);
        effects = (uu___1869_25040.effects);
        generalize = (uu___1869_25040.generalize);
        letrecs = (uu___1869_25040.letrecs);
        top_level = (uu___1869_25040.top_level);
        check_uvars = (uu___1869_25040.check_uvars);
        use_eq = false;
        is_iface = (uu___1869_25040.is_iface);
        admit = (uu___1869_25040.admit);
        lax = (uu___1869_25040.lax);
        lax_universes = (uu___1869_25040.lax_universes);
        phase1 = (uu___1869_25040.phase1);
        failhard = (uu___1869_25040.failhard);
        nosynth = (uu___1869_25040.nosynth);
        uvar_subtyping = (uu___1869_25040.uvar_subtyping);
        tc_term = (uu___1869_25040.tc_term);
        type_of = (uu___1869_25040.type_of);
        universe_of = (uu___1869_25040.universe_of);
        check_type_of = (uu___1869_25040.check_type_of);
        use_bv_sorts = (uu___1869_25040.use_bv_sorts);
        qtbl_name_and_index = (uu___1869_25040.qtbl_name_and_index);
        normalized_eff_names = (uu___1869_25040.normalized_eff_names);
        fv_delta_depths = (uu___1869_25040.fv_delta_depths);
        proof_ns = (uu___1869_25040.proof_ns);
        synth_hook = (uu___1869_25040.synth_hook);
        try_solve_implicits_hook = (uu___1869_25040.try_solve_implicits_hook);
        splice = (uu___1869_25040.splice);
        postprocess = (uu___1869_25040.postprocess);
        is_native_tactic = (uu___1869_25040.is_native_tactic);
        identifier_info = (uu___1869_25040.identifier_info);
        tc_hooks = (uu___1869_25040.tc_hooks);
        dsenv = (uu___1869_25040.dsenv);
        nbe = (uu___1869_25040.nbe);
        strict_args_tab = (uu___1869_25040.strict_args_tab);
        erasable_types_tab = (uu___1869_25040.erasable_types_tab)
      }), uu____25034)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25052 =
      let uu____25055 = FStar_Ident.id_of_text ""  in [uu____25055]  in
    FStar_Ident.lid_of_ids uu____25052  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____25062 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25062
        then
          let uu____25067 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25067 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1877_25095 = env  in
       {
         solver = (uu___1877_25095.solver);
         range = (uu___1877_25095.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1877_25095.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1877_25095.expected_typ);
         sigtab = (uu___1877_25095.sigtab);
         attrtab = (uu___1877_25095.attrtab);
         is_pattern = (uu___1877_25095.is_pattern);
         instantiate_imp = (uu___1877_25095.instantiate_imp);
         effects = (uu___1877_25095.effects);
         generalize = (uu___1877_25095.generalize);
         letrecs = (uu___1877_25095.letrecs);
         top_level = (uu___1877_25095.top_level);
         check_uvars = (uu___1877_25095.check_uvars);
         use_eq = (uu___1877_25095.use_eq);
         is_iface = (uu___1877_25095.is_iface);
         admit = (uu___1877_25095.admit);
         lax = (uu___1877_25095.lax);
         lax_universes = (uu___1877_25095.lax_universes);
         phase1 = (uu___1877_25095.phase1);
         failhard = (uu___1877_25095.failhard);
         nosynth = (uu___1877_25095.nosynth);
         uvar_subtyping = (uu___1877_25095.uvar_subtyping);
         tc_term = (uu___1877_25095.tc_term);
         type_of = (uu___1877_25095.type_of);
         universe_of = (uu___1877_25095.universe_of);
         check_type_of = (uu___1877_25095.check_type_of);
         use_bv_sorts = (uu___1877_25095.use_bv_sorts);
         qtbl_name_and_index = (uu___1877_25095.qtbl_name_and_index);
         normalized_eff_names = (uu___1877_25095.normalized_eff_names);
         fv_delta_depths = (uu___1877_25095.fv_delta_depths);
         proof_ns = (uu___1877_25095.proof_ns);
         synth_hook = (uu___1877_25095.synth_hook);
         try_solve_implicits_hook =
           (uu___1877_25095.try_solve_implicits_hook);
         splice = (uu___1877_25095.splice);
         postprocess = (uu___1877_25095.postprocess);
         is_native_tactic = (uu___1877_25095.is_native_tactic);
         identifier_info = (uu___1877_25095.identifier_info);
         tc_hooks = (uu___1877_25095.tc_hooks);
         dsenv = (uu___1877_25095.dsenv);
         nbe = (uu___1877_25095.nbe);
         strict_args_tab = (uu___1877_25095.strict_args_tab);
         erasable_types_tab = (uu___1877_25095.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25147)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25151,(uu____25152,t)))::tl1
          ->
          let uu____25173 =
            let uu____25176 = FStar_Syntax_Free.uvars t  in
            ext out uu____25176  in
          aux uu____25173 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25179;
            FStar_Syntax_Syntax.index = uu____25180;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25188 =
            let uu____25191 = FStar_Syntax_Free.uvars t  in
            ext out uu____25191  in
          aux uu____25188 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25249)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25253,(uu____25254,t)))::tl1
          ->
          let uu____25275 =
            let uu____25278 = FStar_Syntax_Free.univs t  in
            ext out uu____25278  in
          aux uu____25275 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25281;
            FStar_Syntax_Syntax.index = uu____25282;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25290 =
            let uu____25293 = FStar_Syntax_Free.univs t  in
            ext out uu____25293  in
          aux uu____25290 tl1
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
          let uu____25355 = FStar_Util.set_add uname out  in
          aux uu____25355 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25358,(uu____25359,t)))::tl1
          ->
          let uu____25380 =
            let uu____25383 = FStar_Syntax_Free.univnames t  in
            ext out uu____25383  in
          aux uu____25380 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25386;
            FStar_Syntax_Syntax.index = uu____25387;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25395 =
            let uu____25398 = FStar_Syntax_Free.univnames t  in
            ext out uu____25398  in
          aux uu____25395 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_25419  ->
            match uu___11_25419 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____25423 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____25436 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____25447 =
      let uu____25456 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____25456
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____25447 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____25504 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_25517  ->
              match uu___12_25517 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____25520 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____25520
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____25526) ->
                  let uu____25543 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____25543))
       in
    FStar_All.pipe_right uu____25504 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_25557  ->
    match uu___13_25557 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____25563 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____25563
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____25586  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____25641) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25674,uu____25675) -> false  in
      let uu____25689 =
        FStar_List.tryFind
          (fun uu____25711  ->
             match uu____25711 with | (p,uu____25722) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25689 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25741,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25771 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25771
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2020_25793 = e  in
        {
          solver = (uu___2020_25793.solver);
          range = (uu___2020_25793.range);
          curmodule = (uu___2020_25793.curmodule);
          gamma = (uu___2020_25793.gamma);
          gamma_sig = (uu___2020_25793.gamma_sig);
          gamma_cache = (uu___2020_25793.gamma_cache);
          modules = (uu___2020_25793.modules);
          expected_typ = (uu___2020_25793.expected_typ);
          sigtab = (uu___2020_25793.sigtab);
          attrtab = (uu___2020_25793.attrtab);
          is_pattern = (uu___2020_25793.is_pattern);
          instantiate_imp = (uu___2020_25793.instantiate_imp);
          effects = (uu___2020_25793.effects);
          generalize = (uu___2020_25793.generalize);
          letrecs = (uu___2020_25793.letrecs);
          top_level = (uu___2020_25793.top_level);
          check_uvars = (uu___2020_25793.check_uvars);
          use_eq = (uu___2020_25793.use_eq);
          is_iface = (uu___2020_25793.is_iface);
          admit = (uu___2020_25793.admit);
          lax = (uu___2020_25793.lax);
          lax_universes = (uu___2020_25793.lax_universes);
          phase1 = (uu___2020_25793.phase1);
          failhard = (uu___2020_25793.failhard);
          nosynth = (uu___2020_25793.nosynth);
          uvar_subtyping = (uu___2020_25793.uvar_subtyping);
          tc_term = (uu___2020_25793.tc_term);
          type_of = (uu___2020_25793.type_of);
          universe_of = (uu___2020_25793.universe_of);
          check_type_of = (uu___2020_25793.check_type_of);
          use_bv_sorts = (uu___2020_25793.use_bv_sorts);
          qtbl_name_and_index = (uu___2020_25793.qtbl_name_and_index);
          normalized_eff_names = (uu___2020_25793.normalized_eff_names);
          fv_delta_depths = (uu___2020_25793.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2020_25793.synth_hook);
          try_solve_implicits_hook =
            (uu___2020_25793.try_solve_implicits_hook);
          splice = (uu___2020_25793.splice);
          postprocess = (uu___2020_25793.postprocess);
          is_native_tactic = (uu___2020_25793.is_native_tactic);
          identifier_info = (uu___2020_25793.identifier_info);
          tc_hooks = (uu___2020_25793.tc_hooks);
          dsenv = (uu___2020_25793.dsenv);
          nbe = (uu___2020_25793.nbe);
          strict_args_tab = (uu___2020_25793.strict_args_tab);
          erasable_types_tab = (uu___2020_25793.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2029_25841 = e  in
      {
        solver = (uu___2029_25841.solver);
        range = (uu___2029_25841.range);
        curmodule = (uu___2029_25841.curmodule);
        gamma = (uu___2029_25841.gamma);
        gamma_sig = (uu___2029_25841.gamma_sig);
        gamma_cache = (uu___2029_25841.gamma_cache);
        modules = (uu___2029_25841.modules);
        expected_typ = (uu___2029_25841.expected_typ);
        sigtab = (uu___2029_25841.sigtab);
        attrtab = (uu___2029_25841.attrtab);
        is_pattern = (uu___2029_25841.is_pattern);
        instantiate_imp = (uu___2029_25841.instantiate_imp);
        effects = (uu___2029_25841.effects);
        generalize = (uu___2029_25841.generalize);
        letrecs = (uu___2029_25841.letrecs);
        top_level = (uu___2029_25841.top_level);
        check_uvars = (uu___2029_25841.check_uvars);
        use_eq = (uu___2029_25841.use_eq);
        is_iface = (uu___2029_25841.is_iface);
        admit = (uu___2029_25841.admit);
        lax = (uu___2029_25841.lax);
        lax_universes = (uu___2029_25841.lax_universes);
        phase1 = (uu___2029_25841.phase1);
        failhard = (uu___2029_25841.failhard);
        nosynth = (uu___2029_25841.nosynth);
        uvar_subtyping = (uu___2029_25841.uvar_subtyping);
        tc_term = (uu___2029_25841.tc_term);
        type_of = (uu___2029_25841.type_of);
        universe_of = (uu___2029_25841.universe_of);
        check_type_of = (uu___2029_25841.check_type_of);
        use_bv_sorts = (uu___2029_25841.use_bv_sorts);
        qtbl_name_and_index = (uu___2029_25841.qtbl_name_and_index);
        normalized_eff_names = (uu___2029_25841.normalized_eff_names);
        fv_delta_depths = (uu___2029_25841.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2029_25841.synth_hook);
        try_solve_implicits_hook = (uu___2029_25841.try_solve_implicits_hook);
        splice = (uu___2029_25841.splice);
        postprocess = (uu___2029_25841.postprocess);
        is_native_tactic = (uu___2029_25841.is_native_tactic);
        identifier_info = (uu___2029_25841.identifier_info);
        tc_hooks = (uu___2029_25841.tc_hooks);
        dsenv = (uu___2029_25841.dsenv);
        nbe = (uu___2029_25841.nbe);
        strict_args_tab = (uu___2029_25841.strict_args_tab);
        erasable_types_tab = (uu___2029_25841.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25857 = FStar_Syntax_Free.names t  in
      let uu____25860 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25857 uu____25860
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25883 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25883
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25893 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25893
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25914 =
      match uu____25914 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25934 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25934)
       in
    let uu____25942 =
      let uu____25946 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25946 FStar_List.rev  in
    FStar_All.pipe_right uu____25942 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = [];
        univ_ineqs = ([],[]); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____26016 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26016 with
                   | FStar_Pervasives_Native.Some uu____26020 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26023 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____26033;
        univ_ineqs = uu____26034; implicits = uu____26035;_} -> true
    | uu____26047 -> false
  
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___2073_26078 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2073_26078.deferred);
            univ_ineqs = (uu___2073_26078.univ_ineqs);
            implicits = (uu___2073_26078.implicits)
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
          let uu____26117 = FStar_Options.defensive ()  in
          if uu____26117
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26123 =
              let uu____26125 =
                let uu____26127 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26127  in
              Prims.op_Negation uu____26125  in
            (if uu____26123
             then
               let uu____26134 =
                 let uu____26140 =
                   let uu____26142 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26144 =
                     let uu____26146 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26146
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26142 uu____26144
                    in
                 (FStar_Errors.Warning_Defensive, uu____26140)  in
               FStar_Errors.log_issue rng uu____26134
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
          let uu____26186 =
            let uu____26188 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26188  in
          if uu____26186
          then ()
          else
            (let uu____26193 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26193 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26219 =
            let uu____26221 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26221  in
          if uu____26219
          then ()
          else
            (let uu____26226 = bound_vars e  in
             def_check_closed_in rng msg uu____26226 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2110_26265 = g  in
          let uu____26266 =
            let uu____26267 =
              let uu____26268 =
                let uu____26275 =
                  let uu____26276 =
                    let uu____26293 =
                      let uu____26304 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____26304]  in
                    (f, uu____26293)  in
                  FStar_Syntax_Syntax.Tm_app uu____26276  in
                FStar_Syntax_Syntax.mk uu____26275  in
              uu____26268 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _26341  -> FStar_TypeChecker_Common.NonTrivial _26341)
              uu____26267
             in
          {
            guard_f = uu____26266;
            deferred = (uu___2110_26265.deferred);
            univ_ineqs = (uu___2110_26265.univ_ineqs);
            implicits = (uu___2110_26265.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2117_26359 = g  in
          let uu____26360 =
            let uu____26361 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26361  in
          {
            guard_f = uu____26360;
            deferred = (uu___2117_26359.deferred);
            univ_ineqs = (uu___2117_26359.univ_ineqs);
            implicits = (uu___2117_26359.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2122_26378 = g  in
          let uu____26379 =
            let uu____26380 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____26380  in
          {
            guard_f = uu____26379;
            deferred = (uu___2122_26378.deferred);
            univ_ineqs = (uu___2122_26378.univ_ineqs);
            implicits = (uu___2122_26378.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2126_26382 = g  in
          let uu____26383 =
            let uu____26384 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26384  in
          {
            guard_f = uu____26383;
            deferred = (uu___2126_26382.deferred);
            univ_ineqs = (uu___2126_26382.univ_ineqs);
            implicits = (uu___2126_26382.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____26391 ->
        failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____26408 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____26408
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____26415 =
      let uu____26416 = FStar_Syntax_Util.unmeta t  in
      uu____26416.FStar_Syntax_Syntax.n  in
    match uu____26415 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____26420 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____26463 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____26463;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_List.fold_left conj_guard trivial_guard gs 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____26558 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____26558
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2181_26565 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2181_26565.deferred);
              univ_ineqs = (uu___2181_26565.univ_ineqs);
              implicits = (uu___2181_26565.implicits)
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
               let uu____26599 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____26599
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
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2196_26626 = g  in
            let uu____26627 =
              let uu____26628 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____26628  in
            {
              guard_f = uu____26627;
              deferred = (uu___2196_26626.deferred);
              univ_ineqs = (uu___2196_26626.univ_ineqs);
              implicits = (uu___2196_26626.implicits)
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
              let uu____26686 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26686 with
              | FStar_Pervasives_Native.Some
                  (uu____26711::(tm,uu____26713)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26777 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26795 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26795;
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
                        imp_reason = reason;
                        imp_uvar = ctx_uvar;
                        imp_tm = t;
                        imp_range = r
                      }  in
                    let g =
                      let uu___2218_26827 = trivial_guard  in
                      {
                        guard_f = (uu___2218_26827.guard_f);
                        deferred = (uu___2218_26827.deferred);
                        univ_ineqs = (uu___2218_26827.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26845  -> ());
    push = (fun uu____26847  -> ());
    pop = (fun uu____26850  -> ());
    snapshot =
      (fun uu____26853  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26872  -> fun uu____26873  -> ());
    encode_sig = (fun uu____26888  -> fun uu____26889  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26895 =
             let uu____26902 = FStar_Options.peek ()  in (e, g, uu____26902)
              in
           [uu____26895]);
    solve = (fun uu____26918  -> fun uu____26919  -> fun uu____26920  -> ());
    finish = (fun uu____26927  -> ());
    refresh = (fun uu____26929  -> ())
  } 