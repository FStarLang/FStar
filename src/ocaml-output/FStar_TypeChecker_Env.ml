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
  fun projectee  -> match projectee with | Beta  -> true | uu____111 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____122 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____133 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____145 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____163 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____174 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____185 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____196 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____207 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____218 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____230 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____251 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____278 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____305 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____329 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____340 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____351 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____362 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____373 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____384 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____395 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____406 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____417 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____428 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____439 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____450 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____461 -> false
  
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
      | uu____521 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____547 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____558 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____569 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____581 -> false
  
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
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap }
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
        strict_args_tab;_} -> solver
  
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
        strict_args_tab;_} -> range
  
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
        strict_args_tab;_} -> curmodule
  
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
        strict_args_tab;_} -> gamma
  
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
        strict_args_tab;_} -> gamma_sig
  
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
        strict_args_tab;_} -> gamma_cache
  
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
        strict_args_tab;_} -> modules
  
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
        strict_args_tab;_} -> expected_typ
  
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
        strict_args_tab;_} -> sigtab
  
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
        strict_args_tab;_} -> attrtab
  
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
        strict_args_tab;_} -> is_pattern
  
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
        strict_args_tab;_} -> instantiate_imp
  
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
        strict_args_tab;_} -> effects
  
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
        strict_args_tab;_} -> generalize
  
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
        strict_args_tab;_} -> letrecs
  
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
        strict_args_tab;_} -> top_level
  
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
        strict_args_tab;_} -> check_uvars
  
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
        strict_args_tab;_} -> use_eq
  
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
        strict_args_tab;_} -> is_iface
  
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
        strict_args_tab;_} -> admit1
  
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
        strict_args_tab;_} -> lax1
  
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
        strict_args_tab;_} -> lax_universes
  
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
        strict_args_tab;_} -> phase1
  
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
        strict_args_tab;_} -> failhard
  
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
        strict_args_tab;_} -> nosynth
  
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
        strict_args_tab;_} -> uvar_subtyping
  
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
        strict_args_tab;_} -> tc_term
  
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
        strict_args_tab;_} -> type_of
  
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
        strict_args_tab;_} -> universe_of
  
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
        strict_args_tab;_} -> check_type_of
  
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
        strict_args_tab;_} -> use_bv_sorts
  
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
        strict_args_tab;_} -> qtbl_name_and_index
  
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
        strict_args_tab;_} -> normalized_eff_names
  
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
        strict_args_tab;_} -> fv_delta_depths
  
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
        strict_args_tab;_} -> proof_ns
  
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
        strict_args_tab;_} -> synth_hook
  
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
        strict_args_tab;_} -> try_solve_implicits_hook
  
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
        strict_args_tab;_} -> splice1
  
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
        strict_args_tab;_} -> postprocess
  
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
        strict_args_tab;_} -> is_native_tactic
  
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
        strict_args_tab;_} -> identifier_info
  
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
        strict_args_tab;_} -> tc_hooks
  
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
        strict_args_tab;_} -> dsenv
  
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
        strict_args_tab;_} -> nbe1
  
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
        strict_args_tab;_} -> strict_args_tab
  
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
           (fun uu___0_13161  ->
              match uu___0_13161 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13164 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13164  in
                  let uu____13165 =
                    let uu____13166 = FStar_Syntax_Subst.compress y  in
                    uu____13166.FStar_Syntax_Syntax.n  in
                  (match uu____13165 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13170 =
                         let uu___335_13171 = y1  in
                         let uu____13172 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___335_13171.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___335_13171.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13172
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13170
                   | uu____13175 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___341_13189 = env  in
      let uu____13190 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___341_13189.solver);
        range = (uu___341_13189.range);
        curmodule = (uu___341_13189.curmodule);
        gamma = uu____13190;
        gamma_sig = (uu___341_13189.gamma_sig);
        gamma_cache = (uu___341_13189.gamma_cache);
        modules = (uu___341_13189.modules);
        expected_typ = (uu___341_13189.expected_typ);
        sigtab = (uu___341_13189.sigtab);
        attrtab = (uu___341_13189.attrtab);
        is_pattern = (uu___341_13189.is_pattern);
        instantiate_imp = (uu___341_13189.instantiate_imp);
        effects = (uu___341_13189.effects);
        generalize = (uu___341_13189.generalize);
        letrecs = (uu___341_13189.letrecs);
        top_level = (uu___341_13189.top_level);
        check_uvars = (uu___341_13189.check_uvars);
        use_eq = (uu___341_13189.use_eq);
        is_iface = (uu___341_13189.is_iface);
        admit = (uu___341_13189.admit);
        lax = (uu___341_13189.lax);
        lax_universes = (uu___341_13189.lax_universes);
        phase1 = (uu___341_13189.phase1);
        failhard = (uu___341_13189.failhard);
        nosynth = (uu___341_13189.nosynth);
        uvar_subtyping = (uu___341_13189.uvar_subtyping);
        tc_term = (uu___341_13189.tc_term);
        type_of = (uu___341_13189.type_of);
        universe_of = (uu___341_13189.universe_of);
        check_type_of = (uu___341_13189.check_type_of);
        use_bv_sorts = (uu___341_13189.use_bv_sorts);
        qtbl_name_and_index = (uu___341_13189.qtbl_name_and_index);
        normalized_eff_names = (uu___341_13189.normalized_eff_names);
        fv_delta_depths = (uu___341_13189.fv_delta_depths);
        proof_ns = (uu___341_13189.proof_ns);
        synth_hook = (uu___341_13189.synth_hook);
        try_solve_implicits_hook = (uu___341_13189.try_solve_implicits_hook);
        splice = (uu___341_13189.splice);
        postprocess = (uu___341_13189.postprocess);
        is_native_tactic = (uu___341_13189.is_native_tactic);
        identifier_info = (uu___341_13189.identifier_info);
        tc_hooks = (uu___341_13189.tc_hooks);
        dsenv = (uu___341_13189.dsenv);
        nbe = (uu___341_13189.nbe);
        strict_args_tab = (uu___341_13189.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13198  -> fun uu____13199  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___348_13221 = env  in
      {
        solver = (uu___348_13221.solver);
        range = (uu___348_13221.range);
        curmodule = (uu___348_13221.curmodule);
        gamma = (uu___348_13221.gamma);
        gamma_sig = (uu___348_13221.gamma_sig);
        gamma_cache = (uu___348_13221.gamma_cache);
        modules = (uu___348_13221.modules);
        expected_typ = (uu___348_13221.expected_typ);
        sigtab = (uu___348_13221.sigtab);
        attrtab = (uu___348_13221.attrtab);
        is_pattern = (uu___348_13221.is_pattern);
        instantiate_imp = (uu___348_13221.instantiate_imp);
        effects = (uu___348_13221.effects);
        generalize = (uu___348_13221.generalize);
        letrecs = (uu___348_13221.letrecs);
        top_level = (uu___348_13221.top_level);
        check_uvars = (uu___348_13221.check_uvars);
        use_eq = (uu___348_13221.use_eq);
        is_iface = (uu___348_13221.is_iface);
        admit = (uu___348_13221.admit);
        lax = (uu___348_13221.lax);
        lax_universes = (uu___348_13221.lax_universes);
        phase1 = (uu___348_13221.phase1);
        failhard = (uu___348_13221.failhard);
        nosynth = (uu___348_13221.nosynth);
        uvar_subtyping = (uu___348_13221.uvar_subtyping);
        tc_term = (uu___348_13221.tc_term);
        type_of = (uu___348_13221.type_of);
        universe_of = (uu___348_13221.universe_of);
        check_type_of = (uu___348_13221.check_type_of);
        use_bv_sorts = (uu___348_13221.use_bv_sorts);
        qtbl_name_and_index = (uu___348_13221.qtbl_name_and_index);
        normalized_eff_names = (uu___348_13221.normalized_eff_names);
        fv_delta_depths = (uu___348_13221.fv_delta_depths);
        proof_ns = (uu___348_13221.proof_ns);
        synth_hook = (uu___348_13221.synth_hook);
        try_solve_implicits_hook = (uu___348_13221.try_solve_implicits_hook);
        splice = (uu___348_13221.splice);
        postprocess = (uu___348_13221.postprocess);
        is_native_tactic = (uu___348_13221.is_native_tactic);
        identifier_info = (uu___348_13221.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___348_13221.dsenv);
        nbe = (uu___348_13221.nbe);
        strict_args_tab = (uu___348_13221.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___352_13233 = e  in
      let uu____13234 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___352_13233.solver);
        range = (uu___352_13233.range);
        curmodule = (uu___352_13233.curmodule);
        gamma = (uu___352_13233.gamma);
        gamma_sig = (uu___352_13233.gamma_sig);
        gamma_cache = (uu___352_13233.gamma_cache);
        modules = (uu___352_13233.modules);
        expected_typ = (uu___352_13233.expected_typ);
        sigtab = (uu___352_13233.sigtab);
        attrtab = (uu___352_13233.attrtab);
        is_pattern = (uu___352_13233.is_pattern);
        instantiate_imp = (uu___352_13233.instantiate_imp);
        effects = (uu___352_13233.effects);
        generalize = (uu___352_13233.generalize);
        letrecs = (uu___352_13233.letrecs);
        top_level = (uu___352_13233.top_level);
        check_uvars = (uu___352_13233.check_uvars);
        use_eq = (uu___352_13233.use_eq);
        is_iface = (uu___352_13233.is_iface);
        admit = (uu___352_13233.admit);
        lax = (uu___352_13233.lax);
        lax_universes = (uu___352_13233.lax_universes);
        phase1 = (uu___352_13233.phase1);
        failhard = (uu___352_13233.failhard);
        nosynth = (uu___352_13233.nosynth);
        uvar_subtyping = (uu___352_13233.uvar_subtyping);
        tc_term = (uu___352_13233.tc_term);
        type_of = (uu___352_13233.type_of);
        universe_of = (uu___352_13233.universe_of);
        check_type_of = (uu___352_13233.check_type_of);
        use_bv_sorts = (uu___352_13233.use_bv_sorts);
        qtbl_name_and_index = (uu___352_13233.qtbl_name_and_index);
        normalized_eff_names = (uu___352_13233.normalized_eff_names);
        fv_delta_depths = (uu___352_13233.fv_delta_depths);
        proof_ns = (uu___352_13233.proof_ns);
        synth_hook = (uu___352_13233.synth_hook);
        try_solve_implicits_hook = (uu___352_13233.try_solve_implicits_hook);
        splice = (uu___352_13233.splice);
        postprocess = (uu___352_13233.postprocess);
        is_native_tactic = (uu___352_13233.is_native_tactic);
        identifier_info = (uu___352_13233.identifier_info);
        tc_hooks = (uu___352_13233.tc_hooks);
        dsenv = uu____13234;
        nbe = (uu___352_13233.nbe);
        strict_args_tab = (uu___352_13233.strict_args_tab)
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
      | (NoDelta ,uu____13263) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13266,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13268,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13271 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13285 . unit -> 'Auu____13285 FStar_Util.smap =
  fun uu____13292  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13298 . unit -> 'Auu____13298 FStar_Util.smap =
  fun uu____13305  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13443 = new_gamma_cache ()  in
                  let uu____13446 = new_sigtab ()  in
                  let uu____13449 = new_sigtab ()  in
                  let uu____13456 =
                    let uu____13471 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13471, FStar_Pervasives_Native.None)  in
                  let uu____13492 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13496 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13500 = FStar_Options.using_facts_from ()  in
                  let uu____13501 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13504 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13505 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13443;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13446;
                    attrtab = uu____13449;
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
                    qtbl_name_and_index = uu____13456;
                    normalized_eff_names = uu____13492;
                    fv_delta_depths = uu____13496;
                    proof_ns = uu____13500;
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
                    is_native_tactic = (fun uu____13589  -> false);
                    identifier_info = uu____13501;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13504;
                    nbe = nbe1;
                    strict_args_tab = uu____13505
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
  fun uu____13668  ->
    let uu____13669 = FStar_ST.op_Bang query_indices  in
    match uu____13669 with
    | [] -> failwith "Empty query indices!"
    | uu____13724 ->
        let uu____13734 =
          let uu____13744 =
            let uu____13752 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13752  in
          let uu____13806 = FStar_ST.op_Bang query_indices  in uu____13744 ::
            uu____13806
           in
        FStar_ST.op_Colon_Equals query_indices uu____13734
  
let (pop_query_indices : unit -> unit) =
  fun uu____13902  ->
    let uu____13903 = FStar_ST.op_Bang query_indices  in
    match uu____13903 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14030  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14067  ->
    match uu____14067 with
    | (l,n1) ->
        let uu____14077 = FStar_ST.op_Bang query_indices  in
        (match uu____14077 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14199 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14222  ->
    let uu____14223 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14223
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14291 =
       let uu____14294 = FStar_ST.op_Bang stack  in env :: uu____14294  in
     FStar_ST.op_Colon_Equals stack uu____14291);
    (let uu___423_14343 = env  in
     let uu____14344 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14347 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14350 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14357 =
       let uu____14372 =
         let uu____14376 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14376  in
       let uu____14408 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14372, uu____14408)  in
     let uu____14457 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14460 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14463 =
       let uu____14466 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14466  in
     let uu____14486 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___423_14343.solver);
       range = (uu___423_14343.range);
       curmodule = (uu___423_14343.curmodule);
       gamma = (uu___423_14343.gamma);
       gamma_sig = (uu___423_14343.gamma_sig);
       gamma_cache = uu____14344;
       modules = (uu___423_14343.modules);
       expected_typ = (uu___423_14343.expected_typ);
       sigtab = uu____14347;
       attrtab = uu____14350;
       is_pattern = (uu___423_14343.is_pattern);
       instantiate_imp = (uu___423_14343.instantiate_imp);
       effects = (uu___423_14343.effects);
       generalize = (uu___423_14343.generalize);
       letrecs = (uu___423_14343.letrecs);
       top_level = (uu___423_14343.top_level);
       check_uvars = (uu___423_14343.check_uvars);
       use_eq = (uu___423_14343.use_eq);
       is_iface = (uu___423_14343.is_iface);
       admit = (uu___423_14343.admit);
       lax = (uu___423_14343.lax);
       lax_universes = (uu___423_14343.lax_universes);
       phase1 = (uu___423_14343.phase1);
       failhard = (uu___423_14343.failhard);
       nosynth = (uu___423_14343.nosynth);
       uvar_subtyping = (uu___423_14343.uvar_subtyping);
       tc_term = (uu___423_14343.tc_term);
       type_of = (uu___423_14343.type_of);
       universe_of = (uu___423_14343.universe_of);
       check_type_of = (uu___423_14343.check_type_of);
       use_bv_sorts = (uu___423_14343.use_bv_sorts);
       qtbl_name_and_index = uu____14357;
       normalized_eff_names = uu____14457;
       fv_delta_depths = uu____14460;
       proof_ns = (uu___423_14343.proof_ns);
       synth_hook = (uu___423_14343.synth_hook);
       try_solve_implicits_hook = (uu___423_14343.try_solve_implicits_hook);
       splice = (uu___423_14343.splice);
       postprocess = (uu___423_14343.postprocess);
       is_native_tactic = (uu___423_14343.is_native_tactic);
       identifier_info = uu____14463;
       tc_hooks = (uu___423_14343.tc_hooks);
       dsenv = (uu___423_14343.dsenv);
       nbe = (uu___423_14343.nbe);
       strict_args_tab = uu____14486
     })
  
let (pop_stack : unit -> env) =
  fun uu____14504  ->
    let uu____14505 = FStar_ST.op_Bang stack  in
    match uu____14505 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14559 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14649  ->
           let uu____14650 = snapshot_stack env  in
           match uu____14650 with
           | (stack_depth,env1) ->
               let uu____14684 = snapshot_query_indices ()  in
               (match uu____14684 with
                | (query_indices_depth,()) ->
                    let uu____14717 = (env1.solver).snapshot msg  in
                    (match uu____14717 with
                     | (solver_depth,()) ->
                         let uu____14774 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14774 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___448_14841 = env1  in
                                 {
                                   solver = (uu___448_14841.solver);
                                   range = (uu___448_14841.range);
                                   curmodule = (uu___448_14841.curmodule);
                                   gamma = (uu___448_14841.gamma);
                                   gamma_sig = (uu___448_14841.gamma_sig);
                                   gamma_cache = (uu___448_14841.gamma_cache);
                                   modules = (uu___448_14841.modules);
                                   expected_typ =
                                     (uu___448_14841.expected_typ);
                                   sigtab = (uu___448_14841.sigtab);
                                   attrtab = (uu___448_14841.attrtab);
                                   is_pattern = (uu___448_14841.is_pattern);
                                   instantiate_imp =
                                     (uu___448_14841.instantiate_imp);
                                   effects = (uu___448_14841.effects);
                                   generalize = (uu___448_14841.generalize);
                                   letrecs = (uu___448_14841.letrecs);
                                   top_level = (uu___448_14841.top_level);
                                   check_uvars = (uu___448_14841.check_uvars);
                                   use_eq = (uu___448_14841.use_eq);
                                   is_iface = (uu___448_14841.is_iface);
                                   admit = (uu___448_14841.admit);
                                   lax = (uu___448_14841.lax);
                                   lax_universes =
                                     (uu___448_14841.lax_universes);
                                   phase1 = (uu___448_14841.phase1);
                                   failhard = (uu___448_14841.failhard);
                                   nosynth = (uu___448_14841.nosynth);
                                   uvar_subtyping =
                                     (uu___448_14841.uvar_subtyping);
                                   tc_term = (uu___448_14841.tc_term);
                                   type_of = (uu___448_14841.type_of);
                                   universe_of = (uu___448_14841.universe_of);
                                   check_type_of =
                                     (uu___448_14841.check_type_of);
                                   use_bv_sorts =
                                     (uu___448_14841.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___448_14841.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___448_14841.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___448_14841.fv_delta_depths);
                                   proof_ns = (uu___448_14841.proof_ns);
                                   synth_hook = (uu___448_14841.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___448_14841.try_solve_implicits_hook);
                                   splice = (uu___448_14841.splice);
                                   postprocess = (uu___448_14841.postprocess);
                                   is_native_tactic =
                                     (uu___448_14841.is_native_tactic);
                                   identifier_info =
                                     (uu___448_14841.identifier_info);
                                   tc_hooks = (uu___448_14841.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___448_14841.nbe);
                                   strict_args_tab =
                                     (uu___448_14841.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14875  ->
             let uu____14876 =
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
             match uu____14876 with
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
                             ((let uu____15056 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15056
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15072 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15072
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15104,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15146 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15176  ->
                  match uu____15176 with
                  | (m,uu____15184) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15146 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___493_15199 = env  in
               {
                 solver = (uu___493_15199.solver);
                 range = (uu___493_15199.range);
                 curmodule = (uu___493_15199.curmodule);
                 gamma = (uu___493_15199.gamma);
                 gamma_sig = (uu___493_15199.gamma_sig);
                 gamma_cache = (uu___493_15199.gamma_cache);
                 modules = (uu___493_15199.modules);
                 expected_typ = (uu___493_15199.expected_typ);
                 sigtab = (uu___493_15199.sigtab);
                 attrtab = (uu___493_15199.attrtab);
                 is_pattern = (uu___493_15199.is_pattern);
                 instantiate_imp = (uu___493_15199.instantiate_imp);
                 effects = (uu___493_15199.effects);
                 generalize = (uu___493_15199.generalize);
                 letrecs = (uu___493_15199.letrecs);
                 top_level = (uu___493_15199.top_level);
                 check_uvars = (uu___493_15199.check_uvars);
                 use_eq = (uu___493_15199.use_eq);
                 is_iface = (uu___493_15199.is_iface);
                 admit = (uu___493_15199.admit);
                 lax = (uu___493_15199.lax);
                 lax_universes = (uu___493_15199.lax_universes);
                 phase1 = (uu___493_15199.phase1);
                 failhard = (uu___493_15199.failhard);
                 nosynth = (uu___493_15199.nosynth);
                 uvar_subtyping = (uu___493_15199.uvar_subtyping);
                 tc_term = (uu___493_15199.tc_term);
                 type_of = (uu___493_15199.type_of);
                 universe_of = (uu___493_15199.universe_of);
                 check_type_of = (uu___493_15199.check_type_of);
                 use_bv_sorts = (uu___493_15199.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___493_15199.normalized_eff_names);
                 fv_delta_depths = (uu___493_15199.fv_delta_depths);
                 proof_ns = (uu___493_15199.proof_ns);
                 synth_hook = (uu___493_15199.synth_hook);
                 try_solve_implicits_hook =
                   (uu___493_15199.try_solve_implicits_hook);
                 splice = (uu___493_15199.splice);
                 postprocess = (uu___493_15199.postprocess);
                 is_native_tactic = (uu___493_15199.is_native_tactic);
                 identifier_info = (uu___493_15199.identifier_info);
                 tc_hooks = (uu___493_15199.tc_hooks);
                 dsenv = (uu___493_15199.dsenv);
                 nbe = (uu___493_15199.nbe);
                 strict_args_tab = (uu___493_15199.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15216,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___502_15232 = env  in
               {
                 solver = (uu___502_15232.solver);
                 range = (uu___502_15232.range);
                 curmodule = (uu___502_15232.curmodule);
                 gamma = (uu___502_15232.gamma);
                 gamma_sig = (uu___502_15232.gamma_sig);
                 gamma_cache = (uu___502_15232.gamma_cache);
                 modules = (uu___502_15232.modules);
                 expected_typ = (uu___502_15232.expected_typ);
                 sigtab = (uu___502_15232.sigtab);
                 attrtab = (uu___502_15232.attrtab);
                 is_pattern = (uu___502_15232.is_pattern);
                 instantiate_imp = (uu___502_15232.instantiate_imp);
                 effects = (uu___502_15232.effects);
                 generalize = (uu___502_15232.generalize);
                 letrecs = (uu___502_15232.letrecs);
                 top_level = (uu___502_15232.top_level);
                 check_uvars = (uu___502_15232.check_uvars);
                 use_eq = (uu___502_15232.use_eq);
                 is_iface = (uu___502_15232.is_iface);
                 admit = (uu___502_15232.admit);
                 lax = (uu___502_15232.lax);
                 lax_universes = (uu___502_15232.lax_universes);
                 phase1 = (uu___502_15232.phase1);
                 failhard = (uu___502_15232.failhard);
                 nosynth = (uu___502_15232.nosynth);
                 uvar_subtyping = (uu___502_15232.uvar_subtyping);
                 tc_term = (uu___502_15232.tc_term);
                 type_of = (uu___502_15232.type_of);
                 universe_of = (uu___502_15232.universe_of);
                 check_type_of = (uu___502_15232.check_type_of);
                 use_bv_sorts = (uu___502_15232.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___502_15232.normalized_eff_names);
                 fv_delta_depths = (uu___502_15232.fv_delta_depths);
                 proof_ns = (uu___502_15232.proof_ns);
                 synth_hook = (uu___502_15232.synth_hook);
                 try_solve_implicits_hook =
                   (uu___502_15232.try_solve_implicits_hook);
                 splice = (uu___502_15232.splice);
                 postprocess = (uu___502_15232.postprocess);
                 is_native_tactic = (uu___502_15232.is_native_tactic);
                 identifier_info = (uu___502_15232.identifier_info);
                 tc_hooks = (uu___502_15232.tc_hooks);
                 dsenv = (uu___502_15232.dsenv);
                 nbe = (uu___502_15232.nbe);
                 strict_args_tab = (uu___502_15232.strict_args_tab)
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
        (let uu___509_15275 = e  in
         {
           solver = (uu___509_15275.solver);
           range = r;
           curmodule = (uu___509_15275.curmodule);
           gamma = (uu___509_15275.gamma);
           gamma_sig = (uu___509_15275.gamma_sig);
           gamma_cache = (uu___509_15275.gamma_cache);
           modules = (uu___509_15275.modules);
           expected_typ = (uu___509_15275.expected_typ);
           sigtab = (uu___509_15275.sigtab);
           attrtab = (uu___509_15275.attrtab);
           is_pattern = (uu___509_15275.is_pattern);
           instantiate_imp = (uu___509_15275.instantiate_imp);
           effects = (uu___509_15275.effects);
           generalize = (uu___509_15275.generalize);
           letrecs = (uu___509_15275.letrecs);
           top_level = (uu___509_15275.top_level);
           check_uvars = (uu___509_15275.check_uvars);
           use_eq = (uu___509_15275.use_eq);
           is_iface = (uu___509_15275.is_iface);
           admit = (uu___509_15275.admit);
           lax = (uu___509_15275.lax);
           lax_universes = (uu___509_15275.lax_universes);
           phase1 = (uu___509_15275.phase1);
           failhard = (uu___509_15275.failhard);
           nosynth = (uu___509_15275.nosynth);
           uvar_subtyping = (uu___509_15275.uvar_subtyping);
           tc_term = (uu___509_15275.tc_term);
           type_of = (uu___509_15275.type_of);
           universe_of = (uu___509_15275.universe_of);
           check_type_of = (uu___509_15275.check_type_of);
           use_bv_sorts = (uu___509_15275.use_bv_sorts);
           qtbl_name_and_index = (uu___509_15275.qtbl_name_and_index);
           normalized_eff_names = (uu___509_15275.normalized_eff_names);
           fv_delta_depths = (uu___509_15275.fv_delta_depths);
           proof_ns = (uu___509_15275.proof_ns);
           synth_hook = (uu___509_15275.synth_hook);
           try_solve_implicits_hook =
             (uu___509_15275.try_solve_implicits_hook);
           splice = (uu___509_15275.splice);
           postprocess = (uu___509_15275.postprocess);
           is_native_tactic = (uu___509_15275.is_native_tactic);
           identifier_info = (uu___509_15275.identifier_info);
           tc_hooks = (uu___509_15275.tc_hooks);
           dsenv = (uu___509_15275.dsenv);
           nbe = (uu___509_15275.nbe);
           strict_args_tab = (uu___509_15275.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15295 =
        let uu____15296 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15296 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15295
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15351 =
          let uu____15352 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15352 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15351
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15407 =
          let uu____15408 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15408 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15407
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15463 =
        let uu____15464 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15464 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15463
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___526_15528 = env  in
      {
        solver = (uu___526_15528.solver);
        range = (uu___526_15528.range);
        curmodule = lid;
        gamma = (uu___526_15528.gamma);
        gamma_sig = (uu___526_15528.gamma_sig);
        gamma_cache = (uu___526_15528.gamma_cache);
        modules = (uu___526_15528.modules);
        expected_typ = (uu___526_15528.expected_typ);
        sigtab = (uu___526_15528.sigtab);
        attrtab = (uu___526_15528.attrtab);
        is_pattern = (uu___526_15528.is_pattern);
        instantiate_imp = (uu___526_15528.instantiate_imp);
        effects = (uu___526_15528.effects);
        generalize = (uu___526_15528.generalize);
        letrecs = (uu___526_15528.letrecs);
        top_level = (uu___526_15528.top_level);
        check_uvars = (uu___526_15528.check_uvars);
        use_eq = (uu___526_15528.use_eq);
        is_iface = (uu___526_15528.is_iface);
        admit = (uu___526_15528.admit);
        lax = (uu___526_15528.lax);
        lax_universes = (uu___526_15528.lax_universes);
        phase1 = (uu___526_15528.phase1);
        failhard = (uu___526_15528.failhard);
        nosynth = (uu___526_15528.nosynth);
        uvar_subtyping = (uu___526_15528.uvar_subtyping);
        tc_term = (uu___526_15528.tc_term);
        type_of = (uu___526_15528.type_of);
        universe_of = (uu___526_15528.universe_of);
        check_type_of = (uu___526_15528.check_type_of);
        use_bv_sorts = (uu___526_15528.use_bv_sorts);
        qtbl_name_and_index = (uu___526_15528.qtbl_name_and_index);
        normalized_eff_names = (uu___526_15528.normalized_eff_names);
        fv_delta_depths = (uu___526_15528.fv_delta_depths);
        proof_ns = (uu___526_15528.proof_ns);
        synth_hook = (uu___526_15528.synth_hook);
        try_solve_implicits_hook = (uu___526_15528.try_solve_implicits_hook);
        splice = (uu___526_15528.splice);
        postprocess = (uu___526_15528.postprocess);
        is_native_tactic = (uu___526_15528.is_native_tactic);
        identifier_info = (uu___526_15528.identifier_info);
        tc_hooks = (uu___526_15528.tc_hooks);
        dsenv = (uu___526_15528.dsenv);
        nbe = (uu___526_15528.nbe);
        strict_args_tab = (uu___526_15528.strict_args_tab)
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
      let uu____15559 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15559
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15572 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15572)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15587 =
      let uu____15589 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15589  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15587)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15598  ->
    let uu____15599 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15599
  
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
      | ((formals,t),uu____15699) ->
          let vs = mk_univ_subst formals us  in
          let uu____15723 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15723)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15740  ->
    match uu___1_15740 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15766  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15786 = inst_tscheme t  in
      match uu____15786 with
      | (us,t1) ->
          let uu____15797 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15797)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____15818  ->
          match uu____15818 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____15840 =
                         let uu____15842 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____15846 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____15850 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____15852 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____15842 uu____15846 uu____15850 uu____15852
                          in
                       failwith uu____15840)
                    else ();
                    (let uu____15857 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____15857))
               | uu____15866 ->
                   let uu____15867 =
                     let uu____15869 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____15869
                      in
                   failwith uu____15867)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15881 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15892 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15903 -> false
  
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
             | ([],uu____15951) -> Maybe
             | (uu____15958,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15978 -> No  in
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
          let uu____16072 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16072 with
          | FStar_Pervasives_Native.None  ->
              let uu____16095 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16139  ->
                     match uu___2_16139 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16178 = FStar_Ident.lid_equals lid l  in
                         if uu____16178
                         then
                           let uu____16201 =
                             let uu____16220 =
                               let uu____16235 = inst_tscheme t  in
                               FStar_Util.Inl uu____16235  in
                             let uu____16250 = FStar_Ident.range_of_lid l  in
                             (uu____16220, uu____16250)  in
                           FStar_Pervasives_Native.Some uu____16201
                         else FStar_Pervasives_Native.None
                     | uu____16303 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16095
                (fun uu____16341  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16350  ->
                        match uu___3_16350 with
                        | (uu____16353,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16355);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16356;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16357;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16358;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16359;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16379 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16379
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
                                  uu____16431 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16438 -> cache t  in
                            let uu____16439 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16439 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16445 =
                                   let uu____16446 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16446)
                                    in
                                 maybe_cache uu____16445)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16517 = find_in_sigtab env lid  in
         match uu____16517 with
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
      let uu____16598 = lookup_qname env lid  in
      match uu____16598 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16619,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16733 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16733 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16778 =
          let uu____16781 = lookup_attr env1 attr  in se1 :: uu____16781  in
        FStar_Util.smap_add (attrtab env1) attr uu____16778  in
      FStar_List.iter
        (fun attr  ->
           let uu____16791 =
             let uu____16792 = FStar_Syntax_Subst.compress attr  in
             uu____16792.FStar_Syntax_Syntax.n  in
           match uu____16791 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16796 =
                 let uu____16798 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16798.FStar_Ident.str  in
               add_one1 env se uu____16796
           | uu____16799 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16822) ->
          add_sigelts env ses
      | uu____16831 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____16846 -> ()))

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
        (fun uu___4_16878  ->
           match uu___4_16878 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16896 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16958,lb::[]),uu____16960) ->
            let uu____16969 =
              let uu____16978 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16987 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16978, uu____16987)  in
            FStar_Pervasives_Native.Some uu____16969
        | FStar_Syntax_Syntax.Sig_let ((uu____17000,lbs),uu____17002) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17034 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17047 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17047
                     then
                       let uu____17060 =
                         let uu____17069 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17078 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17069, uu____17078)  in
                       FStar_Pervasives_Native.Some uu____17060
                     else FStar_Pervasives_Native.None)
        | uu____17101 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____17161 =
            let uu____17170 =
              let uu____17175 =
                let uu____17176 =
                  let uu____17179 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____17179
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____17176)  in
              inst_tscheme1 uu____17175  in
            (uu____17170, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____17161
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____17201,uu____17202) ->
          let uu____17207 =
            let uu____17216 =
              let uu____17221 =
                let uu____17222 =
                  let uu____17225 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____17225  in
                (us, uu____17222)  in
              inst_tscheme1 uu____17221  in
            (uu____17216, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____17207
      | uu____17244 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17333 =
          match uu____17333 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17429,uvs,t,uu____17432,uu____17433,uu____17434);
                      FStar_Syntax_Syntax.sigrng = uu____17435;
                      FStar_Syntax_Syntax.sigquals = uu____17436;
                      FStar_Syntax_Syntax.sigmeta = uu____17437;
                      FStar_Syntax_Syntax.sigattrs = uu____17438;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17461 =
                     let uu____17470 = inst_tscheme1 (uvs, t)  in
                     (uu____17470, rng)  in
                   FStar_Pervasives_Native.Some uu____17461
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17494;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17496;
                      FStar_Syntax_Syntax.sigattrs = uu____17497;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17514 =
                     let uu____17516 = in_cur_mod env l  in uu____17516 = Yes
                      in
                   if uu____17514
                   then
                     let uu____17528 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17528
                      then
                        let uu____17544 =
                          let uu____17553 = inst_tscheme1 (uvs, t)  in
                          (uu____17553, rng)  in
                        FStar_Pervasives_Native.Some uu____17544
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17586 =
                        let uu____17595 = inst_tscheme1 (uvs, t)  in
                        (uu____17595, rng)  in
                      FStar_Pervasives_Native.Some uu____17586)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17620,uu____17621);
                      FStar_Syntax_Syntax.sigrng = uu____17622;
                      FStar_Syntax_Syntax.sigquals = uu____17623;
                      FStar_Syntax_Syntax.sigmeta = uu____17624;
                      FStar_Syntax_Syntax.sigattrs = uu____17625;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17666 =
                          let uu____17675 = inst_tscheme1 (uvs, k)  in
                          (uu____17675, rng)  in
                        FStar_Pervasives_Native.Some uu____17666
                    | uu____17696 ->
                        let uu____17697 =
                          let uu____17706 =
                            let uu____17711 =
                              let uu____17712 =
                                let uu____17715 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17715
                                 in
                              (uvs, uu____17712)  in
                            inst_tscheme1 uu____17711  in
                          (uu____17706, rng)  in
                        FStar_Pervasives_Native.Some uu____17697)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17738,uu____17739);
                      FStar_Syntax_Syntax.sigrng = uu____17740;
                      FStar_Syntax_Syntax.sigquals = uu____17741;
                      FStar_Syntax_Syntax.sigmeta = uu____17742;
                      FStar_Syntax_Syntax.sigattrs = uu____17743;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17785 =
                          let uu____17794 = inst_tscheme_with (uvs, k) us  in
                          (uu____17794, rng)  in
                        FStar_Pervasives_Native.Some uu____17785
                    | uu____17815 ->
                        let uu____17816 =
                          let uu____17825 =
                            let uu____17830 =
                              let uu____17831 =
                                let uu____17834 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17834
                                 in
                              (uvs, uu____17831)  in
                            inst_tscheme_with uu____17830 us  in
                          (uu____17825, rng)  in
                        FStar_Pervasives_Native.Some uu____17816)
               | FStar_Util.Inr se ->
                   let uu____17870 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17891;
                          FStar_Syntax_Syntax.sigrng = uu____17892;
                          FStar_Syntax_Syntax.sigquals = uu____17893;
                          FStar_Syntax_Syntax.sigmeta = uu____17894;
                          FStar_Syntax_Syntax.sigattrs = uu____17895;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17910 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____17870
                     (FStar_Util.map_option
                        (fun uu____17958  ->
                           match uu____17958 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17989 =
          let uu____18000 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18000 mapper  in
        match uu____17989 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18074 =
              let uu____18085 =
                let uu____18092 =
                  let uu___853_18095 = t  in
                  let uu____18096 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___853_18095.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18096;
                    FStar_Syntax_Syntax.vars =
                      (uu___853_18095.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18092)  in
              (uu____18085, r)  in
            FStar_Pervasives_Native.Some uu____18074
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18145 = lookup_qname env l  in
      match uu____18145 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18166 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18220 = try_lookup_bv env bv  in
      match uu____18220 with
      | FStar_Pervasives_Native.None  ->
          let uu____18235 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18235 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18251 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18252 =
            let uu____18253 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18253  in
          (uu____18251, uu____18252)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18275 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18275 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18341 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18341  in
          let uu____18342 =
            let uu____18351 =
              let uu____18356 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18356)  in
            (uu____18351, r1)  in
          FStar_Pervasives_Native.Some uu____18342
  
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
        let uu____18391 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18391 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18424,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18449 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18449  in
            let uu____18450 =
              let uu____18455 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18455, r1)  in
            FStar_Pervasives_Native.Some uu____18450
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18479 = try_lookup_lid env l  in
      match uu____18479 with
      | FStar_Pervasives_Native.None  ->
          let uu____18506 = name_not_found l  in
          let uu____18512 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18506 uu____18512
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18555  ->
              match uu___5_18555 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18559 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18580 = lookup_qname env lid  in
      match uu____18580 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18589,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18592;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18594;
              FStar_Syntax_Syntax.sigattrs = uu____18595;_},FStar_Pervasives_Native.None
            ),uu____18596)
          ->
          let uu____18645 =
            let uu____18652 =
              let uu____18653 =
                let uu____18656 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18656 t  in
              (uvs, uu____18653)  in
            (uu____18652, q)  in
          FStar_Pervasives_Native.Some uu____18645
      | uu____18669 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18691 = lookup_qname env lid  in
      match uu____18691 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18696,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18699;
              FStar_Syntax_Syntax.sigquals = uu____18700;
              FStar_Syntax_Syntax.sigmeta = uu____18701;
              FStar_Syntax_Syntax.sigattrs = uu____18702;_},FStar_Pervasives_Native.None
            ),uu____18703)
          ->
          let uu____18752 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18752 (uvs, t)
      | uu____18757 ->
          let uu____18758 = name_not_found lid  in
          let uu____18764 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18758 uu____18764
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18784 = lookup_qname env lid  in
      match uu____18784 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18789,uvs,t,uu____18792,uu____18793,uu____18794);
              FStar_Syntax_Syntax.sigrng = uu____18795;
              FStar_Syntax_Syntax.sigquals = uu____18796;
              FStar_Syntax_Syntax.sigmeta = uu____18797;
              FStar_Syntax_Syntax.sigattrs = uu____18798;_},FStar_Pervasives_Native.None
            ),uu____18799)
          ->
          let uu____18854 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18854 (uvs, t)
      | uu____18859 ->
          let uu____18860 = name_not_found lid  in
          let uu____18866 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18860 uu____18866
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18889 = lookup_qname env lid  in
      match uu____18889 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18897,uu____18898,uu____18899,uu____18900,uu____18901,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18903;
              FStar_Syntax_Syntax.sigquals = uu____18904;
              FStar_Syntax_Syntax.sigmeta = uu____18905;
              FStar_Syntax_Syntax.sigattrs = uu____18906;_},uu____18907),uu____18908)
          -> (true, dcs)
      | uu____18971 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18987 = lookup_qname env lid  in
      match uu____18987 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18988,uu____18989,uu____18990,l,uu____18992,uu____18993);
              FStar_Syntax_Syntax.sigrng = uu____18994;
              FStar_Syntax_Syntax.sigquals = uu____18995;
              FStar_Syntax_Syntax.sigmeta = uu____18996;
              FStar_Syntax_Syntax.sigattrs = uu____18997;_},uu____18998),uu____18999)
          -> l
      | uu____19056 ->
          let uu____19057 =
            let uu____19059 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19059  in
          failwith uu____19057
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19129)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19186) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19210 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19210
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19245 -> FStar_Pervasives_Native.None)
          | uu____19254 -> FStar_Pervasives_Native.None
  
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
        let uu____19316 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19316
  
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
        let uu____19349 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19349
  
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
             (FStar_Util.Inl uu____19401,uu____19402) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19451),uu____19452) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19501 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19519 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19529 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19546 ->
                  let uu____19553 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19553
              | FStar_Syntax_Syntax.Sig_let ((uu____19554,lbs),uu____19556)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19572 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19572
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19579 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19587 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19588 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19595 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19596 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19597 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19598 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19611 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19629 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19629
           (fun d_opt  ->
              let uu____19642 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19642
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19652 =
                   let uu____19655 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19655  in
                 match uu____19652 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19656 =
                       let uu____19658 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19658
                        in
                     failwith uu____19656
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19663 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19663
                       then
                         let uu____19666 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19668 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19670 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19666 uu____19668 uu____19670
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
        (FStar_Util.Inr (se,uu____19695),uu____19696) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19745 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19767),uu____19768) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19817 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19839 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19839
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19862 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19862 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19886 =
                      let uu____19887 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19887.FStar_Syntax_Syntax.n  in
                    match uu____19886 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19892 -> false))
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let s =
        let uu____19929 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19929.FStar_Ident.str  in
      let uu____19930 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19930 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19958 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19958  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____19986 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____19986)
                  in
               (FStar_Util.smap_add env.strict_args_tab s res; res))
      | FStar_Pervasives_Native.Some l -> l
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____20036 = lookup_qname env ftv  in
      match uu____20036 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20040) ->
          let uu____20085 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____20085 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20106,t),r) ->
               let uu____20121 =
                 let uu____20122 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20122 t  in
               FStar_Pervasives_Native.Some uu____20121)
      | uu____20123 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20135 = try_lookup_effect_lid env ftv  in
      match uu____20135 with
      | FStar_Pervasives_Native.None  ->
          let uu____20138 = name_not_found ftv  in
          let uu____20144 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20138 uu____20144
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
        let uu____20168 = lookup_qname env lid0  in
        match uu____20168 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20179);
                FStar_Syntax_Syntax.sigrng = uu____20180;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20182;
                FStar_Syntax_Syntax.sigattrs = uu____20183;_},FStar_Pervasives_Native.None
              ),uu____20184)
            ->
            let lid1 =
              let uu____20238 =
                let uu____20239 = FStar_Ident.range_of_lid lid  in
                let uu____20240 =
                  let uu____20241 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20241  in
                FStar_Range.set_use_range uu____20239 uu____20240  in
              FStar_Ident.set_lid_range lid uu____20238  in
            let uu____20242 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20248  ->
                      match uu___6_20248 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20251 -> false))
               in
            if uu____20242
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20270 =
                      let uu____20272 =
                        let uu____20274 = get_range env  in
                        FStar_Range.string_of_range uu____20274  in
                      let uu____20275 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20277 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20272 uu____20275 uu____20277
                       in
                    failwith uu____20270)
                  in
               match (binders, univs1) with
               | ([],uu____20298) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20324,uu____20325::uu____20326::uu____20327) ->
                   let uu____20348 =
                     let uu____20350 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20352 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20350 uu____20352
                      in
                   failwith uu____20348
               | uu____20363 ->
                   let uu____20378 =
                     let uu____20383 =
                       let uu____20384 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20384)  in
                     inst_tscheme_with uu____20383 insts  in
                   (match uu____20378 with
                    | (uu____20397,t) ->
                        let t1 =
                          let uu____20400 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20400 t  in
                        let uu____20401 =
                          let uu____20402 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20402.FStar_Syntax_Syntax.n  in
                        (match uu____20401 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20437 -> failwith "Impossible")))
        | uu____20445 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20469 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20469 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20482,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20489 = find1 l2  in
            (match uu____20489 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20496 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20496 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20500 = find1 l  in
            (match uu____20500 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20505 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20505
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20520 = lookup_qname env l1  in
      match uu____20520 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20523;
              FStar_Syntax_Syntax.sigrng = uu____20524;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20526;
              FStar_Syntax_Syntax.sigattrs = uu____20527;_},uu____20528),uu____20529)
          -> q
      | uu____20580 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20604 =
          let uu____20605 =
            let uu____20607 = FStar_Util.string_of_int i  in
            let uu____20609 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20607 uu____20609
             in
          failwith uu____20605  in
        let uu____20612 = lookup_datacon env lid  in
        match uu____20612 with
        | (uu____20617,t) ->
            let uu____20619 =
              let uu____20620 = FStar_Syntax_Subst.compress t  in
              uu____20620.FStar_Syntax_Syntax.n  in
            (match uu____20619 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20624) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20668 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20668
                      FStar_Pervasives_Native.fst)
             | uu____20679 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20693 = lookup_qname env l  in
      match uu____20693 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20695,uu____20696,uu____20697);
              FStar_Syntax_Syntax.sigrng = uu____20698;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20700;
              FStar_Syntax_Syntax.sigattrs = uu____20701;_},uu____20702),uu____20703)
          ->
          FStar_Util.for_some
            (fun uu___7_20756  ->
               match uu___7_20756 with
               | FStar_Syntax_Syntax.Projector uu____20758 -> true
               | uu____20764 -> false) quals
      | uu____20766 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20780 = lookup_qname env lid  in
      match uu____20780 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20782,uu____20783,uu____20784,uu____20785,uu____20786,uu____20787);
              FStar_Syntax_Syntax.sigrng = uu____20788;
              FStar_Syntax_Syntax.sigquals = uu____20789;
              FStar_Syntax_Syntax.sigmeta = uu____20790;
              FStar_Syntax_Syntax.sigattrs = uu____20791;_},uu____20792),uu____20793)
          -> true
      | uu____20851 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20865 = lookup_qname env lid  in
      match uu____20865 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20867,uu____20868,uu____20869,uu____20870,uu____20871,uu____20872);
              FStar_Syntax_Syntax.sigrng = uu____20873;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20875;
              FStar_Syntax_Syntax.sigattrs = uu____20876;_},uu____20877),uu____20878)
          ->
          FStar_Util.for_some
            (fun uu___8_20939  ->
               match uu___8_20939 with
               | FStar_Syntax_Syntax.RecordType uu____20941 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20951 -> true
               | uu____20961 -> false) quals
      | uu____20963 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20973,uu____20974);
            FStar_Syntax_Syntax.sigrng = uu____20975;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20977;
            FStar_Syntax_Syntax.sigattrs = uu____20978;_},uu____20979),uu____20980)
        ->
        FStar_Util.for_some
          (fun uu___9_21037  ->
             match uu___9_21037 with
             | FStar_Syntax_Syntax.Action uu____21039 -> true
             | uu____21041 -> false) quals
    | uu____21043 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21057 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21057
  
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
      let uu____21074 =
        let uu____21075 = FStar_Syntax_Util.un_uinst head1  in
        uu____21075.FStar_Syntax_Syntax.n  in
      match uu____21074 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21081 ->
               true
           | uu____21084 -> false)
      | uu____21086 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21100 = lookup_qname env l  in
      match uu____21100 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21103),uu____21104) ->
          FStar_Util.for_some
            (fun uu___10_21152  ->
               match uu___10_21152 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21155 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21157 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21233 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21251) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21269 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21277 ->
                 FStar_Pervasives_Native.Some true
             | uu____21296 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21299 =
        let uu____21303 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21303 mapper  in
      match uu____21299 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21363 = lookup_qname env lid  in
      match uu____21363 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21367,uu____21368,tps,uu____21370,uu____21371,uu____21372);
              FStar_Syntax_Syntax.sigrng = uu____21373;
              FStar_Syntax_Syntax.sigquals = uu____21374;
              FStar_Syntax_Syntax.sigmeta = uu____21375;
              FStar_Syntax_Syntax.sigattrs = uu____21376;_},uu____21377),uu____21378)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21444 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21490  ->
              match uu____21490 with
              | (d,uu____21499) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21515 = effect_decl_opt env l  in
      match uu____21515 with
      | FStar_Pervasives_Native.None  ->
          let uu____21530 = name_not_found l  in
          let uu____21536 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21530 uu____21536
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21559  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21578  ->
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
        let uu____21610 = FStar_Ident.lid_equals l1 l2  in
        if uu____21610
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21621 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21621
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21632 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21685  ->
                        match uu____21685 with
                        | (m1,m2,uu____21699,uu____21700,uu____21701) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21632 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21718 =
                    let uu____21724 =
                      let uu____21726 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21728 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21726
                        uu____21728
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21724)
                     in
                  FStar_Errors.raise_error uu____21718 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21738,uu____21739,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21773 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21773
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
  'Auu____21793 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21793) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21822 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21848  ->
                match uu____21848 with
                | (d,uu____21855) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21822 with
      | FStar_Pervasives_Native.None  ->
          let uu____21866 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21866
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21881 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____21881 with
           | (uu____21896,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21914)::(wp,uu____21916)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21972 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1510_22022 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1510_22022.order);
              joins = (uu___1510_22022.joins)
            }  in
          let uu___1513_22031 = env  in
          {
            solver = (uu___1513_22031.solver);
            range = (uu___1513_22031.range);
            curmodule = (uu___1513_22031.curmodule);
            gamma = (uu___1513_22031.gamma);
            gamma_sig = (uu___1513_22031.gamma_sig);
            gamma_cache = (uu___1513_22031.gamma_cache);
            modules = (uu___1513_22031.modules);
            expected_typ = (uu___1513_22031.expected_typ);
            sigtab = (uu___1513_22031.sigtab);
            attrtab = (uu___1513_22031.attrtab);
            is_pattern = (uu___1513_22031.is_pattern);
            instantiate_imp = (uu___1513_22031.instantiate_imp);
            effects;
            generalize = (uu___1513_22031.generalize);
            letrecs = (uu___1513_22031.letrecs);
            top_level = (uu___1513_22031.top_level);
            check_uvars = (uu___1513_22031.check_uvars);
            use_eq = (uu___1513_22031.use_eq);
            is_iface = (uu___1513_22031.is_iface);
            admit = (uu___1513_22031.admit);
            lax = (uu___1513_22031.lax);
            lax_universes = (uu___1513_22031.lax_universes);
            phase1 = (uu___1513_22031.phase1);
            failhard = (uu___1513_22031.failhard);
            nosynth = (uu___1513_22031.nosynth);
            uvar_subtyping = (uu___1513_22031.uvar_subtyping);
            tc_term = (uu___1513_22031.tc_term);
            type_of = (uu___1513_22031.type_of);
            universe_of = (uu___1513_22031.universe_of);
            check_type_of = (uu___1513_22031.check_type_of);
            use_bv_sorts = (uu___1513_22031.use_bv_sorts);
            qtbl_name_and_index = (uu___1513_22031.qtbl_name_and_index);
            normalized_eff_names = (uu___1513_22031.normalized_eff_names);
            fv_delta_depths = (uu___1513_22031.fv_delta_depths);
            proof_ns = (uu___1513_22031.proof_ns);
            synth_hook = (uu___1513_22031.synth_hook);
            try_solve_implicits_hook =
              (uu___1513_22031.try_solve_implicits_hook);
            splice = (uu___1513_22031.splice);
            postprocess = (uu___1513_22031.postprocess);
            is_native_tactic = (uu___1513_22031.is_native_tactic);
            identifier_info = (uu___1513_22031.identifier_info);
            tc_hooks = (uu___1513_22031.tc_hooks);
            dsenv = (uu___1513_22031.dsenv);
            nbe = (uu___1513_22031.nbe);
            strict_args_tab = (uu___1513_22031.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____22061 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____22061  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____22219 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____22220 = l1 u t wp e  in
                                l2 u t uu____22219 uu____22220))
                | uu____22221 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____22293 = inst_tscheme_with lift_t [u]  in
            match uu____22293 with
            | (uu____22300,lift_t1) ->
                let uu____22302 =
                  let uu____22309 =
                    let uu____22310 =
                      let uu____22327 =
                        let uu____22338 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____22347 =
                          let uu____22358 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____22358]  in
                        uu____22338 :: uu____22347  in
                      (lift_t1, uu____22327)  in
                    FStar_Syntax_Syntax.Tm_app uu____22310  in
                  FStar_Syntax_Syntax.mk uu____22309  in
                uu____22302 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____22468 = inst_tscheme_with lift_t [u]  in
            match uu____22468 with
            | (uu____22475,lift_t1) ->
                let uu____22477 =
                  let uu____22484 =
                    let uu____22485 =
                      let uu____22502 =
                        let uu____22513 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____22522 =
                          let uu____22533 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____22542 =
                            let uu____22553 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____22553]  in
                          uu____22533 :: uu____22542  in
                        uu____22513 :: uu____22522  in
                      (lift_t1, uu____22502)  in
                    FStar_Syntax_Syntax.Tm_app uu____22485  in
                  FStar_Syntax_Syntax.mk uu____22484  in
                uu____22477 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____22655 =
                let uu____22656 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____22656
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____22655  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____22665 =
              let uu____22667 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____22667  in
            let uu____22668 =
              let uu____22670 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____22698 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____22698)
                 in
              FStar_Util.dflt "none" uu____22670  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22665
              uu____22668
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____22727  ->
                    match uu____22727 with
                    | (e,uu____22735) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____22758 =
            match uu____22758 with
            | (i,j) ->
                let uu____22769 = FStar_Ident.lid_equals i j  in
                if uu____22769
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _22776  -> FStar_Pervasives_Native.Some _22776)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____22805 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____22815 = FStar_Ident.lid_equals i k  in
                        if uu____22815
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____22829 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____22829
                                  then []
                                  else
                                    (let uu____22836 =
                                       let uu____22845 =
                                         find_edge order1 (i, k)  in
                                       let uu____22848 =
                                         find_edge order1 (k, j)  in
                                       (uu____22845, uu____22848)  in
                                     match uu____22836 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____22863 =
                                           compose_edges e1 e2  in
                                         [uu____22863]
                                     | uu____22864 -> [])))))
                 in
              FStar_List.append order1 uu____22805  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____22894 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____22897 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____22897
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____22894
                   then
                     let uu____22904 =
                       let uu____22910 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____22910)
                        in
                     let uu____22914 = get_range env  in
                     FStar_Errors.raise_error uu____22904 uu____22914
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____22992 = FStar_Ident.lid_equals i j
                                   in
                                if uu____22992
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____23044 =
                                              let uu____23053 =
                                                find_edge order2 (i, k)  in
                                              let uu____23056 =
                                                find_edge order2 (j, k)  in
                                              (uu____23053, uu____23056)  in
                                            match uu____23044 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____23098,uu____23099)
                                                     ->
                                                     let uu____23106 =
                                                       let uu____23113 =
                                                         let uu____23115 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____23115
                                                          in
                                                       let uu____23118 =
                                                         let uu____23120 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____23120
                                                          in
                                                       (uu____23113,
                                                         uu____23118)
                                                        in
                                                     (match uu____23106 with
                                                      | (true ,true ) ->
                                                          let uu____23137 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____23137
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
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____23180 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1640_23253 = env.effects  in
              { decls = (uu___1640_23253.decls); order = order2; joins }  in
            let uu___1643_23254 = env  in
            {
              solver = (uu___1643_23254.solver);
              range = (uu___1643_23254.range);
              curmodule = (uu___1643_23254.curmodule);
              gamma = (uu___1643_23254.gamma);
              gamma_sig = (uu___1643_23254.gamma_sig);
              gamma_cache = (uu___1643_23254.gamma_cache);
              modules = (uu___1643_23254.modules);
              expected_typ = (uu___1643_23254.expected_typ);
              sigtab = (uu___1643_23254.sigtab);
              attrtab = (uu___1643_23254.attrtab);
              is_pattern = (uu___1643_23254.is_pattern);
              instantiate_imp = (uu___1643_23254.instantiate_imp);
              effects;
              generalize = (uu___1643_23254.generalize);
              letrecs = (uu___1643_23254.letrecs);
              top_level = (uu___1643_23254.top_level);
              check_uvars = (uu___1643_23254.check_uvars);
              use_eq = (uu___1643_23254.use_eq);
              is_iface = (uu___1643_23254.is_iface);
              admit = (uu___1643_23254.admit);
              lax = (uu___1643_23254.lax);
              lax_universes = (uu___1643_23254.lax_universes);
              phase1 = (uu___1643_23254.phase1);
              failhard = (uu___1643_23254.failhard);
              nosynth = (uu___1643_23254.nosynth);
              uvar_subtyping = (uu___1643_23254.uvar_subtyping);
              tc_term = (uu___1643_23254.tc_term);
              type_of = (uu___1643_23254.type_of);
              universe_of = (uu___1643_23254.universe_of);
              check_type_of = (uu___1643_23254.check_type_of);
              use_bv_sorts = (uu___1643_23254.use_bv_sorts);
              qtbl_name_and_index = (uu___1643_23254.qtbl_name_and_index);
              normalized_eff_names = (uu___1643_23254.normalized_eff_names);
              fv_delta_depths = (uu___1643_23254.fv_delta_depths);
              proof_ns = (uu___1643_23254.proof_ns);
              synth_hook = (uu___1643_23254.synth_hook);
              try_solve_implicits_hook =
                (uu___1643_23254.try_solve_implicits_hook);
              splice = (uu___1643_23254.splice);
              postprocess = (uu___1643_23254.postprocess);
              is_native_tactic = (uu___1643_23254.is_native_tactic);
              identifier_info = (uu___1643_23254.identifier_info);
              tc_hooks = (uu___1643_23254.tc_hooks);
              dsenv = (uu___1643_23254.dsenv);
              nbe = (uu___1643_23254.nbe);
              strict_args_tab = (uu___1643_23254.strict_args_tab)
            }))
      | uu____23255 -> env
  
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
        | uu____23284 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23297 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23297 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23314 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23314 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23339 =
                     let uu____23345 =
                       let uu____23347 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23355 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23366 =
                         let uu____23368 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23368  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23347 uu____23355 uu____23366
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23345)
                      in
                   FStar_Errors.raise_error uu____23339
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23376 =
                     let uu____23387 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23387 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23424  ->
                        fun uu____23425  ->
                          match (uu____23424, uu____23425) with
                          | ((x,uu____23455),(t,uu____23457)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23376
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23488 =
                     let uu___1681_23489 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1681_23489.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1681_23489.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1681_23489.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1681_23489.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23488
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23501 .
    'Auu____23501 ->
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
          let uu____23531 = effect_decl_opt env effect_name  in
          match uu____23531 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____23570 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____23593 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____23632 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____23632
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____23637 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____23637
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____23652 =
                     let uu____23655 = get_range env  in
                     let uu____23656 =
                       let uu____23663 =
                         let uu____23664 =
                           let uu____23681 =
                             let uu____23692 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23692; wp]  in
                           (repr, uu____23681)  in
                         FStar_Syntax_Syntax.Tm_app uu____23664  in
                       FStar_Syntax_Syntax.mk uu____23663  in
                     uu____23656 FStar_Pervasives_Native.None uu____23655  in
                   FStar_Pervasives_Native.Some uu____23652)
  
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
      | uu____23836 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23851 =
        let uu____23852 = FStar_Syntax_Subst.compress t  in
        uu____23852.FStar_Syntax_Syntax.n  in
      match uu____23851 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23856,c) ->
          is_reifiable_comp env c
      | uu____23878 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23898 =
           let uu____23900 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23900  in
         if uu____23898
         then
           let uu____23903 =
             let uu____23909 =
               let uu____23911 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23911
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23909)  in
           let uu____23915 = get_range env  in
           FStar_Errors.raise_error uu____23903 uu____23915
         else ());
        (let uu____23918 = effect_repr_aux true env c u_c  in
         match uu____23918 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1746_23954 = env  in
        {
          solver = (uu___1746_23954.solver);
          range = (uu___1746_23954.range);
          curmodule = (uu___1746_23954.curmodule);
          gamma = (uu___1746_23954.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1746_23954.gamma_cache);
          modules = (uu___1746_23954.modules);
          expected_typ = (uu___1746_23954.expected_typ);
          sigtab = (uu___1746_23954.sigtab);
          attrtab = (uu___1746_23954.attrtab);
          is_pattern = (uu___1746_23954.is_pattern);
          instantiate_imp = (uu___1746_23954.instantiate_imp);
          effects = (uu___1746_23954.effects);
          generalize = (uu___1746_23954.generalize);
          letrecs = (uu___1746_23954.letrecs);
          top_level = (uu___1746_23954.top_level);
          check_uvars = (uu___1746_23954.check_uvars);
          use_eq = (uu___1746_23954.use_eq);
          is_iface = (uu___1746_23954.is_iface);
          admit = (uu___1746_23954.admit);
          lax = (uu___1746_23954.lax);
          lax_universes = (uu___1746_23954.lax_universes);
          phase1 = (uu___1746_23954.phase1);
          failhard = (uu___1746_23954.failhard);
          nosynth = (uu___1746_23954.nosynth);
          uvar_subtyping = (uu___1746_23954.uvar_subtyping);
          tc_term = (uu___1746_23954.tc_term);
          type_of = (uu___1746_23954.type_of);
          universe_of = (uu___1746_23954.universe_of);
          check_type_of = (uu___1746_23954.check_type_of);
          use_bv_sorts = (uu___1746_23954.use_bv_sorts);
          qtbl_name_and_index = (uu___1746_23954.qtbl_name_and_index);
          normalized_eff_names = (uu___1746_23954.normalized_eff_names);
          fv_delta_depths = (uu___1746_23954.fv_delta_depths);
          proof_ns = (uu___1746_23954.proof_ns);
          synth_hook = (uu___1746_23954.synth_hook);
          try_solve_implicits_hook =
            (uu___1746_23954.try_solve_implicits_hook);
          splice = (uu___1746_23954.splice);
          postprocess = (uu___1746_23954.postprocess);
          is_native_tactic = (uu___1746_23954.is_native_tactic);
          identifier_info = (uu___1746_23954.identifier_info);
          tc_hooks = (uu___1746_23954.tc_hooks);
          dsenv = (uu___1746_23954.dsenv);
          nbe = (uu___1746_23954.nbe);
          strict_args_tab = (uu___1746_23954.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1753_23968 = env  in
      {
        solver = (uu___1753_23968.solver);
        range = (uu___1753_23968.range);
        curmodule = (uu___1753_23968.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1753_23968.gamma_sig);
        gamma_cache = (uu___1753_23968.gamma_cache);
        modules = (uu___1753_23968.modules);
        expected_typ = (uu___1753_23968.expected_typ);
        sigtab = (uu___1753_23968.sigtab);
        attrtab = (uu___1753_23968.attrtab);
        is_pattern = (uu___1753_23968.is_pattern);
        instantiate_imp = (uu___1753_23968.instantiate_imp);
        effects = (uu___1753_23968.effects);
        generalize = (uu___1753_23968.generalize);
        letrecs = (uu___1753_23968.letrecs);
        top_level = (uu___1753_23968.top_level);
        check_uvars = (uu___1753_23968.check_uvars);
        use_eq = (uu___1753_23968.use_eq);
        is_iface = (uu___1753_23968.is_iface);
        admit = (uu___1753_23968.admit);
        lax = (uu___1753_23968.lax);
        lax_universes = (uu___1753_23968.lax_universes);
        phase1 = (uu___1753_23968.phase1);
        failhard = (uu___1753_23968.failhard);
        nosynth = (uu___1753_23968.nosynth);
        uvar_subtyping = (uu___1753_23968.uvar_subtyping);
        tc_term = (uu___1753_23968.tc_term);
        type_of = (uu___1753_23968.type_of);
        universe_of = (uu___1753_23968.universe_of);
        check_type_of = (uu___1753_23968.check_type_of);
        use_bv_sorts = (uu___1753_23968.use_bv_sorts);
        qtbl_name_and_index = (uu___1753_23968.qtbl_name_and_index);
        normalized_eff_names = (uu___1753_23968.normalized_eff_names);
        fv_delta_depths = (uu___1753_23968.fv_delta_depths);
        proof_ns = (uu___1753_23968.proof_ns);
        synth_hook = (uu___1753_23968.synth_hook);
        try_solve_implicits_hook = (uu___1753_23968.try_solve_implicits_hook);
        splice = (uu___1753_23968.splice);
        postprocess = (uu___1753_23968.postprocess);
        is_native_tactic = (uu___1753_23968.is_native_tactic);
        identifier_info = (uu___1753_23968.identifier_info);
        tc_hooks = (uu___1753_23968.tc_hooks);
        dsenv = (uu___1753_23968.dsenv);
        nbe = (uu___1753_23968.nbe);
        strict_args_tab = (uu___1753_23968.strict_args_tab)
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
            (let uu___1766_24026 = env  in
             {
               solver = (uu___1766_24026.solver);
               range = (uu___1766_24026.range);
               curmodule = (uu___1766_24026.curmodule);
               gamma = rest;
               gamma_sig = (uu___1766_24026.gamma_sig);
               gamma_cache = (uu___1766_24026.gamma_cache);
               modules = (uu___1766_24026.modules);
               expected_typ = (uu___1766_24026.expected_typ);
               sigtab = (uu___1766_24026.sigtab);
               attrtab = (uu___1766_24026.attrtab);
               is_pattern = (uu___1766_24026.is_pattern);
               instantiate_imp = (uu___1766_24026.instantiate_imp);
               effects = (uu___1766_24026.effects);
               generalize = (uu___1766_24026.generalize);
               letrecs = (uu___1766_24026.letrecs);
               top_level = (uu___1766_24026.top_level);
               check_uvars = (uu___1766_24026.check_uvars);
               use_eq = (uu___1766_24026.use_eq);
               is_iface = (uu___1766_24026.is_iface);
               admit = (uu___1766_24026.admit);
               lax = (uu___1766_24026.lax);
               lax_universes = (uu___1766_24026.lax_universes);
               phase1 = (uu___1766_24026.phase1);
               failhard = (uu___1766_24026.failhard);
               nosynth = (uu___1766_24026.nosynth);
               uvar_subtyping = (uu___1766_24026.uvar_subtyping);
               tc_term = (uu___1766_24026.tc_term);
               type_of = (uu___1766_24026.type_of);
               universe_of = (uu___1766_24026.universe_of);
               check_type_of = (uu___1766_24026.check_type_of);
               use_bv_sorts = (uu___1766_24026.use_bv_sorts);
               qtbl_name_and_index = (uu___1766_24026.qtbl_name_and_index);
               normalized_eff_names = (uu___1766_24026.normalized_eff_names);
               fv_delta_depths = (uu___1766_24026.fv_delta_depths);
               proof_ns = (uu___1766_24026.proof_ns);
               synth_hook = (uu___1766_24026.synth_hook);
               try_solve_implicits_hook =
                 (uu___1766_24026.try_solve_implicits_hook);
               splice = (uu___1766_24026.splice);
               postprocess = (uu___1766_24026.postprocess);
               is_native_tactic = (uu___1766_24026.is_native_tactic);
               identifier_info = (uu___1766_24026.identifier_info);
               tc_hooks = (uu___1766_24026.tc_hooks);
               dsenv = (uu___1766_24026.dsenv);
               nbe = (uu___1766_24026.nbe);
               strict_args_tab = (uu___1766_24026.strict_args_tab)
             }))
    | uu____24027 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24056  ->
             match uu____24056 with | (x,uu____24064) -> push_bv env1 x) env
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
            let uu___1780_24099 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1780_24099.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1780_24099.FStar_Syntax_Syntax.index);
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
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___1791_24141 = env  in
       {
         solver = (uu___1791_24141.solver);
         range = (uu___1791_24141.range);
         curmodule = (uu___1791_24141.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1791_24141.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1791_24141.sigtab);
         attrtab = (uu___1791_24141.attrtab);
         is_pattern = (uu___1791_24141.is_pattern);
         instantiate_imp = (uu___1791_24141.instantiate_imp);
         effects = (uu___1791_24141.effects);
         generalize = (uu___1791_24141.generalize);
         letrecs = (uu___1791_24141.letrecs);
         top_level = (uu___1791_24141.top_level);
         check_uvars = (uu___1791_24141.check_uvars);
         use_eq = (uu___1791_24141.use_eq);
         is_iface = (uu___1791_24141.is_iface);
         admit = (uu___1791_24141.admit);
         lax = (uu___1791_24141.lax);
         lax_universes = (uu___1791_24141.lax_universes);
         phase1 = (uu___1791_24141.phase1);
         failhard = (uu___1791_24141.failhard);
         nosynth = (uu___1791_24141.nosynth);
         uvar_subtyping = (uu___1791_24141.uvar_subtyping);
         tc_term = (uu___1791_24141.tc_term);
         type_of = (uu___1791_24141.type_of);
         universe_of = (uu___1791_24141.universe_of);
         check_type_of = (uu___1791_24141.check_type_of);
         use_bv_sorts = (uu___1791_24141.use_bv_sorts);
         qtbl_name_and_index = (uu___1791_24141.qtbl_name_and_index);
         normalized_eff_names = (uu___1791_24141.normalized_eff_names);
         fv_delta_depths = (uu___1791_24141.fv_delta_depths);
         proof_ns = (uu___1791_24141.proof_ns);
         synth_hook = (uu___1791_24141.synth_hook);
         try_solve_implicits_hook =
           (uu___1791_24141.try_solve_implicits_hook);
         splice = (uu___1791_24141.splice);
         postprocess = (uu___1791_24141.postprocess);
         is_native_tactic = (uu___1791_24141.is_native_tactic);
         identifier_info = (uu___1791_24141.identifier_info);
         tc_hooks = (uu___1791_24141.tc_hooks);
         dsenv = (uu___1791_24141.dsenv);
         nbe = (uu___1791_24141.nbe);
         strict_args_tab = (uu___1791_24141.strict_args_tab)
       })
  
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
        let uu____24185 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24185 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24213 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24213)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1806_24229 = env  in
      {
        solver = (uu___1806_24229.solver);
        range = (uu___1806_24229.range);
        curmodule = (uu___1806_24229.curmodule);
        gamma = (uu___1806_24229.gamma);
        gamma_sig = (uu___1806_24229.gamma_sig);
        gamma_cache = (uu___1806_24229.gamma_cache);
        modules = (uu___1806_24229.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1806_24229.sigtab);
        attrtab = (uu___1806_24229.attrtab);
        is_pattern = (uu___1806_24229.is_pattern);
        instantiate_imp = (uu___1806_24229.instantiate_imp);
        effects = (uu___1806_24229.effects);
        generalize = (uu___1806_24229.generalize);
        letrecs = (uu___1806_24229.letrecs);
        top_level = (uu___1806_24229.top_level);
        check_uvars = (uu___1806_24229.check_uvars);
        use_eq = false;
        is_iface = (uu___1806_24229.is_iface);
        admit = (uu___1806_24229.admit);
        lax = (uu___1806_24229.lax);
        lax_universes = (uu___1806_24229.lax_universes);
        phase1 = (uu___1806_24229.phase1);
        failhard = (uu___1806_24229.failhard);
        nosynth = (uu___1806_24229.nosynth);
        uvar_subtyping = (uu___1806_24229.uvar_subtyping);
        tc_term = (uu___1806_24229.tc_term);
        type_of = (uu___1806_24229.type_of);
        universe_of = (uu___1806_24229.universe_of);
        check_type_of = (uu___1806_24229.check_type_of);
        use_bv_sorts = (uu___1806_24229.use_bv_sorts);
        qtbl_name_and_index = (uu___1806_24229.qtbl_name_and_index);
        normalized_eff_names = (uu___1806_24229.normalized_eff_names);
        fv_delta_depths = (uu___1806_24229.fv_delta_depths);
        proof_ns = (uu___1806_24229.proof_ns);
        synth_hook = (uu___1806_24229.synth_hook);
        try_solve_implicits_hook = (uu___1806_24229.try_solve_implicits_hook);
        splice = (uu___1806_24229.splice);
        postprocess = (uu___1806_24229.postprocess);
        is_native_tactic = (uu___1806_24229.is_native_tactic);
        identifier_info = (uu___1806_24229.identifier_info);
        tc_hooks = (uu___1806_24229.tc_hooks);
        dsenv = (uu___1806_24229.dsenv);
        nbe = (uu___1806_24229.nbe);
        strict_args_tab = (uu___1806_24229.strict_args_tab)
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
    let uu____24260 = expected_typ env_  in
    ((let uu___1813_24266 = env_  in
      {
        solver = (uu___1813_24266.solver);
        range = (uu___1813_24266.range);
        curmodule = (uu___1813_24266.curmodule);
        gamma = (uu___1813_24266.gamma);
        gamma_sig = (uu___1813_24266.gamma_sig);
        gamma_cache = (uu___1813_24266.gamma_cache);
        modules = (uu___1813_24266.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1813_24266.sigtab);
        attrtab = (uu___1813_24266.attrtab);
        is_pattern = (uu___1813_24266.is_pattern);
        instantiate_imp = (uu___1813_24266.instantiate_imp);
        effects = (uu___1813_24266.effects);
        generalize = (uu___1813_24266.generalize);
        letrecs = (uu___1813_24266.letrecs);
        top_level = (uu___1813_24266.top_level);
        check_uvars = (uu___1813_24266.check_uvars);
        use_eq = false;
        is_iface = (uu___1813_24266.is_iface);
        admit = (uu___1813_24266.admit);
        lax = (uu___1813_24266.lax);
        lax_universes = (uu___1813_24266.lax_universes);
        phase1 = (uu___1813_24266.phase1);
        failhard = (uu___1813_24266.failhard);
        nosynth = (uu___1813_24266.nosynth);
        uvar_subtyping = (uu___1813_24266.uvar_subtyping);
        tc_term = (uu___1813_24266.tc_term);
        type_of = (uu___1813_24266.type_of);
        universe_of = (uu___1813_24266.universe_of);
        check_type_of = (uu___1813_24266.check_type_of);
        use_bv_sorts = (uu___1813_24266.use_bv_sorts);
        qtbl_name_and_index = (uu___1813_24266.qtbl_name_and_index);
        normalized_eff_names = (uu___1813_24266.normalized_eff_names);
        fv_delta_depths = (uu___1813_24266.fv_delta_depths);
        proof_ns = (uu___1813_24266.proof_ns);
        synth_hook = (uu___1813_24266.synth_hook);
        try_solve_implicits_hook = (uu___1813_24266.try_solve_implicits_hook);
        splice = (uu___1813_24266.splice);
        postprocess = (uu___1813_24266.postprocess);
        is_native_tactic = (uu___1813_24266.is_native_tactic);
        identifier_info = (uu___1813_24266.identifier_info);
        tc_hooks = (uu___1813_24266.tc_hooks);
        dsenv = (uu___1813_24266.dsenv);
        nbe = (uu___1813_24266.nbe);
        strict_args_tab = (uu___1813_24266.strict_args_tab)
      }), uu____24260)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24278 =
      let uu____24281 = FStar_Ident.id_of_text ""  in [uu____24281]  in
    FStar_Ident.lid_of_ids uu____24278  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24288 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24288
        then
          let uu____24293 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24293 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1821_24321 = env  in
       {
         solver = (uu___1821_24321.solver);
         range = (uu___1821_24321.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1821_24321.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1821_24321.expected_typ);
         sigtab = (uu___1821_24321.sigtab);
         attrtab = (uu___1821_24321.attrtab);
         is_pattern = (uu___1821_24321.is_pattern);
         instantiate_imp = (uu___1821_24321.instantiate_imp);
         effects = (uu___1821_24321.effects);
         generalize = (uu___1821_24321.generalize);
         letrecs = (uu___1821_24321.letrecs);
         top_level = (uu___1821_24321.top_level);
         check_uvars = (uu___1821_24321.check_uvars);
         use_eq = (uu___1821_24321.use_eq);
         is_iface = (uu___1821_24321.is_iface);
         admit = (uu___1821_24321.admit);
         lax = (uu___1821_24321.lax);
         lax_universes = (uu___1821_24321.lax_universes);
         phase1 = (uu___1821_24321.phase1);
         failhard = (uu___1821_24321.failhard);
         nosynth = (uu___1821_24321.nosynth);
         uvar_subtyping = (uu___1821_24321.uvar_subtyping);
         tc_term = (uu___1821_24321.tc_term);
         type_of = (uu___1821_24321.type_of);
         universe_of = (uu___1821_24321.universe_of);
         check_type_of = (uu___1821_24321.check_type_of);
         use_bv_sorts = (uu___1821_24321.use_bv_sorts);
         qtbl_name_and_index = (uu___1821_24321.qtbl_name_and_index);
         normalized_eff_names = (uu___1821_24321.normalized_eff_names);
         fv_delta_depths = (uu___1821_24321.fv_delta_depths);
         proof_ns = (uu___1821_24321.proof_ns);
         synth_hook = (uu___1821_24321.synth_hook);
         try_solve_implicits_hook =
           (uu___1821_24321.try_solve_implicits_hook);
         splice = (uu___1821_24321.splice);
         postprocess = (uu___1821_24321.postprocess);
         is_native_tactic = (uu___1821_24321.is_native_tactic);
         identifier_info = (uu___1821_24321.identifier_info);
         tc_hooks = (uu___1821_24321.tc_hooks);
         dsenv = (uu___1821_24321.dsenv);
         nbe = (uu___1821_24321.nbe);
         strict_args_tab = (uu___1821_24321.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24373)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24377,(uu____24378,t)))::tl1
          ->
          let uu____24399 =
            let uu____24402 = FStar_Syntax_Free.uvars t  in
            ext out uu____24402  in
          aux uu____24399 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24405;
            FStar_Syntax_Syntax.index = uu____24406;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24414 =
            let uu____24417 = FStar_Syntax_Free.uvars t  in
            ext out uu____24417  in
          aux uu____24414 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24475)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24479,(uu____24480,t)))::tl1
          ->
          let uu____24501 =
            let uu____24504 = FStar_Syntax_Free.univs t  in
            ext out uu____24504  in
          aux uu____24501 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24507;
            FStar_Syntax_Syntax.index = uu____24508;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24516 =
            let uu____24519 = FStar_Syntax_Free.univs t  in
            ext out uu____24519  in
          aux uu____24516 tl1
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
          let uu____24581 = FStar_Util.set_add uname out  in
          aux uu____24581 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24584,(uu____24585,t)))::tl1
          ->
          let uu____24606 =
            let uu____24609 = FStar_Syntax_Free.univnames t  in
            ext out uu____24609  in
          aux uu____24606 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24612;
            FStar_Syntax_Syntax.index = uu____24613;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24621 =
            let uu____24624 = FStar_Syntax_Free.univnames t  in
            ext out uu____24624  in
          aux uu____24621 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24645  ->
            match uu___11_24645 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24649 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24662 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24673 =
      let uu____24682 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24682
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24673 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24730 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24743  ->
              match uu___12_24743 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24746 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24746
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24752) ->
                  let uu____24769 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24769))
       in
    FStar_All.pipe_right uu____24730 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24783  ->
    match uu___13_24783 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24789 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24789
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24812  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24867) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24900,uu____24901) -> false  in
      let uu____24915 =
        FStar_List.tryFind
          (fun uu____24937  ->
             match uu____24937 with | (p,uu____24948) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24915 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24967,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24997 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24997
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1964_25019 = e  in
        {
          solver = (uu___1964_25019.solver);
          range = (uu___1964_25019.range);
          curmodule = (uu___1964_25019.curmodule);
          gamma = (uu___1964_25019.gamma);
          gamma_sig = (uu___1964_25019.gamma_sig);
          gamma_cache = (uu___1964_25019.gamma_cache);
          modules = (uu___1964_25019.modules);
          expected_typ = (uu___1964_25019.expected_typ);
          sigtab = (uu___1964_25019.sigtab);
          attrtab = (uu___1964_25019.attrtab);
          is_pattern = (uu___1964_25019.is_pattern);
          instantiate_imp = (uu___1964_25019.instantiate_imp);
          effects = (uu___1964_25019.effects);
          generalize = (uu___1964_25019.generalize);
          letrecs = (uu___1964_25019.letrecs);
          top_level = (uu___1964_25019.top_level);
          check_uvars = (uu___1964_25019.check_uvars);
          use_eq = (uu___1964_25019.use_eq);
          is_iface = (uu___1964_25019.is_iface);
          admit = (uu___1964_25019.admit);
          lax = (uu___1964_25019.lax);
          lax_universes = (uu___1964_25019.lax_universes);
          phase1 = (uu___1964_25019.phase1);
          failhard = (uu___1964_25019.failhard);
          nosynth = (uu___1964_25019.nosynth);
          uvar_subtyping = (uu___1964_25019.uvar_subtyping);
          tc_term = (uu___1964_25019.tc_term);
          type_of = (uu___1964_25019.type_of);
          universe_of = (uu___1964_25019.universe_of);
          check_type_of = (uu___1964_25019.check_type_of);
          use_bv_sorts = (uu___1964_25019.use_bv_sorts);
          qtbl_name_and_index = (uu___1964_25019.qtbl_name_and_index);
          normalized_eff_names = (uu___1964_25019.normalized_eff_names);
          fv_delta_depths = (uu___1964_25019.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1964_25019.synth_hook);
          try_solve_implicits_hook =
            (uu___1964_25019.try_solve_implicits_hook);
          splice = (uu___1964_25019.splice);
          postprocess = (uu___1964_25019.postprocess);
          is_native_tactic = (uu___1964_25019.is_native_tactic);
          identifier_info = (uu___1964_25019.identifier_info);
          tc_hooks = (uu___1964_25019.tc_hooks);
          dsenv = (uu___1964_25019.dsenv);
          nbe = (uu___1964_25019.nbe);
          strict_args_tab = (uu___1964_25019.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1973_25067 = e  in
      {
        solver = (uu___1973_25067.solver);
        range = (uu___1973_25067.range);
        curmodule = (uu___1973_25067.curmodule);
        gamma = (uu___1973_25067.gamma);
        gamma_sig = (uu___1973_25067.gamma_sig);
        gamma_cache = (uu___1973_25067.gamma_cache);
        modules = (uu___1973_25067.modules);
        expected_typ = (uu___1973_25067.expected_typ);
        sigtab = (uu___1973_25067.sigtab);
        attrtab = (uu___1973_25067.attrtab);
        is_pattern = (uu___1973_25067.is_pattern);
        instantiate_imp = (uu___1973_25067.instantiate_imp);
        effects = (uu___1973_25067.effects);
        generalize = (uu___1973_25067.generalize);
        letrecs = (uu___1973_25067.letrecs);
        top_level = (uu___1973_25067.top_level);
        check_uvars = (uu___1973_25067.check_uvars);
        use_eq = (uu___1973_25067.use_eq);
        is_iface = (uu___1973_25067.is_iface);
        admit = (uu___1973_25067.admit);
        lax = (uu___1973_25067.lax);
        lax_universes = (uu___1973_25067.lax_universes);
        phase1 = (uu___1973_25067.phase1);
        failhard = (uu___1973_25067.failhard);
        nosynth = (uu___1973_25067.nosynth);
        uvar_subtyping = (uu___1973_25067.uvar_subtyping);
        tc_term = (uu___1973_25067.tc_term);
        type_of = (uu___1973_25067.type_of);
        universe_of = (uu___1973_25067.universe_of);
        check_type_of = (uu___1973_25067.check_type_of);
        use_bv_sorts = (uu___1973_25067.use_bv_sorts);
        qtbl_name_and_index = (uu___1973_25067.qtbl_name_and_index);
        normalized_eff_names = (uu___1973_25067.normalized_eff_names);
        fv_delta_depths = (uu___1973_25067.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1973_25067.synth_hook);
        try_solve_implicits_hook = (uu___1973_25067.try_solve_implicits_hook);
        splice = (uu___1973_25067.splice);
        postprocess = (uu___1973_25067.postprocess);
        is_native_tactic = (uu___1973_25067.is_native_tactic);
        identifier_info = (uu___1973_25067.identifier_info);
        tc_hooks = (uu___1973_25067.tc_hooks);
        dsenv = (uu___1973_25067.dsenv);
        nbe = (uu___1973_25067.nbe);
        strict_args_tab = (uu___1973_25067.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25083 = FStar_Syntax_Free.names t  in
      let uu____25086 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25083 uu____25086
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25109 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25109
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25119 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25119
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25140 =
      match uu____25140 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25160 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25160)
       in
    let uu____25168 =
      let uu____25172 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25172 FStar_List.rev  in
    FStar_All.pipe_right uu____25168 (FStar_String.concat " ")
  
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
                  (let uu____25242 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25242 with
                   | FStar_Pervasives_Native.Some uu____25246 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25249 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____25259;
        univ_ineqs = uu____25260; implicits = uu____25261;_} -> true
    | uu____25273 -> false
  
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
          let uu___2017_25304 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2017_25304.deferred);
            univ_ineqs = (uu___2017_25304.univ_ineqs);
            implicits = (uu___2017_25304.implicits)
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
          let uu____25343 = FStar_Options.defensive ()  in
          if uu____25343
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25349 =
              let uu____25351 =
                let uu____25353 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25353  in
              Prims.op_Negation uu____25351  in
            (if uu____25349
             then
               let uu____25360 =
                 let uu____25366 =
                   let uu____25368 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25370 =
                     let uu____25372 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25372
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25368 uu____25370
                    in
                 (FStar_Errors.Warning_Defensive, uu____25366)  in
               FStar_Errors.log_issue rng uu____25360
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
          let uu____25412 =
            let uu____25414 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25414  in
          if uu____25412
          then ()
          else
            (let uu____25419 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25419 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25445 =
            let uu____25447 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25447  in
          if uu____25445
          then ()
          else
            (let uu____25452 = bound_vars e  in
             def_check_closed_in rng msg uu____25452 t)
  
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
          let uu___2054_25491 = g  in
          let uu____25492 =
            let uu____25493 =
              let uu____25494 =
                let uu____25501 =
                  let uu____25502 =
                    let uu____25519 =
                      let uu____25530 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25530]  in
                    (f, uu____25519)  in
                  FStar_Syntax_Syntax.Tm_app uu____25502  in
                FStar_Syntax_Syntax.mk uu____25501  in
              uu____25494 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25567  -> FStar_TypeChecker_Common.NonTrivial _25567)
              uu____25493
             in
          {
            guard_f = uu____25492;
            deferred = (uu___2054_25491.deferred);
            univ_ineqs = (uu___2054_25491.univ_ineqs);
            implicits = (uu___2054_25491.implicits)
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
          let uu___2061_25585 = g  in
          let uu____25586 =
            let uu____25587 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25587  in
          {
            guard_f = uu____25586;
            deferred = (uu___2061_25585.deferred);
            univ_ineqs = (uu___2061_25585.univ_ineqs);
            implicits = (uu___2061_25585.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2066_25604 = g  in
          let uu____25605 =
            let uu____25606 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25606  in
          {
            guard_f = uu____25605;
            deferred = (uu___2066_25604.deferred);
            univ_ineqs = (uu___2066_25604.univ_ineqs);
            implicits = (uu___2066_25604.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2070_25608 = g  in
          let uu____25609 =
            let uu____25610 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25610  in
          {
            guard_f = uu____25609;
            deferred = (uu___2070_25608.deferred);
            univ_ineqs = (uu___2070_25608.univ_ineqs);
            implicits = (uu___2070_25608.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25617 ->
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
          let uu____25634 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25634
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25641 =
      let uu____25642 = FStar_Syntax_Util.unmeta t  in
      uu____25642.FStar_Syntax_Syntax.n  in
    match uu____25641 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25646 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25689 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25689;
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
                       let uu____25784 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25784
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2125_25791 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2125_25791.deferred);
              univ_ineqs = (uu___2125_25791.univ_ineqs);
              implicits = (uu___2125_25791.implicits)
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
               let uu____25825 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25825
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
            let uu___2140_25852 = g  in
            let uu____25853 =
              let uu____25854 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25854  in
            {
              guard_f = uu____25853;
              deferred = (uu___2140_25852.deferred);
              univ_ineqs = (uu___2140_25852.univ_ineqs);
              implicits = (uu___2140_25852.implicits)
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
              let uu____25912 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25912 with
              | FStar_Pervasives_Native.Some
                  (uu____25937::(tm,uu____25939)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26003 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26021 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26021;
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
                      let uu___2162_26053 = trivial_guard  in
                      {
                        guard_f = (uu___2162_26053.guard_f);
                        deferred = (uu___2162_26053.deferred);
                        univ_ineqs = (uu___2162_26053.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26071  -> ());
    push = (fun uu____26073  -> ());
    pop = (fun uu____26076  -> ());
    snapshot =
      (fun uu____26079  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26098  -> fun uu____26099  -> ());
    encode_sig = (fun uu____26114  -> fun uu____26115  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26121 =
             let uu____26128 = FStar_Options.peek ()  in (e, g, uu____26128)
              in
           [uu____26121]);
    solve = (fun uu____26144  -> fun uu____26145  -> fun uu____26146  -> ());
    finish = (fun uu____26153  -> ());
    refresh = (fun uu____26155  -> ())
  } 