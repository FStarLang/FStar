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
      let inst_tscheme1 us_opt1 ts =
        match us_opt1 with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____17170 =
            match us_opt with
            | FStar_Pervasives_Native.None  ->
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.Some us ->
                if
                  (FStar_List.length us) <>
                    ((FStar_List.length ne.FStar_Syntax_Syntax.univs) +
                       (FStar_List.length
                          (FStar_Pervasives_Native.fst
                             ne.FStar_Syntax_Syntax.signature)))
                then
                  let uu____17206 =
                    let uu____17208 =
                      let uu____17210 =
                        let uu____17212 =
                          let uu____17214 =
                            FStar_Util.string_of_int
                              ((FStar_List.length
                                  ne.FStar_Syntax_Syntax.univs)
                                 +
                                 (FStar_List.length
                                    (FStar_Pervasives_Native.fst
                                       ne.FStar_Syntax_Syntax.signature)))
                             in
                          let uu____17220 =
                            let uu____17222 =
                              FStar_Util.string_of_int (FStar_List.length us)
                               in
                            Prims.op_Hat ", got " uu____17222  in
                          Prims.op_Hat uu____17214 uu____17220  in
                        Prims.op_Hat ", expected " uu____17212  in
                      Prims.op_Hat
                        (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                        uu____17210
                       in
                    Prims.op_Hat
                      "effect_signature: insufficient number of universes for the signature of "
                      uu____17208
                     in
                  failwith uu____17206
                else
                  (let uu____17237 =
                     FStar_List.splitAt
                       (FStar_List.length ne.FStar_Syntax_Syntax.univs) us
                      in
                   match uu____17237 with
                   | (ne_us,sig_us) ->
                       ((FStar_Pervasives_Native.Some ne_us),
                         (FStar_Pervasives_Native.Some sig_us)))
             in
          (match uu____17170 with
           | (ne_us,sig_us) ->
               let uu____17288 =
                 inst_tscheme1 sig_us ne.FStar_Syntax_Syntax.signature  in
               (match uu____17288 with
                | (sig_us1,signature_t) ->
                    let uu____17305 =
                      let uu____17310 =
                        let uu____17311 =
                          let uu____17314 =
                            FStar_Syntax_Syntax.mk_Total signature_t  in
                          FStar_Syntax_Util.arrow
                            ne.FStar_Syntax_Syntax.binders uu____17314
                           in
                        ((ne.FStar_Syntax_Syntax.univs), uu____17311)  in
                      inst_tscheme1 ne_us uu____17310  in
                    (match uu____17305 with
                     | (ne_us1,signature_t1) ->
                         FStar_Pervasives_Native.Some
                           (((FStar_List.append ne_us1 sig_us1),
                              signature_t1), (se.FStar_Syntax_Syntax.sigrng)))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____17348,uu____17349) ->
          let uu____17354 =
            let uu____17363 =
              let uu____17368 =
                let uu____17369 =
                  let uu____17372 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____17372  in
                (us, uu____17369)  in
              inst_tscheme1 us_opt uu____17368  in
            (uu____17363, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____17354
      | uu____17391 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17480 =
          match uu____17480 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17576,uvs,t,uu____17579,uu____17580,uu____17581);
                      FStar_Syntax_Syntax.sigrng = uu____17582;
                      FStar_Syntax_Syntax.sigquals = uu____17583;
                      FStar_Syntax_Syntax.sigmeta = uu____17584;
                      FStar_Syntax_Syntax.sigattrs = uu____17585;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17608 =
                     let uu____17617 = inst_tscheme1 (uvs, t)  in
                     (uu____17617, rng)  in
                   FStar_Pervasives_Native.Some uu____17608
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17641;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17643;
                      FStar_Syntax_Syntax.sigattrs = uu____17644;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17661 =
                     let uu____17663 = in_cur_mod env l  in uu____17663 = Yes
                      in
                   if uu____17661
                   then
                     let uu____17675 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17675
                      then
                        let uu____17691 =
                          let uu____17700 = inst_tscheme1 (uvs, t)  in
                          (uu____17700, rng)  in
                        FStar_Pervasives_Native.Some uu____17691
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17733 =
                        let uu____17742 = inst_tscheme1 (uvs, t)  in
                        (uu____17742, rng)  in
                      FStar_Pervasives_Native.Some uu____17733)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17767,uu____17768);
                      FStar_Syntax_Syntax.sigrng = uu____17769;
                      FStar_Syntax_Syntax.sigquals = uu____17770;
                      FStar_Syntax_Syntax.sigmeta = uu____17771;
                      FStar_Syntax_Syntax.sigattrs = uu____17772;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17813 =
                          let uu____17822 = inst_tscheme1 (uvs, k)  in
                          (uu____17822, rng)  in
                        FStar_Pervasives_Native.Some uu____17813
                    | uu____17843 ->
                        let uu____17844 =
                          let uu____17853 =
                            let uu____17858 =
                              let uu____17859 =
                                let uu____17862 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17862
                                 in
                              (uvs, uu____17859)  in
                            inst_tscheme1 uu____17858  in
                          (uu____17853, rng)  in
                        FStar_Pervasives_Native.Some uu____17844)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17885,uu____17886);
                      FStar_Syntax_Syntax.sigrng = uu____17887;
                      FStar_Syntax_Syntax.sigquals = uu____17888;
                      FStar_Syntax_Syntax.sigmeta = uu____17889;
                      FStar_Syntax_Syntax.sigattrs = uu____17890;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17932 =
                          let uu____17941 = inst_tscheme_with (uvs, k) us  in
                          (uu____17941, rng)  in
                        FStar_Pervasives_Native.Some uu____17932
                    | uu____17962 ->
                        let uu____17963 =
                          let uu____17972 =
                            let uu____17977 =
                              let uu____17978 =
                                let uu____17981 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17981
                                 in
                              (uvs, uu____17978)  in
                            inst_tscheme_with uu____17977 us  in
                          (uu____17972, rng)  in
                        FStar_Pervasives_Native.Some uu____17963)
               | FStar_Util.Inr se ->
                   let uu____18017 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18038;
                          FStar_Syntax_Syntax.sigrng = uu____18039;
                          FStar_Syntax_Syntax.sigquals = uu____18040;
                          FStar_Syntax_Syntax.sigmeta = uu____18041;
                          FStar_Syntax_Syntax.sigattrs = uu____18042;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18057 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____18017
                     (FStar_Util.map_option
                        (fun uu____18105  ->
                           match uu____18105 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18136 =
          let uu____18147 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18147 mapper  in
        match uu____18136 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18221 =
              let uu____18232 =
                let uu____18239 =
                  let uu___870_18242 = t  in
                  let uu____18243 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___870_18242.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18243;
                    FStar_Syntax_Syntax.vars =
                      (uu___870_18242.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18239)  in
              (uu____18232, r)  in
            FStar_Pervasives_Native.Some uu____18221
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18292 = lookup_qname env l  in
      match uu____18292 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18313 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18367 = try_lookup_bv env bv  in
      match uu____18367 with
      | FStar_Pervasives_Native.None  ->
          let uu____18382 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18382 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18398 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18399 =
            let uu____18400 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18400  in
          (uu____18398, uu____18399)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18422 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18422 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18488 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18488  in
          let uu____18489 =
            let uu____18498 =
              let uu____18503 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18503)  in
            (uu____18498, r1)  in
          FStar_Pervasives_Native.Some uu____18489
  
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
        let uu____18538 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18538 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18571,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18596 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18596  in
            let uu____18597 =
              let uu____18602 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18602, r1)  in
            FStar_Pervasives_Native.Some uu____18597
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18626 = try_lookup_lid env l  in
      match uu____18626 with
      | FStar_Pervasives_Native.None  ->
          let uu____18653 = name_not_found l  in
          let uu____18659 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18653 uu____18659
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18702  ->
              match uu___5_18702 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18706 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18727 = lookup_qname env lid  in
      match uu____18727 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18736,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18739;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18741;
              FStar_Syntax_Syntax.sigattrs = uu____18742;_},FStar_Pervasives_Native.None
            ),uu____18743)
          ->
          let uu____18792 =
            let uu____18799 =
              let uu____18800 =
                let uu____18803 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18803 t  in
              (uvs, uu____18800)  in
            (uu____18799, q)  in
          FStar_Pervasives_Native.Some uu____18792
      | uu____18816 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18838 = lookup_qname env lid  in
      match uu____18838 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18843,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18846;
              FStar_Syntax_Syntax.sigquals = uu____18847;
              FStar_Syntax_Syntax.sigmeta = uu____18848;
              FStar_Syntax_Syntax.sigattrs = uu____18849;_},FStar_Pervasives_Native.None
            ),uu____18850)
          ->
          let uu____18899 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18899 (uvs, t)
      | uu____18904 ->
          let uu____18905 = name_not_found lid  in
          let uu____18911 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18905 uu____18911
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18931 = lookup_qname env lid  in
      match uu____18931 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18936,uvs,t,uu____18939,uu____18940,uu____18941);
              FStar_Syntax_Syntax.sigrng = uu____18942;
              FStar_Syntax_Syntax.sigquals = uu____18943;
              FStar_Syntax_Syntax.sigmeta = uu____18944;
              FStar_Syntax_Syntax.sigattrs = uu____18945;_},FStar_Pervasives_Native.None
            ),uu____18946)
          ->
          let uu____19001 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19001 (uvs, t)
      | uu____19006 ->
          let uu____19007 = name_not_found lid  in
          let uu____19013 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19007 uu____19013
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19036 = lookup_qname env lid  in
      match uu____19036 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19044,uu____19045,uu____19046,uu____19047,uu____19048,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19050;
              FStar_Syntax_Syntax.sigquals = uu____19051;
              FStar_Syntax_Syntax.sigmeta = uu____19052;
              FStar_Syntax_Syntax.sigattrs = uu____19053;_},uu____19054),uu____19055)
          -> (true, dcs)
      | uu____19118 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19134 = lookup_qname env lid  in
      match uu____19134 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19135,uu____19136,uu____19137,l,uu____19139,uu____19140);
              FStar_Syntax_Syntax.sigrng = uu____19141;
              FStar_Syntax_Syntax.sigquals = uu____19142;
              FStar_Syntax_Syntax.sigmeta = uu____19143;
              FStar_Syntax_Syntax.sigattrs = uu____19144;_},uu____19145),uu____19146)
          -> l
      | uu____19203 ->
          let uu____19204 =
            let uu____19206 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19206  in
          failwith uu____19204
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19276)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19333) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19357 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19357
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19392 -> FStar_Pervasives_Native.None)
          | uu____19401 -> FStar_Pervasives_Native.None
  
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
        let uu____19463 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19463
  
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
        let uu____19496 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19496
  
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
             (FStar_Util.Inl uu____19548,uu____19549) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19598),uu____19599) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19648 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19666 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19676 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19693 ->
                  let uu____19700 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19700
              | FStar_Syntax_Syntax.Sig_let ((uu____19701,lbs),uu____19703)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19719 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19719
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19726 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19734 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19735 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19742 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19743 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19744 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19745 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19758 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19776 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19776
           (fun d_opt  ->
              let uu____19789 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19789
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19799 =
                   let uu____19802 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19802  in
                 match uu____19799 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19803 =
                       let uu____19805 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19805
                        in
                     failwith uu____19803
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19810 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19810
                       then
                         let uu____19813 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19815 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19817 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19813 uu____19815 uu____19817
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
        (FStar_Util.Inr (se,uu____19842),uu____19843) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19892 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19914),uu____19915) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19964 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19986 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19986
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20009 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20009 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____20033 =
                      let uu____20034 = FStar_Syntax_Util.un_uinst tm  in
                      uu____20034.FStar_Syntax_Syntax.n  in
                    match uu____20033 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____20039 -> false))
  
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
        let uu____20076 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____20076.FStar_Ident.str  in
      let uu____20077 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____20077 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____20105 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____20105  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____20133 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____20133)
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
      let uu____20183 = lookup_qname env ftv  in
      match uu____20183 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20187) ->
          let uu____20232 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____20232 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20253,t),r) ->
               let uu____20268 =
                 let uu____20269 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20269 t  in
               FStar_Pervasives_Native.Some uu____20268)
      | uu____20270 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20282 = try_lookup_effect_lid env ftv  in
      match uu____20282 with
      | FStar_Pervasives_Native.None  ->
          let uu____20285 = name_not_found ftv  in
          let uu____20291 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20285 uu____20291
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
        let uu____20315 = lookup_qname env lid0  in
        match uu____20315 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20326);
                FStar_Syntax_Syntax.sigrng = uu____20327;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20329;
                FStar_Syntax_Syntax.sigattrs = uu____20330;_},FStar_Pervasives_Native.None
              ),uu____20331)
            ->
            let lid1 =
              let uu____20385 =
                let uu____20386 = FStar_Ident.range_of_lid lid  in
                let uu____20387 =
                  let uu____20388 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20388  in
                FStar_Range.set_use_range uu____20386 uu____20387  in
              FStar_Ident.set_lid_range lid uu____20385  in
            let uu____20389 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20395  ->
                      match uu___6_20395 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20398 -> false))
               in
            if uu____20389
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20417 =
                      let uu____20419 =
                        let uu____20421 = get_range env  in
                        FStar_Range.string_of_range uu____20421  in
                      let uu____20422 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20424 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20419 uu____20422 uu____20424
                       in
                    failwith uu____20417)
                  in
               match (binders, univs1) with
               | ([],uu____20445) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20471,uu____20472::uu____20473::uu____20474) ->
                   let uu____20495 =
                     let uu____20497 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20499 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20497 uu____20499
                      in
                   failwith uu____20495
               | uu____20510 ->
                   let uu____20525 =
                     let uu____20530 =
                       let uu____20531 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20531)  in
                     inst_tscheme_with uu____20530 insts  in
                   (match uu____20525 with
                    | (uu____20544,t) ->
                        let t1 =
                          let uu____20547 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20547 t  in
                        let uu____20548 =
                          let uu____20549 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20549.FStar_Syntax_Syntax.n  in
                        (match uu____20548 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20584 -> failwith "Impossible")))
        | uu____20592 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20616 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20616 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20629,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20636 = find1 l2  in
            (match uu____20636 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20643 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20643 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20647 = find1 l  in
            (match uu____20647 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20652 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20652
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20667 = lookup_qname env l1  in
      match uu____20667 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20670;
              FStar_Syntax_Syntax.sigrng = uu____20671;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20673;
              FStar_Syntax_Syntax.sigattrs = uu____20674;_},uu____20675),uu____20676)
          -> q
      | uu____20727 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20751 =
          let uu____20752 =
            let uu____20754 = FStar_Util.string_of_int i  in
            let uu____20756 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20754 uu____20756
             in
          failwith uu____20752  in
        let uu____20759 = lookup_datacon env lid  in
        match uu____20759 with
        | (uu____20764,t) ->
            let uu____20766 =
              let uu____20767 = FStar_Syntax_Subst.compress t  in
              uu____20767.FStar_Syntax_Syntax.n  in
            (match uu____20766 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20771) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20815 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20815
                      FStar_Pervasives_Native.fst)
             | uu____20826 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20840 = lookup_qname env l  in
      match uu____20840 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20842,uu____20843,uu____20844);
              FStar_Syntax_Syntax.sigrng = uu____20845;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20847;
              FStar_Syntax_Syntax.sigattrs = uu____20848;_},uu____20849),uu____20850)
          ->
          FStar_Util.for_some
            (fun uu___7_20903  ->
               match uu___7_20903 with
               | FStar_Syntax_Syntax.Projector uu____20905 -> true
               | uu____20911 -> false) quals
      | uu____20913 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20927 = lookup_qname env lid  in
      match uu____20927 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20929,uu____20930,uu____20931,uu____20932,uu____20933,uu____20934);
              FStar_Syntax_Syntax.sigrng = uu____20935;
              FStar_Syntax_Syntax.sigquals = uu____20936;
              FStar_Syntax_Syntax.sigmeta = uu____20937;
              FStar_Syntax_Syntax.sigattrs = uu____20938;_},uu____20939),uu____20940)
          -> true
      | uu____20998 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21012 = lookup_qname env lid  in
      match uu____21012 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21014,uu____21015,uu____21016,uu____21017,uu____21018,uu____21019);
              FStar_Syntax_Syntax.sigrng = uu____21020;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21022;
              FStar_Syntax_Syntax.sigattrs = uu____21023;_},uu____21024),uu____21025)
          ->
          FStar_Util.for_some
            (fun uu___8_21086  ->
               match uu___8_21086 with
               | FStar_Syntax_Syntax.RecordType uu____21088 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21098 -> true
               | uu____21108 -> false) quals
      | uu____21110 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21120,uu____21121);
            FStar_Syntax_Syntax.sigrng = uu____21122;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21124;
            FStar_Syntax_Syntax.sigattrs = uu____21125;_},uu____21126),uu____21127)
        ->
        FStar_Util.for_some
          (fun uu___9_21184  ->
             match uu___9_21184 with
             | FStar_Syntax_Syntax.Action uu____21186 -> true
             | uu____21188 -> false) quals
    | uu____21190 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21204 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21204
  
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
      let uu____21221 =
        let uu____21222 = FStar_Syntax_Util.un_uinst head1  in
        uu____21222.FStar_Syntax_Syntax.n  in
      match uu____21221 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21228 ->
               true
           | uu____21231 -> false)
      | uu____21233 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21247 = lookup_qname env l  in
      match uu____21247 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21250),uu____21251) ->
          FStar_Util.for_some
            (fun uu___10_21299  ->
               match uu___10_21299 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21302 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21304 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21380 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21398) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21416 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21424 ->
                 FStar_Pervasives_Native.Some true
             | uu____21443 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21446 =
        let uu____21450 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21450 mapper  in
      match uu____21446 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21510 = lookup_qname env lid  in
      match uu____21510 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21514,uu____21515,tps,uu____21517,uu____21518,uu____21519);
              FStar_Syntax_Syntax.sigrng = uu____21520;
              FStar_Syntax_Syntax.sigquals = uu____21521;
              FStar_Syntax_Syntax.sigmeta = uu____21522;
              FStar_Syntax_Syntax.sigattrs = uu____21523;_},uu____21524),uu____21525)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21591 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21637  ->
              match uu____21637 with
              | (d,uu____21646) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21662 = effect_decl_opt env l  in
      match uu____21662 with
      | FStar_Pervasives_Native.None  ->
          let uu____21677 = name_not_found l  in
          let uu____21683 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21677 uu____21683
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21706  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21725  ->
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
        let uu____21757 = FStar_Ident.lid_equals l1 l2  in
        if uu____21757
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21768 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21768
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21779 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21832  ->
                        match uu____21832 with
                        | (m1,m2,uu____21846,uu____21847,uu____21848) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21779 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21865 =
                    let uu____21871 =
                      let uu____21873 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21875 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21873
                        uu____21875
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21871)
                     in
                  FStar_Errors.raise_error uu____21865 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21885,uu____21886,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21920 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21920
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
  'Auu____21940 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21940) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21969 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21995  ->
                match uu____21995 with
                | (d,uu____22002) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21969 with
      | FStar_Pervasives_Native.None  ->
          let uu____22013 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22013
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22028 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22028 with
           | (uu____22039,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22057)::(wp,uu____22059)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22115 -> failwith "Impossible"))
  
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
            let uu___1527_22165 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1527_22165.order);
              joins = (uu___1527_22165.joins)
            }  in
          let uu___1530_22174 = env  in
          {
            solver = (uu___1530_22174.solver);
            range = (uu___1530_22174.range);
            curmodule = (uu___1530_22174.curmodule);
            gamma = (uu___1530_22174.gamma);
            gamma_sig = (uu___1530_22174.gamma_sig);
            gamma_cache = (uu___1530_22174.gamma_cache);
            modules = (uu___1530_22174.modules);
            expected_typ = (uu___1530_22174.expected_typ);
            sigtab = (uu___1530_22174.sigtab);
            attrtab = (uu___1530_22174.attrtab);
            is_pattern = (uu___1530_22174.is_pattern);
            instantiate_imp = (uu___1530_22174.instantiate_imp);
            effects;
            generalize = (uu___1530_22174.generalize);
            letrecs = (uu___1530_22174.letrecs);
            top_level = (uu___1530_22174.top_level);
            check_uvars = (uu___1530_22174.check_uvars);
            use_eq = (uu___1530_22174.use_eq);
            is_iface = (uu___1530_22174.is_iface);
            admit = (uu___1530_22174.admit);
            lax = (uu___1530_22174.lax);
            lax_universes = (uu___1530_22174.lax_universes);
            phase1 = (uu___1530_22174.phase1);
            failhard = (uu___1530_22174.failhard);
            nosynth = (uu___1530_22174.nosynth);
            uvar_subtyping = (uu___1530_22174.uvar_subtyping);
            tc_term = (uu___1530_22174.tc_term);
            type_of = (uu___1530_22174.type_of);
            universe_of = (uu___1530_22174.universe_of);
            check_type_of = (uu___1530_22174.check_type_of);
            use_bv_sorts = (uu___1530_22174.use_bv_sorts);
            qtbl_name_and_index = (uu___1530_22174.qtbl_name_and_index);
            normalized_eff_names = (uu___1530_22174.normalized_eff_names);
            fv_delta_depths = (uu___1530_22174.fv_delta_depths);
            proof_ns = (uu___1530_22174.proof_ns);
            synth_hook = (uu___1530_22174.synth_hook);
            try_solve_implicits_hook =
              (uu___1530_22174.try_solve_implicits_hook);
            splice = (uu___1530_22174.splice);
            postprocess = (uu___1530_22174.postprocess);
            is_native_tactic = (uu___1530_22174.is_native_tactic);
            identifier_info = (uu___1530_22174.identifier_info);
            tc_hooks = (uu___1530_22174.tc_hooks);
            dsenv = (uu___1530_22174.dsenv);
            nbe = (uu___1530_22174.nbe);
            strict_args_tab = (uu___1530_22174.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____22204 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____22204  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____22362 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____22363 = l1 u t wp e  in
                                l2 u t uu____22362 uu____22363))
                | uu____22364 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____22436 = inst_tscheme_with lift_t [u]  in
            match uu____22436 with
            | (uu____22443,lift_t1) ->
                let uu____22445 =
                  let uu____22452 =
                    let uu____22453 =
                      let uu____22470 =
                        let uu____22481 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____22490 =
                          let uu____22501 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____22501]  in
                        uu____22481 :: uu____22490  in
                      (lift_t1, uu____22470)  in
                    FStar_Syntax_Syntax.Tm_app uu____22453  in
                  FStar_Syntax_Syntax.mk uu____22452  in
                uu____22445 FStar_Pervasives_Native.None
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
            let uu____22611 = inst_tscheme_with lift_t [u]  in
            match uu____22611 with
            | (uu____22618,lift_t1) ->
                let uu____22620 =
                  let uu____22627 =
                    let uu____22628 =
                      let uu____22645 =
                        let uu____22656 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____22665 =
                          let uu____22676 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____22685 =
                            let uu____22696 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____22696]  in
                          uu____22676 :: uu____22685  in
                        uu____22656 :: uu____22665  in
                      (lift_t1, uu____22645)  in
                    FStar_Syntax_Syntax.Tm_app uu____22628  in
                  FStar_Syntax_Syntax.mk uu____22627  in
                uu____22620 FStar_Pervasives_Native.None
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
              let uu____22798 =
                let uu____22799 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____22799
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____22798  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____22808 =
              let uu____22810 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____22810  in
            let uu____22811 =
              let uu____22813 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____22841 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____22841)
                 in
              FStar_Util.dflt "none" uu____22813  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22808
              uu____22811
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____22870  ->
                    match uu____22870 with
                    | (e,uu____22878) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____22901 =
            match uu____22901 with
            | (i,j) ->
                let uu____22912 = FStar_Ident.lid_equals i j  in
                if uu____22912
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _22919  -> FStar_Pervasives_Native.Some _22919)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____22948 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____22958 = FStar_Ident.lid_equals i k  in
                        if uu____22958
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____22972 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____22972
                                  then []
                                  else
                                    (let uu____22979 =
                                       let uu____22988 =
                                         find_edge order1 (i, k)  in
                                       let uu____22991 =
                                         find_edge order1 (k, j)  in
                                       (uu____22988, uu____22991)  in
                                     match uu____22979 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____23006 =
                                           compose_edges e1 e2  in
                                         [uu____23006]
                                     | uu____23007 -> [])))))
                 in
              FStar_List.append order1 uu____22948  in
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
                   let uu____23037 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____23040 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____23040
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____23037
                   then
                     let uu____23047 =
                       let uu____23053 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____23053)
                        in
                     let uu____23057 = get_range env  in
                     FStar_Errors.raise_error uu____23047 uu____23057
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____23135 = FStar_Ident.lid_equals i j
                                   in
                                if uu____23135
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____23187 =
                                              let uu____23196 =
                                                find_edge order2 (i, k)  in
                                              let uu____23199 =
                                                find_edge order2 (j, k)  in
                                              (uu____23196, uu____23199)  in
                                            match uu____23187 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____23241,uu____23242)
                                                     ->
                                                     let uu____23249 =
                                                       let uu____23256 =
                                                         let uu____23258 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____23258
                                                          in
                                                       let uu____23261 =
                                                         let uu____23263 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____23263
                                                          in
                                                       (uu____23256,
                                                         uu____23261)
                                                        in
                                                     (match uu____23249 with
                                                      | (true ,true ) ->
                                                          let uu____23280 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____23280
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
                                            | uu____23323 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1657_23396 = env.effects  in
              { decls = (uu___1657_23396.decls); order = order2; joins }  in
            let uu___1660_23397 = env  in
            {
              solver = (uu___1660_23397.solver);
              range = (uu___1660_23397.range);
              curmodule = (uu___1660_23397.curmodule);
              gamma = (uu___1660_23397.gamma);
              gamma_sig = (uu___1660_23397.gamma_sig);
              gamma_cache = (uu___1660_23397.gamma_cache);
              modules = (uu___1660_23397.modules);
              expected_typ = (uu___1660_23397.expected_typ);
              sigtab = (uu___1660_23397.sigtab);
              attrtab = (uu___1660_23397.attrtab);
              is_pattern = (uu___1660_23397.is_pattern);
              instantiate_imp = (uu___1660_23397.instantiate_imp);
              effects;
              generalize = (uu___1660_23397.generalize);
              letrecs = (uu___1660_23397.letrecs);
              top_level = (uu___1660_23397.top_level);
              check_uvars = (uu___1660_23397.check_uvars);
              use_eq = (uu___1660_23397.use_eq);
              is_iface = (uu___1660_23397.is_iface);
              admit = (uu___1660_23397.admit);
              lax = (uu___1660_23397.lax);
              lax_universes = (uu___1660_23397.lax_universes);
              phase1 = (uu___1660_23397.phase1);
              failhard = (uu___1660_23397.failhard);
              nosynth = (uu___1660_23397.nosynth);
              uvar_subtyping = (uu___1660_23397.uvar_subtyping);
              tc_term = (uu___1660_23397.tc_term);
              type_of = (uu___1660_23397.type_of);
              universe_of = (uu___1660_23397.universe_of);
              check_type_of = (uu___1660_23397.check_type_of);
              use_bv_sorts = (uu___1660_23397.use_bv_sorts);
              qtbl_name_and_index = (uu___1660_23397.qtbl_name_and_index);
              normalized_eff_names = (uu___1660_23397.normalized_eff_names);
              fv_delta_depths = (uu___1660_23397.fv_delta_depths);
              proof_ns = (uu___1660_23397.proof_ns);
              synth_hook = (uu___1660_23397.synth_hook);
              try_solve_implicits_hook =
                (uu___1660_23397.try_solve_implicits_hook);
              splice = (uu___1660_23397.splice);
              postprocess = (uu___1660_23397.postprocess);
              is_native_tactic = (uu___1660_23397.is_native_tactic);
              identifier_info = (uu___1660_23397.identifier_info);
              tc_hooks = (uu___1660_23397.tc_hooks);
              dsenv = (uu___1660_23397.dsenv);
              nbe = (uu___1660_23397.nbe);
              strict_args_tab = (uu___1660_23397.strict_args_tab)
            }))
      | uu____23398 -> env
  
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
        | uu____23427 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23440 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23440 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23457 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23457 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23482 =
                     let uu____23488 =
                       let uu____23490 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23498 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23509 =
                         let uu____23511 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23511  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23490 uu____23498 uu____23509
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23488)
                      in
                   FStar_Errors.raise_error uu____23482
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23519 =
                     let uu____23530 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23530 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23567  ->
                        fun uu____23568  ->
                          match (uu____23567, uu____23568) with
                          | ((x,uu____23598),(t,uu____23600)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23519
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23631 =
                     let uu___1698_23632 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1698_23632.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1698_23632.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1698_23632.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1698_23632.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23631
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23644 .
    'Auu____23644 ->
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
          let uu____23674 = effect_decl_opt env effect_name  in
          match uu____23674 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____23717 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____23740 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____23779 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____23779
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____23784 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____23784
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____23795 =
                     let uu____23798 = get_range env  in
                     let uu____23799 =
                       let uu____23806 =
                         let uu____23807 =
                           let uu____23824 =
                             let uu____23835 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23835; wp]  in
                           (repr, uu____23824)  in
                         FStar_Syntax_Syntax.Tm_app uu____23807  in
                       FStar_Syntax_Syntax.mk uu____23806  in
                     uu____23799 FStar_Pervasives_Native.None uu____23798  in
                   FStar_Pervasives_Native.Some uu____23795)
  
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
      | uu____23979 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23994 =
        let uu____23995 = FStar_Syntax_Subst.compress t  in
        uu____23995.FStar_Syntax_Syntax.n  in
      match uu____23994 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23999,c) ->
          is_reifiable_comp env c
      | uu____24021 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24041 =
           let uu____24043 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24043  in
         if uu____24041
         then
           let uu____24046 =
             let uu____24052 =
               let uu____24054 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24054
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24052)  in
           let uu____24058 = get_range env  in
           FStar_Errors.raise_error uu____24046 uu____24058
         else ());
        (let uu____24061 = effect_repr_aux true env c u_c  in
         match uu____24061 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1763_24097 = env  in
        {
          solver = (uu___1763_24097.solver);
          range = (uu___1763_24097.range);
          curmodule = (uu___1763_24097.curmodule);
          gamma = (uu___1763_24097.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1763_24097.gamma_cache);
          modules = (uu___1763_24097.modules);
          expected_typ = (uu___1763_24097.expected_typ);
          sigtab = (uu___1763_24097.sigtab);
          attrtab = (uu___1763_24097.attrtab);
          is_pattern = (uu___1763_24097.is_pattern);
          instantiate_imp = (uu___1763_24097.instantiate_imp);
          effects = (uu___1763_24097.effects);
          generalize = (uu___1763_24097.generalize);
          letrecs = (uu___1763_24097.letrecs);
          top_level = (uu___1763_24097.top_level);
          check_uvars = (uu___1763_24097.check_uvars);
          use_eq = (uu___1763_24097.use_eq);
          is_iface = (uu___1763_24097.is_iface);
          admit = (uu___1763_24097.admit);
          lax = (uu___1763_24097.lax);
          lax_universes = (uu___1763_24097.lax_universes);
          phase1 = (uu___1763_24097.phase1);
          failhard = (uu___1763_24097.failhard);
          nosynth = (uu___1763_24097.nosynth);
          uvar_subtyping = (uu___1763_24097.uvar_subtyping);
          tc_term = (uu___1763_24097.tc_term);
          type_of = (uu___1763_24097.type_of);
          universe_of = (uu___1763_24097.universe_of);
          check_type_of = (uu___1763_24097.check_type_of);
          use_bv_sorts = (uu___1763_24097.use_bv_sorts);
          qtbl_name_and_index = (uu___1763_24097.qtbl_name_and_index);
          normalized_eff_names = (uu___1763_24097.normalized_eff_names);
          fv_delta_depths = (uu___1763_24097.fv_delta_depths);
          proof_ns = (uu___1763_24097.proof_ns);
          synth_hook = (uu___1763_24097.synth_hook);
          try_solve_implicits_hook =
            (uu___1763_24097.try_solve_implicits_hook);
          splice = (uu___1763_24097.splice);
          postprocess = (uu___1763_24097.postprocess);
          is_native_tactic = (uu___1763_24097.is_native_tactic);
          identifier_info = (uu___1763_24097.identifier_info);
          tc_hooks = (uu___1763_24097.tc_hooks);
          dsenv = (uu___1763_24097.dsenv);
          nbe = (uu___1763_24097.nbe);
          strict_args_tab = (uu___1763_24097.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1770_24111 = env  in
      {
        solver = (uu___1770_24111.solver);
        range = (uu___1770_24111.range);
        curmodule = (uu___1770_24111.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1770_24111.gamma_sig);
        gamma_cache = (uu___1770_24111.gamma_cache);
        modules = (uu___1770_24111.modules);
        expected_typ = (uu___1770_24111.expected_typ);
        sigtab = (uu___1770_24111.sigtab);
        attrtab = (uu___1770_24111.attrtab);
        is_pattern = (uu___1770_24111.is_pattern);
        instantiate_imp = (uu___1770_24111.instantiate_imp);
        effects = (uu___1770_24111.effects);
        generalize = (uu___1770_24111.generalize);
        letrecs = (uu___1770_24111.letrecs);
        top_level = (uu___1770_24111.top_level);
        check_uvars = (uu___1770_24111.check_uvars);
        use_eq = (uu___1770_24111.use_eq);
        is_iface = (uu___1770_24111.is_iface);
        admit = (uu___1770_24111.admit);
        lax = (uu___1770_24111.lax);
        lax_universes = (uu___1770_24111.lax_universes);
        phase1 = (uu___1770_24111.phase1);
        failhard = (uu___1770_24111.failhard);
        nosynth = (uu___1770_24111.nosynth);
        uvar_subtyping = (uu___1770_24111.uvar_subtyping);
        tc_term = (uu___1770_24111.tc_term);
        type_of = (uu___1770_24111.type_of);
        universe_of = (uu___1770_24111.universe_of);
        check_type_of = (uu___1770_24111.check_type_of);
        use_bv_sorts = (uu___1770_24111.use_bv_sorts);
        qtbl_name_and_index = (uu___1770_24111.qtbl_name_and_index);
        normalized_eff_names = (uu___1770_24111.normalized_eff_names);
        fv_delta_depths = (uu___1770_24111.fv_delta_depths);
        proof_ns = (uu___1770_24111.proof_ns);
        synth_hook = (uu___1770_24111.synth_hook);
        try_solve_implicits_hook = (uu___1770_24111.try_solve_implicits_hook);
        splice = (uu___1770_24111.splice);
        postprocess = (uu___1770_24111.postprocess);
        is_native_tactic = (uu___1770_24111.is_native_tactic);
        identifier_info = (uu___1770_24111.identifier_info);
        tc_hooks = (uu___1770_24111.tc_hooks);
        dsenv = (uu___1770_24111.dsenv);
        nbe = (uu___1770_24111.nbe);
        strict_args_tab = (uu___1770_24111.strict_args_tab)
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
            (let uu___1783_24169 = env  in
             {
               solver = (uu___1783_24169.solver);
               range = (uu___1783_24169.range);
               curmodule = (uu___1783_24169.curmodule);
               gamma = rest;
               gamma_sig = (uu___1783_24169.gamma_sig);
               gamma_cache = (uu___1783_24169.gamma_cache);
               modules = (uu___1783_24169.modules);
               expected_typ = (uu___1783_24169.expected_typ);
               sigtab = (uu___1783_24169.sigtab);
               attrtab = (uu___1783_24169.attrtab);
               is_pattern = (uu___1783_24169.is_pattern);
               instantiate_imp = (uu___1783_24169.instantiate_imp);
               effects = (uu___1783_24169.effects);
               generalize = (uu___1783_24169.generalize);
               letrecs = (uu___1783_24169.letrecs);
               top_level = (uu___1783_24169.top_level);
               check_uvars = (uu___1783_24169.check_uvars);
               use_eq = (uu___1783_24169.use_eq);
               is_iface = (uu___1783_24169.is_iface);
               admit = (uu___1783_24169.admit);
               lax = (uu___1783_24169.lax);
               lax_universes = (uu___1783_24169.lax_universes);
               phase1 = (uu___1783_24169.phase1);
               failhard = (uu___1783_24169.failhard);
               nosynth = (uu___1783_24169.nosynth);
               uvar_subtyping = (uu___1783_24169.uvar_subtyping);
               tc_term = (uu___1783_24169.tc_term);
               type_of = (uu___1783_24169.type_of);
               universe_of = (uu___1783_24169.universe_of);
               check_type_of = (uu___1783_24169.check_type_of);
               use_bv_sorts = (uu___1783_24169.use_bv_sorts);
               qtbl_name_and_index = (uu___1783_24169.qtbl_name_and_index);
               normalized_eff_names = (uu___1783_24169.normalized_eff_names);
               fv_delta_depths = (uu___1783_24169.fv_delta_depths);
               proof_ns = (uu___1783_24169.proof_ns);
               synth_hook = (uu___1783_24169.synth_hook);
               try_solve_implicits_hook =
                 (uu___1783_24169.try_solve_implicits_hook);
               splice = (uu___1783_24169.splice);
               postprocess = (uu___1783_24169.postprocess);
               is_native_tactic = (uu___1783_24169.is_native_tactic);
               identifier_info = (uu___1783_24169.identifier_info);
               tc_hooks = (uu___1783_24169.tc_hooks);
               dsenv = (uu___1783_24169.dsenv);
               nbe = (uu___1783_24169.nbe);
               strict_args_tab = (uu___1783_24169.strict_args_tab)
             }))
    | uu____24170 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24199  ->
             match uu____24199 with | (x,uu____24207) -> push_bv env1 x) env
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
            let uu___1797_24242 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1797_24242.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1797_24242.FStar_Syntax_Syntax.index);
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
      (let uu___1808_24284 = env  in
       {
         solver = (uu___1808_24284.solver);
         range = (uu___1808_24284.range);
         curmodule = (uu___1808_24284.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1808_24284.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1808_24284.sigtab);
         attrtab = (uu___1808_24284.attrtab);
         is_pattern = (uu___1808_24284.is_pattern);
         instantiate_imp = (uu___1808_24284.instantiate_imp);
         effects = (uu___1808_24284.effects);
         generalize = (uu___1808_24284.generalize);
         letrecs = (uu___1808_24284.letrecs);
         top_level = (uu___1808_24284.top_level);
         check_uvars = (uu___1808_24284.check_uvars);
         use_eq = (uu___1808_24284.use_eq);
         is_iface = (uu___1808_24284.is_iface);
         admit = (uu___1808_24284.admit);
         lax = (uu___1808_24284.lax);
         lax_universes = (uu___1808_24284.lax_universes);
         phase1 = (uu___1808_24284.phase1);
         failhard = (uu___1808_24284.failhard);
         nosynth = (uu___1808_24284.nosynth);
         uvar_subtyping = (uu___1808_24284.uvar_subtyping);
         tc_term = (uu___1808_24284.tc_term);
         type_of = (uu___1808_24284.type_of);
         universe_of = (uu___1808_24284.universe_of);
         check_type_of = (uu___1808_24284.check_type_of);
         use_bv_sorts = (uu___1808_24284.use_bv_sorts);
         qtbl_name_and_index = (uu___1808_24284.qtbl_name_and_index);
         normalized_eff_names = (uu___1808_24284.normalized_eff_names);
         fv_delta_depths = (uu___1808_24284.fv_delta_depths);
         proof_ns = (uu___1808_24284.proof_ns);
         synth_hook = (uu___1808_24284.synth_hook);
         try_solve_implicits_hook =
           (uu___1808_24284.try_solve_implicits_hook);
         splice = (uu___1808_24284.splice);
         postprocess = (uu___1808_24284.postprocess);
         is_native_tactic = (uu___1808_24284.is_native_tactic);
         identifier_info = (uu___1808_24284.identifier_info);
         tc_hooks = (uu___1808_24284.tc_hooks);
         dsenv = (uu___1808_24284.dsenv);
         nbe = (uu___1808_24284.nbe);
         strict_args_tab = (uu___1808_24284.strict_args_tab)
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
        let uu____24328 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24328 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24356 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24356)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1823_24372 = env  in
      {
        solver = (uu___1823_24372.solver);
        range = (uu___1823_24372.range);
        curmodule = (uu___1823_24372.curmodule);
        gamma = (uu___1823_24372.gamma);
        gamma_sig = (uu___1823_24372.gamma_sig);
        gamma_cache = (uu___1823_24372.gamma_cache);
        modules = (uu___1823_24372.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1823_24372.sigtab);
        attrtab = (uu___1823_24372.attrtab);
        is_pattern = (uu___1823_24372.is_pattern);
        instantiate_imp = (uu___1823_24372.instantiate_imp);
        effects = (uu___1823_24372.effects);
        generalize = (uu___1823_24372.generalize);
        letrecs = (uu___1823_24372.letrecs);
        top_level = (uu___1823_24372.top_level);
        check_uvars = (uu___1823_24372.check_uvars);
        use_eq = false;
        is_iface = (uu___1823_24372.is_iface);
        admit = (uu___1823_24372.admit);
        lax = (uu___1823_24372.lax);
        lax_universes = (uu___1823_24372.lax_universes);
        phase1 = (uu___1823_24372.phase1);
        failhard = (uu___1823_24372.failhard);
        nosynth = (uu___1823_24372.nosynth);
        uvar_subtyping = (uu___1823_24372.uvar_subtyping);
        tc_term = (uu___1823_24372.tc_term);
        type_of = (uu___1823_24372.type_of);
        universe_of = (uu___1823_24372.universe_of);
        check_type_of = (uu___1823_24372.check_type_of);
        use_bv_sorts = (uu___1823_24372.use_bv_sorts);
        qtbl_name_and_index = (uu___1823_24372.qtbl_name_and_index);
        normalized_eff_names = (uu___1823_24372.normalized_eff_names);
        fv_delta_depths = (uu___1823_24372.fv_delta_depths);
        proof_ns = (uu___1823_24372.proof_ns);
        synth_hook = (uu___1823_24372.synth_hook);
        try_solve_implicits_hook = (uu___1823_24372.try_solve_implicits_hook);
        splice = (uu___1823_24372.splice);
        postprocess = (uu___1823_24372.postprocess);
        is_native_tactic = (uu___1823_24372.is_native_tactic);
        identifier_info = (uu___1823_24372.identifier_info);
        tc_hooks = (uu___1823_24372.tc_hooks);
        dsenv = (uu___1823_24372.dsenv);
        nbe = (uu___1823_24372.nbe);
        strict_args_tab = (uu___1823_24372.strict_args_tab)
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
    let uu____24403 = expected_typ env_  in
    ((let uu___1830_24409 = env_  in
      {
        solver = (uu___1830_24409.solver);
        range = (uu___1830_24409.range);
        curmodule = (uu___1830_24409.curmodule);
        gamma = (uu___1830_24409.gamma);
        gamma_sig = (uu___1830_24409.gamma_sig);
        gamma_cache = (uu___1830_24409.gamma_cache);
        modules = (uu___1830_24409.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1830_24409.sigtab);
        attrtab = (uu___1830_24409.attrtab);
        is_pattern = (uu___1830_24409.is_pattern);
        instantiate_imp = (uu___1830_24409.instantiate_imp);
        effects = (uu___1830_24409.effects);
        generalize = (uu___1830_24409.generalize);
        letrecs = (uu___1830_24409.letrecs);
        top_level = (uu___1830_24409.top_level);
        check_uvars = (uu___1830_24409.check_uvars);
        use_eq = false;
        is_iface = (uu___1830_24409.is_iface);
        admit = (uu___1830_24409.admit);
        lax = (uu___1830_24409.lax);
        lax_universes = (uu___1830_24409.lax_universes);
        phase1 = (uu___1830_24409.phase1);
        failhard = (uu___1830_24409.failhard);
        nosynth = (uu___1830_24409.nosynth);
        uvar_subtyping = (uu___1830_24409.uvar_subtyping);
        tc_term = (uu___1830_24409.tc_term);
        type_of = (uu___1830_24409.type_of);
        universe_of = (uu___1830_24409.universe_of);
        check_type_of = (uu___1830_24409.check_type_of);
        use_bv_sorts = (uu___1830_24409.use_bv_sorts);
        qtbl_name_and_index = (uu___1830_24409.qtbl_name_and_index);
        normalized_eff_names = (uu___1830_24409.normalized_eff_names);
        fv_delta_depths = (uu___1830_24409.fv_delta_depths);
        proof_ns = (uu___1830_24409.proof_ns);
        synth_hook = (uu___1830_24409.synth_hook);
        try_solve_implicits_hook = (uu___1830_24409.try_solve_implicits_hook);
        splice = (uu___1830_24409.splice);
        postprocess = (uu___1830_24409.postprocess);
        is_native_tactic = (uu___1830_24409.is_native_tactic);
        identifier_info = (uu___1830_24409.identifier_info);
        tc_hooks = (uu___1830_24409.tc_hooks);
        dsenv = (uu___1830_24409.dsenv);
        nbe = (uu___1830_24409.nbe);
        strict_args_tab = (uu___1830_24409.strict_args_tab)
      }), uu____24403)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24421 =
      let uu____24424 = FStar_Ident.id_of_text ""  in [uu____24424]  in
    FStar_Ident.lid_of_ids uu____24421  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24431 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24431
        then
          let uu____24436 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24436 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1838_24464 = env  in
       {
         solver = (uu___1838_24464.solver);
         range = (uu___1838_24464.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1838_24464.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1838_24464.expected_typ);
         sigtab = (uu___1838_24464.sigtab);
         attrtab = (uu___1838_24464.attrtab);
         is_pattern = (uu___1838_24464.is_pattern);
         instantiate_imp = (uu___1838_24464.instantiate_imp);
         effects = (uu___1838_24464.effects);
         generalize = (uu___1838_24464.generalize);
         letrecs = (uu___1838_24464.letrecs);
         top_level = (uu___1838_24464.top_level);
         check_uvars = (uu___1838_24464.check_uvars);
         use_eq = (uu___1838_24464.use_eq);
         is_iface = (uu___1838_24464.is_iface);
         admit = (uu___1838_24464.admit);
         lax = (uu___1838_24464.lax);
         lax_universes = (uu___1838_24464.lax_universes);
         phase1 = (uu___1838_24464.phase1);
         failhard = (uu___1838_24464.failhard);
         nosynth = (uu___1838_24464.nosynth);
         uvar_subtyping = (uu___1838_24464.uvar_subtyping);
         tc_term = (uu___1838_24464.tc_term);
         type_of = (uu___1838_24464.type_of);
         universe_of = (uu___1838_24464.universe_of);
         check_type_of = (uu___1838_24464.check_type_of);
         use_bv_sorts = (uu___1838_24464.use_bv_sorts);
         qtbl_name_and_index = (uu___1838_24464.qtbl_name_and_index);
         normalized_eff_names = (uu___1838_24464.normalized_eff_names);
         fv_delta_depths = (uu___1838_24464.fv_delta_depths);
         proof_ns = (uu___1838_24464.proof_ns);
         synth_hook = (uu___1838_24464.synth_hook);
         try_solve_implicits_hook =
           (uu___1838_24464.try_solve_implicits_hook);
         splice = (uu___1838_24464.splice);
         postprocess = (uu___1838_24464.postprocess);
         is_native_tactic = (uu___1838_24464.is_native_tactic);
         identifier_info = (uu___1838_24464.identifier_info);
         tc_hooks = (uu___1838_24464.tc_hooks);
         dsenv = (uu___1838_24464.dsenv);
         nbe = (uu___1838_24464.nbe);
         strict_args_tab = (uu___1838_24464.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24516)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24520,(uu____24521,t)))::tl1
          ->
          let uu____24542 =
            let uu____24545 = FStar_Syntax_Free.uvars t  in
            ext out uu____24545  in
          aux uu____24542 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24548;
            FStar_Syntax_Syntax.index = uu____24549;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24557 =
            let uu____24560 = FStar_Syntax_Free.uvars t  in
            ext out uu____24560  in
          aux uu____24557 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24618)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24622,(uu____24623,t)))::tl1
          ->
          let uu____24644 =
            let uu____24647 = FStar_Syntax_Free.univs t  in
            ext out uu____24647  in
          aux uu____24644 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24650;
            FStar_Syntax_Syntax.index = uu____24651;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24659 =
            let uu____24662 = FStar_Syntax_Free.univs t  in
            ext out uu____24662  in
          aux uu____24659 tl1
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
          let uu____24724 = FStar_Util.set_add uname out  in
          aux uu____24724 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24727,(uu____24728,t)))::tl1
          ->
          let uu____24749 =
            let uu____24752 = FStar_Syntax_Free.univnames t  in
            ext out uu____24752  in
          aux uu____24749 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24755;
            FStar_Syntax_Syntax.index = uu____24756;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24764 =
            let uu____24767 = FStar_Syntax_Free.univnames t  in
            ext out uu____24767  in
          aux uu____24764 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24788  ->
            match uu___11_24788 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24792 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24805 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24816 =
      let uu____24825 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24825
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24816 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24873 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24886  ->
              match uu___12_24886 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24889 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24889
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24895) ->
                  let uu____24912 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24912))
       in
    FStar_All.pipe_right uu____24873 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24926  ->
    match uu___13_24926 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24932 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24932
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24955  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____25010) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25043,uu____25044) -> false  in
      let uu____25058 =
        FStar_List.tryFind
          (fun uu____25080  ->
             match uu____25080 with | (p,uu____25091) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25058 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25110,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25140 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25140
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1981_25162 = e  in
        {
          solver = (uu___1981_25162.solver);
          range = (uu___1981_25162.range);
          curmodule = (uu___1981_25162.curmodule);
          gamma = (uu___1981_25162.gamma);
          gamma_sig = (uu___1981_25162.gamma_sig);
          gamma_cache = (uu___1981_25162.gamma_cache);
          modules = (uu___1981_25162.modules);
          expected_typ = (uu___1981_25162.expected_typ);
          sigtab = (uu___1981_25162.sigtab);
          attrtab = (uu___1981_25162.attrtab);
          is_pattern = (uu___1981_25162.is_pattern);
          instantiate_imp = (uu___1981_25162.instantiate_imp);
          effects = (uu___1981_25162.effects);
          generalize = (uu___1981_25162.generalize);
          letrecs = (uu___1981_25162.letrecs);
          top_level = (uu___1981_25162.top_level);
          check_uvars = (uu___1981_25162.check_uvars);
          use_eq = (uu___1981_25162.use_eq);
          is_iface = (uu___1981_25162.is_iface);
          admit = (uu___1981_25162.admit);
          lax = (uu___1981_25162.lax);
          lax_universes = (uu___1981_25162.lax_universes);
          phase1 = (uu___1981_25162.phase1);
          failhard = (uu___1981_25162.failhard);
          nosynth = (uu___1981_25162.nosynth);
          uvar_subtyping = (uu___1981_25162.uvar_subtyping);
          tc_term = (uu___1981_25162.tc_term);
          type_of = (uu___1981_25162.type_of);
          universe_of = (uu___1981_25162.universe_of);
          check_type_of = (uu___1981_25162.check_type_of);
          use_bv_sorts = (uu___1981_25162.use_bv_sorts);
          qtbl_name_and_index = (uu___1981_25162.qtbl_name_and_index);
          normalized_eff_names = (uu___1981_25162.normalized_eff_names);
          fv_delta_depths = (uu___1981_25162.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1981_25162.synth_hook);
          try_solve_implicits_hook =
            (uu___1981_25162.try_solve_implicits_hook);
          splice = (uu___1981_25162.splice);
          postprocess = (uu___1981_25162.postprocess);
          is_native_tactic = (uu___1981_25162.is_native_tactic);
          identifier_info = (uu___1981_25162.identifier_info);
          tc_hooks = (uu___1981_25162.tc_hooks);
          dsenv = (uu___1981_25162.dsenv);
          nbe = (uu___1981_25162.nbe);
          strict_args_tab = (uu___1981_25162.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1990_25210 = e  in
      {
        solver = (uu___1990_25210.solver);
        range = (uu___1990_25210.range);
        curmodule = (uu___1990_25210.curmodule);
        gamma = (uu___1990_25210.gamma);
        gamma_sig = (uu___1990_25210.gamma_sig);
        gamma_cache = (uu___1990_25210.gamma_cache);
        modules = (uu___1990_25210.modules);
        expected_typ = (uu___1990_25210.expected_typ);
        sigtab = (uu___1990_25210.sigtab);
        attrtab = (uu___1990_25210.attrtab);
        is_pattern = (uu___1990_25210.is_pattern);
        instantiate_imp = (uu___1990_25210.instantiate_imp);
        effects = (uu___1990_25210.effects);
        generalize = (uu___1990_25210.generalize);
        letrecs = (uu___1990_25210.letrecs);
        top_level = (uu___1990_25210.top_level);
        check_uvars = (uu___1990_25210.check_uvars);
        use_eq = (uu___1990_25210.use_eq);
        is_iface = (uu___1990_25210.is_iface);
        admit = (uu___1990_25210.admit);
        lax = (uu___1990_25210.lax);
        lax_universes = (uu___1990_25210.lax_universes);
        phase1 = (uu___1990_25210.phase1);
        failhard = (uu___1990_25210.failhard);
        nosynth = (uu___1990_25210.nosynth);
        uvar_subtyping = (uu___1990_25210.uvar_subtyping);
        tc_term = (uu___1990_25210.tc_term);
        type_of = (uu___1990_25210.type_of);
        universe_of = (uu___1990_25210.universe_of);
        check_type_of = (uu___1990_25210.check_type_of);
        use_bv_sorts = (uu___1990_25210.use_bv_sorts);
        qtbl_name_and_index = (uu___1990_25210.qtbl_name_and_index);
        normalized_eff_names = (uu___1990_25210.normalized_eff_names);
        fv_delta_depths = (uu___1990_25210.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1990_25210.synth_hook);
        try_solve_implicits_hook = (uu___1990_25210.try_solve_implicits_hook);
        splice = (uu___1990_25210.splice);
        postprocess = (uu___1990_25210.postprocess);
        is_native_tactic = (uu___1990_25210.is_native_tactic);
        identifier_info = (uu___1990_25210.identifier_info);
        tc_hooks = (uu___1990_25210.tc_hooks);
        dsenv = (uu___1990_25210.dsenv);
        nbe = (uu___1990_25210.nbe);
        strict_args_tab = (uu___1990_25210.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25226 = FStar_Syntax_Free.names t  in
      let uu____25229 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25226 uu____25229
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25252 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25252
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25262 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25262
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25283 =
      match uu____25283 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25303 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25303)
       in
    let uu____25311 =
      let uu____25315 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25315 FStar_List.rev  in
    FStar_All.pipe_right uu____25311 (FStar_String.concat " ")
  
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
                  (let uu____25385 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25385 with
                   | FStar_Pervasives_Native.Some uu____25389 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25392 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____25402;
        univ_ineqs = uu____25403; implicits = uu____25404;_} -> true
    | uu____25416 -> false
  
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
          let uu___2034_25447 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2034_25447.deferred);
            univ_ineqs = (uu___2034_25447.univ_ineqs);
            implicits = (uu___2034_25447.implicits)
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
          let uu____25486 = FStar_Options.defensive ()  in
          if uu____25486
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25492 =
              let uu____25494 =
                let uu____25496 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25496  in
              Prims.op_Negation uu____25494  in
            (if uu____25492
             then
               let uu____25503 =
                 let uu____25509 =
                   let uu____25511 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25513 =
                     let uu____25515 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25515
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25511 uu____25513
                    in
                 (FStar_Errors.Warning_Defensive, uu____25509)  in
               FStar_Errors.log_issue rng uu____25503
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
          let uu____25555 =
            let uu____25557 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25557  in
          if uu____25555
          then ()
          else
            (let uu____25562 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25562 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25588 =
            let uu____25590 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25590  in
          if uu____25588
          then ()
          else
            (let uu____25595 = bound_vars e  in
             def_check_closed_in rng msg uu____25595 t)
  
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
          let uu___2071_25634 = g  in
          let uu____25635 =
            let uu____25636 =
              let uu____25637 =
                let uu____25644 =
                  let uu____25645 =
                    let uu____25662 =
                      let uu____25673 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25673]  in
                    (f, uu____25662)  in
                  FStar_Syntax_Syntax.Tm_app uu____25645  in
                FStar_Syntax_Syntax.mk uu____25644  in
              uu____25637 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25710  -> FStar_TypeChecker_Common.NonTrivial _25710)
              uu____25636
             in
          {
            guard_f = uu____25635;
            deferred = (uu___2071_25634.deferred);
            univ_ineqs = (uu___2071_25634.univ_ineqs);
            implicits = (uu___2071_25634.implicits)
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
          let uu___2078_25728 = g  in
          let uu____25729 =
            let uu____25730 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25730  in
          {
            guard_f = uu____25729;
            deferred = (uu___2078_25728.deferred);
            univ_ineqs = (uu___2078_25728.univ_ineqs);
            implicits = (uu___2078_25728.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2083_25747 = g  in
          let uu____25748 =
            let uu____25749 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25749  in
          {
            guard_f = uu____25748;
            deferred = (uu___2083_25747.deferred);
            univ_ineqs = (uu___2083_25747.univ_ineqs);
            implicits = (uu___2083_25747.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2087_25751 = g  in
          let uu____25752 =
            let uu____25753 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25753  in
          {
            guard_f = uu____25752;
            deferred = (uu___2087_25751.deferred);
            univ_ineqs = (uu___2087_25751.univ_ineqs);
            implicits = (uu___2087_25751.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25760 ->
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
          let uu____25777 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25777
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25784 =
      let uu____25785 = FStar_Syntax_Util.unmeta t  in
      uu____25785.FStar_Syntax_Syntax.n  in
    match uu____25784 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25789 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25832 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25832;
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
                       let uu____25927 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25927
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2142_25934 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2142_25934.deferred);
              univ_ineqs = (uu___2142_25934.univ_ineqs);
              implicits = (uu___2142_25934.implicits)
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
               let uu____25968 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25968
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
            let uu___2157_25995 = g  in
            let uu____25996 =
              let uu____25997 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25997  in
            {
              guard_f = uu____25996;
              deferred = (uu___2157_25995.deferred);
              univ_ineqs = (uu___2157_25995.univ_ineqs);
              implicits = (uu___2157_25995.implicits)
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
              let uu____26055 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26055 with
              | FStar_Pervasives_Native.Some
                  (uu____26080::(tm,uu____26082)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26146 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26164 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26164;
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
                      let uu___2179_26196 = trivial_guard  in
                      {
                        guard_f = (uu___2179_26196.guard_f);
                        deferred = (uu___2179_26196.deferred);
                        univ_ineqs = (uu___2179_26196.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26214  -> ());
    push = (fun uu____26216  -> ());
    pop = (fun uu____26219  -> ());
    snapshot =
      (fun uu____26222  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26241  -> fun uu____26242  -> ());
    encode_sig = (fun uu____26257  -> fun uu____26258  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26264 =
             let uu____26271 = FStar_Options.peek ()  in (e, g, uu____26271)
              in
           [uu____26264]);
    solve = (fun uu____26287  -> fun uu____26288  -> fun uu____26289  -> ());
    finish = (fun uu____26296  -> ());
    refresh = (fun uu____26298  -> ())
  } 