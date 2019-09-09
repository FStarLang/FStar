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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> solver
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> range
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> curmodule
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> gamma
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> gamma_sig
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> gamma_cache
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> modules
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> expected_typ
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> sigtab
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> attrtab
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> is_pattern
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> instantiate_imp
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> effects
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> generalize
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> letrecs
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> top_level
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> check_uvars
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> use_eq
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> is_iface
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> admit1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> lax1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> lax_universes
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> phase1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> failhard
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> nosynth
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> uvar_subtyping
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> tc_term
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> type_of
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> universe_of
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> check_type_of
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> use_bv_sorts
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> qtbl_name_and_index
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> normalized_eff_names
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> fv_delta_depths
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> proof_ns
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> synth_hook
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> splice1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> postprocess
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> is_native_tactic
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> identifier_info
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> tc_hooks
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> dsenv
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> nbe1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> strict_args_tab
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab; erasable_types_tab;_}
        -> erasable_types_tab
  
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
           (fun uu___0_12768  ->
              match uu___0_12768 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12771 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12771  in
                  let uu____12772 =
                    let uu____12773 = FStar_Syntax_Subst.compress y  in
                    uu____12773.FStar_Syntax_Syntax.n  in
                  (match uu____12772 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12777 =
                         let uu___335_12778 = y1  in
                         let uu____12779 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___335_12778.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___335_12778.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12779
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12777
                   | uu____12782 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___341_12796 = env  in
      let uu____12797 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___341_12796.solver);
        range = (uu___341_12796.range);
        curmodule = (uu___341_12796.curmodule);
        gamma = uu____12797;
        gamma_sig = (uu___341_12796.gamma_sig);
        gamma_cache = (uu___341_12796.gamma_cache);
        modules = (uu___341_12796.modules);
        expected_typ = (uu___341_12796.expected_typ);
        sigtab = (uu___341_12796.sigtab);
        attrtab = (uu___341_12796.attrtab);
        is_pattern = (uu___341_12796.is_pattern);
        instantiate_imp = (uu___341_12796.instantiate_imp);
        effects = (uu___341_12796.effects);
        generalize = (uu___341_12796.generalize);
        letrecs = (uu___341_12796.letrecs);
        top_level = (uu___341_12796.top_level);
        check_uvars = (uu___341_12796.check_uvars);
        use_eq = (uu___341_12796.use_eq);
        is_iface = (uu___341_12796.is_iface);
        admit = (uu___341_12796.admit);
        lax = (uu___341_12796.lax);
        lax_universes = (uu___341_12796.lax_universes);
        phase1 = (uu___341_12796.phase1);
        failhard = (uu___341_12796.failhard);
        nosynth = (uu___341_12796.nosynth);
        uvar_subtyping = (uu___341_12796.uvar_subtyping);
        tc_term = (uu___341_12796.tc_term);
        type_of = (uu___341_12796.type_of);
        universe_of = (uu___341_12796.universe_of);
        check_type_of = (uu___341_12796.check_type_of);
        use_bv_sorts = (uu___341_12796.use_bv_sorts);
        qtbl_name_and_index = (uu___341_12796.qtbl_name_and_index);
        normalized_eff_names = (uu___341_12796.normalized_eff_names);
        fv_delta_depths = (uu___341_12796.fv_delta_depths);
        proof_ns = (uu___341_12796.proof_ns);
        synth_hook = (uu___341_12796.synth_hook);
        splice = (uu___341_12796.splice);
        postprocess = (uu___341_12796.postprocess);
        is_native_tactic = (uu___341_12796.is_native_tactic);
        identifier_info = (uu___341_12796.identifier_info);
        tc_hooks = (uu___341_12796.tc_hooks);
        dsenv = (uu___341_12796.dsenv);
        nbe = (uu___341_12796.nbe);
        strict_args_tab = (uu___341_12796.strict_args_tab);
        erasable_types_tab = (uu___341_12796.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12805  -> fun uu____12806  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___348_12828 = env  in
      {
        solver = (uu___348_12828.solver);
        range = (uu___348_12828.range);
        curmodule = (uu___348_12828.curmodule);
        gamma = (uu___348_12828.gamma);
        gamma_sig = (uu___348_12828.gamma_sig);
        gamma_cache = (uu___348_12828.gamma_cache);
        modules = (uu___348_12828.modules);
        expected_typ = (uu___348_12828.expected_typ);
        sigtab = (uu___348_12828.sigtab);
        attrtab = (uu___348_12828.attrtab);
        is_pattern = (uu___348_12828.is_pattern);
        instantiate_imp = (uu___348_12828.instantiate_imp);
        effects = (uu___348_12828.effects);
        generalize = (uu___348_12828.generalize);
        letrecs = (uu___348_12828.letrecs);
        top_level = (uu___348_12828.top_level);
        check_uvars = (uu___348_12828.check_uvars);
        use_eq = (uu___348_12828.use_eq);
        is_iface = (uu___348_12828.is_iface);
        admit = (uu___348_12828.admit);
        lax = (uu___348_12828.lax);
        lax_universes = (uu___348_12828.lax_universes);
        phase1 = (uu___348_12828.phase1);
        failhard = (uu___348_12828.failhard);
        nosynth = (uu___348_12828.nosynth);
        uvar_subtyping = (uu___348_12828.uvar_subtyping);
        tc_term = (uu___348_12828.tc_term);
        type_of = (uu___348_12828.type_of);
        universe_of = (uu___348_12828.universe_of);
        check_type_of = (uu___348_12828.check_type_of);
        use_bv_sorts = (uu___348_12828.use_bv_sorts);
        qtbl_name_and_index = (uu___348_12828.qtbl_name_and_index);
        normalized_eff_names = (uu___348_12828.normalized_eff_names);
        fv_delta_depths = (uu___348_12828.fv_delta_depths);
        proof_ns = (uu___348_12828.proof_ns);
        synth_hook = (uu___348_12828.synth_hook);
        splice = (uu___348_12828.splice);
        postprocess = (uu___348_12828.postprocess);
        is_native_tactic = (uu___348_12828.is_native_tactic);
        identifier_info = (uu___348_12828.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___348_12828.dsenv);
        nbe = (uu___348_12828.nbe);
        strict_args_tab = (uu___348_12828.strict_args_tab);
        erasable_types_tab = (uu___348_12828.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___352_12840 = e  in
      let uu____12841 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___352_12840.solver);
        range = (uu___352_12840.range);
        curmodule = (uu___352_12840.curmodule);
        gamma = (uu___352_12840.gamma);
        gamma_sig = (uu___352_12840.gamma_sig);
        gamma_cache = (uu___352_12840.gamma_cache);
        modules = (uu___352_12840.modules);
        expected_typ = (uu___352_12840.expected_typ);
        sigtab = (uu___352_12840.sigtab);
        attrtab = (uu___352_12840.attrtab);
        is_pattern = (uu___352_12840.is_pattern);
        instantiate_imp = (uu___352_12840.instantiate_imp);
        effects = (uu___352_12840.effects);
        generalize = (uu___352_12840.generalize);
        letrecs = (uu___352_12840.letrecs);
        top_level = (uu___352_12840.top_level);
        check_uvars = (uu___352_12840.check_uvars);
        use_eq = (uu___352_12840.use_eq);
        is_iface = (uu___352_12840.is_iface);
        admit = (uu___352_12840.admit);
        lax = (uu___352_12840.lax);
        lax_universes = (uu___352_12840.lax_universes);
        phase1 = (uu___352_12840.phase1);
        failhard = (uu___352_12840.failhard);
        nosynth = (uu___352_12840.nosynth);
        uvar_subtyping = (uu___352_12840.uvar_subtyping);
        tc_term = (uu___352_12840.tc_term);
        type_of = (uu___352_12840.type_of);
        universe_of = (uu___352_12840.universe_of);
        check_type_of = (uu___352_12840.check_type_of);
        use_bv_sorts = (uu___352_12840.use_bv_sorts);
        qtbl_name_and_index = (uu___352_12840.qtbl_name_and_index);
        normalized_eff_names = (uu___352_12840.normalized_eff_names);
        fv_delta_depths = (uu___352_12840.fv_delta_depths);
        proof_ns = (uu___352_12840.proof_ns);
        synth_hook = (uu___352_12840.synth_hook);
        splice = (uu___352_12840.splice);
        postprocess = (uu___352_12840.postprocess);
        is_native_tactic = (uu___352_12840.is_native_tactic);
        identifier_info = (uu___352_12840.identifier_info);
        tc_hooks = (uu___352_12840.tc_hooks);
        dsenv = uu____12841;
        nbe = (uu___352_12840.nbe);
        strict_args_tab = (uu___352_12840.strict_args_tab);
        erasable_types_tab = (uu___352_12840.erasable_types_tab)
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
      | (NoDelta ,uu____12870) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12873,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12875,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12878 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12892 . unit -> 'Auu____12892 FStar_Util.smap =
  fun uu____12899  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12905 . unit -> 'Auu____12905 FStar_Util.smap =
  fun uu____12912  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13050 = new_gamma_cache ()  in
                  let uu____13053 = new_sigtab ()  in
                  let uu____13056 = new_sigtab ()  in
                  let uu____13063 =
                    let uu____13078 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13078, FStar_Pervasives_Native.None)  in
                  let uu____13099 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13103 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13107 = FStar_Options.using_facts_from ()  in
                  let uu____13108 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13111 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13112 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13126 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13050;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13053;
                    attrtab = uu____13056;
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
                    qtbl_name_and_index = uu____13063;
                    normalized_eff_names = uu____13099;
                    fv_delta_depths = uu____13103;
                    proof_ns = uu____13107;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____13193  -> false);
                    identifier_info = uu____13108;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13111;
                    nbe = nbe1;
                    strict_args_tab = uu____13112;
                    erasable_types_tab = uu____13126
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
  fun uu____13272  ->
    let uu____13273 = FStar_ST.op_Bang query_indices  in
    match uu____13273 with
    | [] -> failwith "Empty query indices!"
    | uu____13328 ->
        let uu____13338 =
          let uu____13348 =
            let uu____13356 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13356  in
          let uu____13410 = FStar_ST.op_Bang query_indices  in uu____13348 ::
            uu____13410
           in
        FStar_ST.op_Colon_Equals query_indices uu____13338
  
let (pop_query_indices : unit -> unit) =
  fun uu____13506  ->
    let uu____13507 = FStar_ST.op_Bang query_indices  in
    match uu____13507 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13634  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13671  ->
    match uu____13671 with
    | (l,n1) ->
        let uu____13681 = FStar_ST.op_Bang query_indices  in
        (match uu____13681 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13803 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13826  ->
    let uu____13827 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13827
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13895 =
       let uu____13898 = FStar_ST.op_Bang stack  in env :: uu____13898  in
     FStar_ST.op_Colon_Equals stack uu____13895);
    (let uu___420_13947 = env  in
     let uu____13948 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13951 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13954 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13961 =
       let uu____13976 =
         let uu____13980 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13980  in
       let uu____14012 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13976, uu____14012)  in
     let uu____14061 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14064 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14067 =
       let uu____14070 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14070  in
     let uu____14090 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14103 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___420_13947.solver);
       range = (uu___420_13947.range);
       curmodule = (uu___420_13947.curmodule);
       gamma = (uu___420_13947.gamma);
       gamma_sig = (uu___420_13947.gamma_sig);
       gamma_cache = uu____13948;
       modules = (uu___420_13947.modules);
       expected_typ = (uu___420_13947.expected_typ);
       sigtab = uu____13951;
       attrtab = uu____13954;
       is_pattern = (uu___420_13947.is_pattern);
       instantiate_imp = (uu___420_13947.instantiate_imp);
       effects = (uu___420_13947.effects);
       generalize = (uu___420_13947.generalize);
       letrecs = (uu___420_13947.letrecs);
       top_level = (uu___420_13947.top_level);
       check_uvars = (uu___420_13947.check_uvars);
       use_eq = (uu___420_13947.use_eq);
       is_iface = (uu___420_13947.is_iface);
       admit = (uu___420_13947.admit);
       lax = (uu___420_13947.lax);
       lax_universes = (uu___420_13947.lax_universes);
       phase1 = (uu___420_13947.phase1);
       failhard = (uu___420_13947.failhard);
       nosynth = (uu___420_13947.nosynth);
       uvar_subtyping = (uu___420_13947.uvar_subtyping);
       tc_term = (uu___420_13947.tc_term);
       type_of = (uu___420_13947.type_of);
       universe_of = (uu___420_13947.universe_of);
       check_type_of = (uu___420_13947.check_type_of);
       use_bv_sorts = (uu___420_13947.use_bv_sorts);
       qtbl_name_and_index = uu____13961;
       normalized_eff_names = uu____14061;
       fv_delta_depths = uu____14064;
       proof_ns = (uu___420_13947.proof_ns);
       synth_hook = (uu___420_13947.synth_hook);
       splice = (uu___420_13947.splice);
       postprocess = (uu___420_13947.postprocess);
       is_native_tactic = (uu___420_13947.is_native_tactic);
       identifier_info = uu____14067;
       tc_hooks = (uu___420_13947.tc_hooks);
       dsenv = (uu___420_13947.dsenv);
       nbe = (uu___420_13947.nbe);
       strict_args_tab = uu____14090;
       erasable_types_tab = uu____14103
     })
  
let (pop_stack : unit -> env) =
  fun uu____14113  ->
    let uu____14114 = FStar_ST.op_Bang stack  in
    match uu____14114 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14168 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14258  ->
           let uu____14259 = snapshot_stack env  in
           match uu____14259 with
           | (stack_depth,env1) ->
               let uu____14293 = snapshot_query_indices ()  in
               (match uu____14293 with
                | (query_indices_depth,()) ->
                    let uu____14326 = (env1.solver).snapshot msg  in
                    (match uu____14326 with
                     | (solver_depth,()) ->
                         let uu____14383 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14383 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___445_14450 = env1  in
                                 {
                                   solver = (uu___445_14450.solver);
                                   range = (uu___445_14450.range);
                                   curmodule = (uu___445_14450.curmodule);
                                   gamma = (uu___445_14450.gamma);
                                   gamma_sig = (uu___445_14450.gamma_sig);
                                   gamma_cache = (uu___445_14450.gamma_cache);
                                   modules = (uu___445_14450.modules);
                                   expected_typ =
                                     (uu___445_14450.expected_typ);
                                   sigtab = (uu___445_14450.sigtab);
                                   attrtab = (uu___445_14450.attrtab);
                                   is_pattern = (uu___445_14450.is_pattern);
                                   instantiate_imp =
                                     (uu___445_14450.instantiate_imp);
                                   effects = (uu___445_14450.effects);
                                   generalize = (uu___445_14450.generalize);
                                   letrecs = (uu___445_14450.letrecs);
                                   top_level = (uu___445_14450.top_level);
                                   check_uvars = (uu___445_14450.check_uvars);
                                   use_eq = (uu___445_14450.use_eq);
                                   is_iface = (uu___445_14450.is_iface);
                                   admit = (uu___445_14450.admit);
                                   lax = (uu___445_14450.lax);
                                   lax_universes =
                                     (uu___445_14450.lax_universes);
                                   phase1 = (uu___445_14450.phase1);
                                   failhard = (uu___445_14450.failhard);
                                   nosynth = (uu___445_14450.nosynth);
                                   uvar_subtyping =
                                     (uu___445_14450.uvar_subtyping);
                                   tc_term = (uu___445_14450.tc_term);
                                   type_of = (uu___445_14450.type_of);
                                   universe_of = (uu___445_14450.universe_of);
                                   check_type_of =
                                     (uu___445_14450.check_type_of);
                                   use_bv_sorts =
                                     (uu___445_14450.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___445_14450.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___445_14450.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___445_14450.fv_delta_depths);
                                   proof_ns = (uu___445_14450.proof_ns);
                                   synth_hook = (uu___445_14450.synth_hook);
                                   splice = (uu___445_14450.splice);
                                   postprocess = (uu___445_14450.postprocess);
                                   is_native_tactic =
                                     (uu___445_14450.is_native_tactic);
                                   identifier_info =
                                     (uu___445_14450.identifier_info);
                                   tc_hooks = (uu___445_14450.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___445_14450.nbe);
                                   strict_args_tab =
                                     (uu___445_14450.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___445_14450.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14484  ->
             let uu____14485 =
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
             match uu____14485 with
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
                             ((let uu____14665 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14665
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14681 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14681
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14713,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14755 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14785  ->
                  match uu____14785 with
                  | (m,uu____14793) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14755 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___490_14808 = env  in
               {
                 solver = (uu___490_14808.solver);
                 range = (uu___490_14808.range);
                 curmodule = (uu___490_14808.curmodule);
                 gamma = (uu___490_14808.gamma);
                 gamma_sig = (uu___490_14808.gamma_sig);
                 gamma_cache = (uu___490_14808.gamma_cache);
                 modules = (uu___490_14808.modules);
                 expected_typ = (uu___490_14808.expected_typ);
                 sigtab = (uu___490_14808.sigtab);
                 attrtab = (uu___490_14808.attrtab);
                 is_pattern = (uu___490_14808.is_pattern);
                 instantiate_imp = (uu___490_14808.instantiate_imp);
                 effects = (uu___490_14808.effects);
                 generalize = (uu___490_14808.generalize);
                 letrecs = (uu___490_14808.letrecs);
                 top_level = (uu___490_14808.top_level);
                 check_uvars = (uu___490_14808.check_uvars);
                 use_eq = (uu___490_14808.use_eq);
                 is_iface = (uu___490_14808.is_iface);
                 admit = (uu___490_14808.admit);
                 lax = (uu___490_14808.lax);
                 lax_universes = (uu___490_14808.lax_universes);
                 phase1 = (uu___490_14808.phase1);
                 failhard = (uu___490_14808.failhard);
                 nosynth = (uu___490_14808.nosynth);
                 uvar_subtyping = (uu___490_14808.uvar_subtyping);
                 tc_term = (uu___490_14808.tc_term);
                 type_of = (uu___490_14808.type_of);
                 universe_of = (uu___490_14808.universe_of);
                 check_type_of = (uu___490_14808.check_type_of);
                 use_bv_sorts = (uu___490_14808.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___490_14808.normalized_eff_names);
                 fv_delta_depths = (uu___490_14808.fv_delta_depths);
                 proof_ns = (uu___490_14808.proof_ns);
                 synth_hook = (uu___490_14808.synth_hook);
                 splice = (uu___490_14808.splice);
                 postprocess = (uu___490_14808.postprocess);
                 is_native_tactic = (uu___490_14808.is_native_tactic);
                 identifier_info = (uu___490_14808.identifier_info);
                 tc_hooks = (uu___490_14808.tc_hooks);
                 dsenv = (uu___490_14808.dsenv);
                 nbe = (uu___490_14808.nbe);
                 strict_args_tab = (uu___490_14808.strict_args_tab);
                 erasable_types_tab = (uu___490_14808.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14825,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___499_14841 = env  in
               {
                 solver = (uu___499_14841.solver);
                 range = (uu___499_14841.range);
                 curmodule = (uu___499_14841.curmodule);
                 gamma = (uu___499_14841.gamma);
                 gamma_sig = (uu___499_14841.gamma_sig);
                 gamma_cache = (uu___499_14841.gamma_cache);
                 modules = (uu___499_14841.modules);
                 expected_typ = (uu___499_14841.expected_typ);
                 sigtab = (uu___499_14841.sigtab);
                 attrtab = (uu___499_14841.attrtab);
                 is_pattern = (uu___499_14841.is_pattern);
                 instantiate_imp = (uu___499_14841.instantiate_imp);
                 effects = (uu___499_14841.effects);
                 generalize = (uu___499_14841.generalize);
                 letrecs = (uu___499_14841.letrecs);
                 top_level = (uu___499_14841.top_level);
                 check_uvars = (uu___499_14841.check_uvars);
                 use_eq = (uu___499_14841.use_eq);
                 is_iface = (uu___499_14841.is_iface);
                 admit = (uu___499_14841.admit);
                 lax = (uu___499_14841.lax);
                 lax_universes = (uu___499_14841.lax_universes);
                 phase1 = (uu___499_14841.phase1);
                 failhard = (uu___499_14841.failhard);
                 nosynth = (uu___499_14841.nosynth);
                 uvar_subtyping = (uu___499_14841.uvar_subtyping);
                 tc_term = (uu___499_14841.tc_term);
                 type_of = (uu___499_14841.type_of);
                 universe_of = (uu___499_14841.universe_of);
                 check_type_of = (uu___499_14841.check_type_of);
                 use_bv_sorts = (uu___499_14841.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___499_14841.normalized_eff_names);
                 fv_delta_depths = (uu___499_14841.fv_delta_depths);
                 proof_ns = (uu___499_14841.proof_ns);
                 synth_hook = (uu___499_14841.synth_hook);
                 splice = (uu___499_14841.splice);
                 postprocess = (uu___499_14841.postprocess);
                 is_native_tactic = (uu___499_14841.is_native_tactic);
                 identifier_info = (uu___499_14841.identifier_info);
                 tc_hooks = (uu___499_14841.tc_hooks);
                 dsenv = (uu___499_14841.dsenv);
                 nbe = (uu___499_14841.nbe);
                 strict_args_tab = (uu___499_14841.strict_args_tab);
                 erasable_types_tab = (uu___499_14841.erasable_types_tab)
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
        (let uu___506_14884 = e  in
         {
           solver = (uu___506_14884.solver);
           range = r;
           curmodule = (uu___506_14884.curmodule);
           gamma = (uu___506_14884.gamma);
           gamma_sig = (uu___506_14884.gamma_sig);
           gamma_cache = (uu___506_14884.gamma_cache);
           modules = (uu___506_14884.modules);
           expected_typ = (uu___506_14884.expected_typ);
           sigtab = (uu___506_14884.sigtab);
           attrtab = (uu___506_14884.attrtab);
           is_pattern = (uu___506_14884.is_pattern);
           instantiate_imp = (uu___506_14884.instantiate_imp);
           effects = (uu___506_14884.effects);
           generalize = (uu___506_14884.generalize);
           letrecs = (uu___506_14884.letrecs);
           top_level = (uu___506_14884.top_level);
           check_uvars = (uu___506_14884.check_uvars);
           use_eq = (uu___506_14884.use_eq);
           is_iface = (uu___506_14884.is_iface);
           admit = (uu___506_14884.admit);
           lax = (uu___506_14884.lax);
           lax_universes = (uu___506_14884.lax_universes);
           phase1 = (uu___506_14884.phase1);
           failhard = (uu___506_14884.failhard);
           nosynth = (uu___506_14884.nosynth);
           uvar_subtyping = (uu___506_14884.uvar_subtyping);
           tc_term = (uu___506_14884.tc_term);
           type_of = (uu___506_14884.type_of);
           universe_of = (uu___506_14884.universe_of);
           check_type_of = (uu___506_14884.check_type_of);
           use_bv_sorts = (uu___506_14884.use_bv_sorts);
           qtbl_name_and_index = (uu___506_14884.qtbl_name_and_index);
           normalized_eff_names = (uu___506_14884.normalized_eff_names);
           fv_delta_depths = (uu___506_14884.fv_delta_depths);
           proof_ns = (uu___506_14884.proof_ns);
           synth_hook = (uu___506_14884.synth_hook);
           splice = (uu___506_14884.splice);
           postprocess = (uu___506_14884.postprocess);
           is_native_tactic = (uu___506_14884.is_native_tactic);
           identifier_info = (uu___506_14884.identifier_info);
           tc_hooks = (uu___506_14884.tc_hooks);
           dsenv = (uu___506_14884.dsenv);
           nbe = (uu___506_14884.nbe);
           strict_args_tab = (uu___506_14884.strict_args_tab);
           erasable_types_tab = (uu___506_14884.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14904 =
        let uu____14905 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14905 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14904
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14960 =
          let uu____14961 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14961 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14960
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15016 =
          let uu____15017 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15017 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15016
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15072 =
        let uu____15073 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15073 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15072
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___523_15137 = env  in
      {
        solver = (uu___523_15137.solver);
        range = (uu___523_15137.range);
        curmodule = lid;
        gamma = (uu___523_15137.gamma);
        gamma_sig = (uu___523_15137.gamma_sig);
        gamma_cache = (uu___523_15137.gamma_cache);
        modules = (uu___523_15137.modules);
        expected_typ = (uu___523_15137.expected_typ);
        sigtab = (uu___523_15137.sigtab);
        attrtab = (uu___523_15137.attrtab);
        is_pattern = (uu___523_15137.is_pattern);
        instantiate_imp = (uu___523_15137.instantiate_imp);
        effects = (uu___523_15137.effects);
        generalize = (uu___523_15137.generalize);
        letrecs = (uu___523_15137.letrecs);
        top_level = (uu___523_15137.top_level);
        check_uvars = (uu___523_15137.check_uvars);
        use_eq = (uu___523_15137.use_eq);
        is_iface = (uu___523_15137.is_iface);
        admit = (uu___523_15137.admit);
        lax = (uu___523_15137.lax);
        lax_universes = (uu___523_15137.lax_universes);
        phase1 = (uu___523_15137.phase1);
        failhard = (uu___523_15137.failhard);
        nosynth = (uu___523_15137.nosynth);
        uvar_subtyping = (uu___523_15137.uvar_subtyping);
        tc_term = (uu___523_15137.tc_term);
        type_of = (uu___523_15137.type_of);
        universe_of = (uu___523_15137.universe_of);
        check_type_of = (uu___523_15137.check_type_of);
        use_bv_sorts = (uu___523_15137.use_bv_sorts);
        qtbl_name_and_index = (uu___523_15137.qtbl_name_and_index);
        normalized_eff_names = (uu___523_15137.normalized_eff_names);
        fv_delta_depths = (uu___523_15137.fv_delta_depths);
        proof_ns = (uu___523_15137.proof_ns);
        synth_hook = (uu___523_15137.synth_hook);
        splice = (uu___523_15137.splice);
        postprocess = (uu___523_15137.postprocess);
        is_native_tactic = (uu___523_15137.is_native_tactic);
        identifier_info = (uu___523_15137.identifier_info);
        tc_hooks = (uu___523_15137.tc_hooks);
        dsenv = (uu___523_15137.dsenv);
        nbe = (uu___523_15137.nbe);
        strict_args_tab = (uu___523_15137.strict_args_tab);
        erasable_types_tab = (uu___523_15137.erasable_types_tab)
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
      let uu____15168 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15168
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15181 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15181)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15196 =
      let uu____15198 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15198  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15196)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15207  ->
    let uu____15208 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15208
  
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
      | ((formals,t),uu____15308) ->
          let vs = mk_univ_subst formals us  in
          let uu____15332 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15332)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15349  ->
    match uu___1_15349 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15375  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15395 = inst_tscheme t  in
      match uu____15395 with
      | (us,t1) ->
          let uu____15406 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15406)
  
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
          let uu____15431 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15433 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15431 uu____15433
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
        fun uu____15460  ->
          match uu____15460 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15474 =
                    let uu____15476 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15480 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15484 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15486 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15476 uu____15480 uu____15484 uu____15486
                     in
                  failwith uu____15474)
               else ();
               (let uu____15491 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15491))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15509 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15520 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15531 -> false
  
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
             | ([],uu____15579) -> Maybe
             | (uu____15586,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15606 -> No  in
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
          let uu____15700 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15700 with
          | FStar_Pervasives_Native.None  ->
              let uu____15723 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15767  ->
                     match uu___2_15767 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15806 = FStar_Ident.lid_equals lid l  in
                         if uu____15806
                         then
                           let uu____15829 =
                             let uu____15848 =
                               let uu____15863 = inst_tscheme t  in
                               FStar_Util.Inl uu____15863  in
                             let uu____15878 = FStar_Ident.range_of_lid l  in
                             (uu____15848, uu____15878)  in
                           FStar_Pervasives_Native.Some uu____15829
                         else FStar_Pervasives_Native.None
                     | uu____15931 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15723
                (fun uu____15969  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15978  ->
                        match uu___3_15978 with
                        | (uu____15981,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15983);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15984;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15985;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15986;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15987;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16007 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16007
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
                                  uu____16059 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16066 -> cache t  in
                            let uu____16067 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16067 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16073 =
                                   let uu____16074 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16074)
                                    in
                                 maybe_cache uu____16073)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16145 = find_in_sigtab env lid  in
         match uu____16145 with
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
      let uu____16226 = lookup_qname env lid  in
      match uu____16226 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16247,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16361 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16361 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16406 =
          let uu____16409 = lookup_attr env1 attr  in se1 :: uu____16409  in
        FStar_Util.smap_add (attrtab env1) attr uu____16406  in
      FStar_List.iter
        (fun attr  ->
           let uu____16419 =
             let uu____16420 = FStar_Syntax_Subst.compress attr  in
             uu____16420.FStar_Syntax_Syntax.n  in
           match uu____16419 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16424 =
                 let uu____16426 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16426.FStar_Ident.str  in
               add_one1 env se uu____16424
           | uu____16427 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16450) ->
          add_sigelts env ses
      | uu____16459 ->
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
        (fun uu___4_16497  ->
           match uu___4_16497 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16515 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16577,lb::[]),uu____16579) ->
            let uu____16588 =
              let uu____16597 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16606 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16597, uu____16606)  in
            FStar_Pervasives_Native.Some uu____16588
        | FStar_Syntax_Syntax.Sig_let ((uu____16619,lbs),uu____16621) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16653 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16666 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16666
                     then
                       let uu____16679 =
                         let uu____16688 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16697 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16688, uu____16697)  in
                       FStar_Pervasives_Native.Some uu____16679
                     else FStar_Pervasives_Native.None)
        | uu____16720 -> FStar_Pervasives_Native.None
  
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
                    let uu____16812 =
                      let uu____16814 =
                        let uu____16816 =
                          let uu____16818 =
                            let uu____16820 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16826 =
                              let uu____16828 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16828  in
                            Prims.op_Hat uu____16820 uu____16826  in
                          Prims.op_Hat ", expected " uu____16818  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16816
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16814
                       in
                    failwith uu____16812
                  else ());
             (let uu____16835 =
                let uu____16844 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16844, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16835))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16864,uu____16865) ->
            let uu____16870 =
              let uu____16879 =
                let uu____16884 =
                  let uu____16885 =
                    let uu____16888 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16888  in
                  (us, uu____16885)  in
                inst_ts us_opt uu____16884  in
              (uu____16879, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16870
        | uu____16907 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16996 =
          match uu____16996 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17092,uvs,t,uu____17095,uu____17096,uu____17097);
                      FStar_Syntax_Syntax.sigrng = uu____17098;
                      FStar_Syntax_Syntax.sigquals = uu____17099;
                      FStar_Syntax_Syntax.sigmeta = uu____17100;
                      FStar_Syntax_Syntax.sigattrs = uu____17101;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17124 =
                     let uu____17133 = inst_tscheme1 (uvs, t)  in
                     (uu____17133, rng)  in
                   FStar_Pervasives_Native.Some uu____17124
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17157;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17159;
                      FStar_Syntax_Syntax.sigattrs = uu____17160;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17177 =
                     let uu____17179 = in_cur_mod env l  in uu____17179 = Yes
                      in
                   if uu____17177
                   then
                     let uu____17191 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17191
                      then
                        let uu____17207 =
                          let uu____17216 = inst_tscheme1 (uvs, t)  in
                          (uu____17216, rng)  in
                        FStar_Pervasives_Native.Some uu____17207
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17249 =
                        let uu____17258 = inst_tscheme1 (uvs, t)  in
                        (uu____17258, rng)  in
                      FStar_Pervasives_Native.Some uu____17249)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17283,uu____17284);
                      FStar_Syntax_Syntax.sigrng = uu____17285;
                      FStar_Syntax_Syntax.sigquals = uu____17286;
                      FStar_Syntax_Syntax.sigmeta = uu____17287;
                      FStar_Syntax_Syntax.sigattrs = uu____17288;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17329 =
                          let uu____17338 = inst_tscheme1 (uvs, k)  in
                          (uu____17338, rng)  in
                        FStar_Pervasives_Native.Some uu____17329
                    | uu____17359 ->
                        let uu____17360 =
                          let uu____17369 =
                            let uu____17374 =
                              let uu____17375 =
                                let uu____17378 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17378
                                 in
                              (uvs, uu____17375)  in
                            inst_tscheme1 uu____17374  in
                          (uu____17369, rng)  in
                        FStar_Pervasives_Native.Some uu____17360)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17401,uu____17402);
                      FStar_Syntax_Syntax.sigrng = uu____17403;
                      FStar_Syntax_Syntax.sigquals = uu____17404;
                      FStar_Syntax_Syntax.sigmeta = uu____17405;
                      FStar_Syntax_Syntax.sigattrs = uu____17406;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17448 =
                          let uu____17457 = inst_tscheme_with (uvs, k) us  in
                          (uu____17457, rng)  in
                        FStar_Pervasives_Native.Some uu____17448
                    | uu____17478 ->
                        let uu____17479 =
                          let uu____17488 =
                            let uu____17493 =
                              let uu____17494 =
                                let uu____17497 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17497
                                 in
                              (uvs, uu____17494)  in
                            inst_tscheme_with uu____17493 us  in
                          (uu____17488, rng)  in
                        FStar_Pervasives_Native.Some uu____17479)
               | FStar_Util.Inr se ->
                   let uu____17533 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17554;
                          FStar_Syntax_Syntax.sigrng = uu____17555;
                          FStar_Syntax_Syntax.sigquals = uu____17556;
                          FStar_Syntax_Syntax.sigmeta = uu____17557;
                          FStar_Syntax_Syntax.sigattrs = uu____17558;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17573 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17533
                     (FStar_Util.map_option
                        (fun uu____17621  ->
                           match uu____17621 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17652 =
          let uu____17663 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17663 mapper  in
        match uu____17652 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17737 =
              let uu____17748 =
                let uu____17755 =
                  let uu___854_17758 = t  in
                  let uu____17759 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___854_17758.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17759;
                    FStar_Syntax_Syntax.vars =
                      (uu___854_17758.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17755)  in
              (uu____17748, r)  in
            FStar_Pervasives_Native.Some uu____17737
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17808 = lookup_qname env l  in
      match uu____17808 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17829 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17883 = try_lookup_bv env bv  in
      match uu____17883 with
      | FStar_Pervasives_Native.None  ->
          let uu____17898 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17898 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17914 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17915 =
            let uu____17916 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17916  in
          (uu____17914, uu____17915)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17938 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17938 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18004 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18004  in
          let uu____18005 =
            let uu____18014 =
              let uu____18019 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18019)  in
            (uu____18014, r1)  in
          FStar_Pervasives_Native.Some uu____18005
  
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
        let uu____18054 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18054 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18087,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18112 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18112  in
            let uu____18113 =
              let uu____18118 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18118, r1)  in
            FStar_Pervasives_Native.Some uu____18113
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18142 = try_lookup_lid env l  in
      match uu____18142 with
      | FStar_Pervasives_Native.None  ->
          let uu____18169 = name_not_found l  in
          let uu____18175 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18169 uu____18175
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18218  ->
              match uu___5_18218 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18222 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18243 = lookup_qname env lid  in
      match uu____18243 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18252,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18255;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18257;
              FStar_Syntax_Syntax.sigattrs = uu____18258;_},FStar_Pervasives_Native.None
            ),uu____18259)
          ->
          let uu____18308 =
            let uu____18315 =
              let uu____18316 =
                let uu____18319 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18319 t  in
              (uvs, uu____18316)  in
            (uu____18315, q)  in
          FStar_Pervasives_Native.Some uu____18308
      | uu____18332 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18354 = lookup_qname env lid  in
      match uu____18354 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18359,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18362;
              FStar_Syntax_Syntax.sigquals = uu____18363;
              FStar_Syntax_Syntax.sigmeta = uu____18364;
              FStar_Syntax_Syntax.sigattrs = uu____18365;_},FStar_Pervasives_Native.None
            ),uu____18366)
          ->
          let uu____18415 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18415 (uvs, t)
      | uu____18420 ->
          let uu____18421 = name_not_found lid  in
          let uu____18427 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18421 uu____18427
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18447 = lookup_qname env lid  in
      match uu____18447 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18452,uvs,t,uu____18455,uu____18456,uu____18457);
              FStar_Syntax_Syntax.sigrng = uu____18458;
              FStar_Syntax_Syntax.sigquals = uu____18459;
              FStar_Syntax_Syntax.sigmeta = uu____18460;
              FStar_Syntax_Syntax.sigattrs = uu____18461;_},FStar_Pervasives_Native.None
            ),uu____18462)
          ->
          let uu____18517 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18517 (uvs, t)
      | uu____18522 ->
          let uu____18523 = name_not_found lid  in
          let uu____18529 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18523 uu____18529
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18552 = lookup_qname env lid  in
      match uu____18552 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18560,uu____18561,uu____18562,uu____18563,uu____18564,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18566;
              FStar_Syntax_Syntax.sigquals = uu____18567;
              FStar_Syntax_Syntax.sigmeta = uu____18568;
              FStar_Syntax_Syntax.sigattrs = uu____18569;_},uu____18570),uu____18571)
          -> (true, dcs)
      | uu____18634 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18650 = lookup_qname env lid  in
      match uu____18650 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18651,uu____18652,uu____18653,l,uu____18655,uu____18656);
              FStar_Syntax_Syntax.sigrng = uu____18657;
              FStar_Syntax_Syntax.sigquals = uu____18658;
              FStar_Syntax_Syntax.sigmeta = uu____18659;
              FStar_Syntax_Syntax.sigattrs = uu____18660;_},uu____18661),uu____18662)
          -> l
      | uu____18719 ->
          let uu____18720 =
            let uu____18722 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18722  in
          failwith uu____18720
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18792)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18849) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18873 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18873
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18908 -> FStar_Pervasives_Native.None)
          | uu____18917 -> FStar_Pervasives_Native.None
  
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
        let uu____18979 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18979
  
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
        let uu____19012 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19012
  
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
             (FStar_Util.Inl uu____19064,uu____19065) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19114),uu____19115) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19164 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19182 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19192 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19209 ->
                  let uu____19216 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19216
              | FStar_Syntax_Syntax.Sig_let ((uu____19217,lbs),uu____19219)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19235 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19235
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19242 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19250 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19251 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19258 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19259 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19260 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19261 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19274 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19292 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19292
           (fun d_opt  ->
              let uu____19305 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19305
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19315 =
                   let uu____19318 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19318  in
                 match uu____19315 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19319 =
                       let uu____19321 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19321
                        in
                     failwith uu____19319
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19326 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19326
                       then
                         let uu____19329 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19331 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19333 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19329 uu____19331 uu____19333
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
        (FStar_Util.Inr (se,uu____19358),uu____19359) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19408 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19430),uu____19431) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19480 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19502 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19502
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19535 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19535 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19557 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19566 =
                        let uu____19567 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19567.FStar_Syntax_Syntax.n  in
                      match uu____19566 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19572 -> false))
               in
            (true, uu____19557)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19595 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19595
  
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
          let uu____19667 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19667.FStar_Ident.str  in
        let uu____19668 = FStar_Util.smap_try_find tab s  in
        match uu____19668 with
        | FStar_Pervasives_Native.None  ->
            let uu____19671 = f ()  in
            (match uu____19671 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____19709 =
        let uu____19710 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____19710 with
        | (ex,erasable1) ->
            let uu____19729 =
              fv_exists_and_has_attr env
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                FStar_Parser_Const.must_erase_for_extraction_attr
               in
            (match uu____19729 with
             | (ex',must_erase_for_extraction_attr1) ->
                 ((ex || ex'),
                   (erasable1 || must_erase_for_extraction_attr1)))
         in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19763 =
        let uu____19764 = FStar_Syntax_Util.unrefine t  in
        uu____19764.FStar_Syntax_Syntax.n  in
      match uu____19763 with
      | FStar_Syntax_Syntax.Tm_type uu____19768 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____19772) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____19798) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____19803,c) ->
          ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
             (non_informative env (FStar_Syntax_Util.comp_result c)))
            ||
            (FStar_Syntax_Util.is_ghost_effect
               (FStar_Syntax_Util.comp_effect_name c))
      | uu____19825 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____19858 =
        let attrs =
          let uu____19864 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____19864  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____19904 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____19904)
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
      let uu____19949 = lookup_qname env ftv  in
      match uu____19949 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19953) ->
          let uu____19998 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19998 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20019,t),r) ->
               let uu____20034 =
                 let uu____20035 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20035 t  in
               FStar_Pervasives_Native.Some uu____20034)
      | uu____20036 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20048 = try_lookup_effect_lid env ftv  in
      match uu____20048 with
      | FStar_Pervasives_Native.None  ->
          let uu____20051 = name_not_found ftv  in
          let uu____20057 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20051 uu____20057
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
        let uu____20081 = lookup_qname env lid0  in
        match uu____20081 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20092);
                FStar_Syntax_Syntax.sigrng = uu____20093;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20095;
                FStar_Syntax_Syntax.sigattrs = uu____20096;_},FStar_Pervasives_Native.None
              ),uu____20097)
            ->
            let lid1 =
              let uu____20151 =
                let uu____20152 = FStar_Ident.range_of_lid lid  in
                let uu____20153 =
                  let uu____20154 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20154  in
                FStar_Range.set_use_range uu____20152 uu____20153  in
              FStar_Ident.set_lid_range lid uu____20151  in
            let uu____20155 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20161  ->
                      match uu___6_20161 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20164 -> false))
               in
            if uu____20155
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20183 =
                      let uu____20185 =
                        let uu____20187 = get_range env  in
                        FStar_Range.string_of_range uu____20187  in
                      let uu____20188 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20190 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20185 uu____20188 uu____20190
                       in
                    failwith uu____20183)
                  in
               match (binders, univs1) with
               | ([],uu____20211) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20237,uu____20238::uu____20239::uu____20240) ->
                   let uu____20261 =
                     let uu____20263 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20265 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20263 uu____20265
                      in
                   failwith uu____20261
               | uu____20276 ->
                   let uu____20291 =
                     let uu____20296 =
                       let uu____20297 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20297)  in
                     inst_tscheme_with uu____20296 insts  in
                   (match uu____20291 with
                    | (uu____20310,t) ->
                        let t1 =
                          let uu____20313 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20313 t  in
                        let uu____20314 =
                          let uu____20315 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20315.FStar_Syntax_Syntax.n  in
                        (match uu____20314 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20350 -> failwith "Impossible")))
        | uu____20358 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20382 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20382 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20395,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20402 = find1 l2  in
            (match uu____20402 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20409 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20409 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20413 = find1 l  in
            (match uu____20413 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20418 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20418
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20433 = lookup_qname env l1  in
      match uu____20433 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20436;
              FStar_Syntax_Syntax.sigrng = uu____20437;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20439;
              FStar_Syntax_Syntax.sigattrs = uu____20440;_},uu____20441),uu____20442)
          -> q
      | uu____20493 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20517 =
          let uu____20518 =
            let uu____20520 = FStar_Util.string_of_int i  in
            let uu____20522 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20520 uu____20522
             in
          failwith uu____20518  in
        let uu____20525 = lookup_datacon env lid  in
        match uu____20525 with
        | (uu____20530,t) ->
            let uu____20532 =
              let uu____20533 = FStar_Syntax_Subst.compress t  in
              uu____20533.FStar_Syntax_Syntax.n  in
            (match uu____20532 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20537) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20581 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20581
                      FStar_Pervasives_Native.fst)
             | uu____20592 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20606 = lookup_qname env l  in
      match uu____20606 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20608,uu____20609,uu____20610);
              FStar_Syntax_Syntax.sigrng = uu____20611;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20613;
              FStar_Syntax_Syntax.sigattrs = uu____20614;_},uu____20615),uu____20616)
          ->
          FStar_Util.for_some
            (fun uu___7_20669  ->
               match uu___7_20669 with
               | FStar_Syntax_Syntax.Projector uu____20671 -> true
               | uu____20677 -> false) quals
      | uu____20679 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20693 = lookup_qname env lid  in
      match uu____20693 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20695,uu____20696,uu____20697,uu____20698,uu____20699,uu____20700);
              FStar_Syntax_Syntax.sigrng = uu____20701;
              FStar_Syntax_Syntax.sigquals = uu____20702;
              FStar_Syntax_Syntax.sigmeta = uu____20703;
              FStar_Syntax_Syntax.sigattrs = uu____20704;_},uu____20705),uu____20706)
          -> true
      | uu____20764 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20778 = lookup_qname env lid  in
      match uu____20778 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20780,uu____20781,uu____20782,uu____20783,uu____20784,uu____20785);
              FStar_Syntax_Syntax.sigrng = uu____20786;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20788;
              FStar_Syntax_Syntax.sigattrs = uu____20789;_},uu____20790),uu____20791)
          ->
          FStar_Util.for_some
            (fun uu___8_20852  ->
               match uu___8_20852 with
               | FStar_Syntax_Syntax.RecordType uu____20854 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20864 -> true
               | uu____20874 -> false) quals
      | uu____20876 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20886,uu____20887);
            FStar_Syntax_Syntax.sigrng = uu____20888;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20890;
            FStar_Syntax_Syntax.sigattrs = uu____20891;_},uu____20892),uu____20893)
        ->
        FStar_Util.for_some
          (fun uu___9_20950  ->
             match uu___9_20950 with
             | FStar_Syntax_Syntax.Action uu____20952 -> true
             | uu____20954 -> false) quals
    | uu____20956 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20970 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20970
  
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
      let uu____20987 =
        let uu____20988 = FStar_Syntax_Util.un_uinst head1  in
        uu____20988.FStar_Syntax_Syntax.n  in
      match uu____20987 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20994 ->
               true
           | uu____20997 -> false)
      | uu____20999 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21013 = lookup_qname env l  in
      match uu____21013 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21016),uu____21017) ->
          FStar_Util.for_some
            (fun uu___10_21065  ->
               match uu___10_21065 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21068 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21070 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21146 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21164) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21182 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21190 ->
                 FStar_Pervasives_Native.Some true
             | uu____21209 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21212 =
        let uu____21216 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21216 mapper  in
      match uu____21212 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21276 = lookup_qname env lid  in
      match uu____21276 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21280,uu____21281,tps,uu____21283,uu____21284,uu____21285);
              FStar_Syntax_Syntax.sigrng = uu____21286;
              FStar_Syntax_Syntax.sigquals = uu____21287;
              FStar_Syntax_Syntax.sigmeta = uu____21288;
              FStar_Syntax_Syntax.sigattrs = uu____21289;_},uu____21290),uu____21291)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21357 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21403  ->
              match uu____21403 with
              | (d,uu____21412) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21428 = effect_decl_opt env l  in
      match uu____21428 with
      | FStar_Pervasives_Native.None  ->
          let uu____21443 = name_not_found l  in
          let uu____21449 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21443 uu____21449
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21472  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21491  ->
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
        let uu____21523 = FStar_Ident.lid_equals l1 l2  in
        if uu____21523
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21534 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21534
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21545 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21598  ->
                        match uu____21598 with
                        | (m1,m2,uu____21612,uu____21613,uu____21614) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21545 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21631 =
                    let uu____21637 =
                      let uu____21639 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21641 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21639
                        uu____21641
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21637)
                     in
                  FStar_Errors.raise_error uu____21631 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21651,uu____21652,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21686 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21686
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
  'Auu____21706 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21706) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21735 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21761  ->
                match uu____21761 with
                | (d,uu____21768) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21735 with
      | FStar_Pervasives_Native.None  ->
          let uu____21779 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21779
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21794 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21794 with
           | (uu____21805,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21823)::(wp,uu____21825)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21881 -> failwith "Impossible"))
  
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
        | uu____21946 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21959 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21959 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21976 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21976 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22001 =
                     let uu____22007 =
                       let uu____22009 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22017 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22028 =
                         let uu____22030 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22030  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22009 uu____22017 uu____22028
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22007)
                      in
                   FStar_Errors.raise_error uu____22001
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22038 =
                     let uu____22049 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22049 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22086  ->
                        fun uu____22087  ->
                          match (uu____22086, uu____22087) with
                          | ((x,uu____22117),(t,uu____22119)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22038
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22150 =
                     let uu___1582_22151 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1582_22151.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1582_22151.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1582_22151.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1582_22151.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22150
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22163 .
    'Auu____22163 ->
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
          let uu____22193 = effect_decl_opt env effect_name  in
          match uu____22193 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22236 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22259 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22298 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22298
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22303 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22303
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____22314 =
                     let uu____22317 = get_range env  in
                     let uu____22318 =
                       let uu____22325 =
                         let uu____22326 =
                           let uu____22343 =
                             let uu____22354 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22354; wp]  in
                           (repr, uu____22343)  in
                         FStar_Syntax_Syntax.Tm_app uu____22326  in
                       FStar_Syntax_Syntax.mk uu____22325  in
                     uu____22318 FStar_Pervasives_Native.None uu____22317  in
                   FStar_Pervasives_Native.Some uu____22314)
  
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
      | uu____22498 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22513 =
        let uu____22514 = FStar_Syntax_Subst.compress t  in
        uu____22514.FStar_Syntax_Syntax.n  in
      match uu____22513 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22518,c) ->
          is_reifiable_comp env c
      | uu____22540 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22560 =
           let uu____22562 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22562  in
         if uu____22560
         then
           let uu____22565 =
             let uu____22571 =
               let uu____22573 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22573
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22571)  in
           let uu____22577 = get_range env  in
           FStar_Errors.raise_error uu____22565 uu____22577
         else ());
        (let uu____22580 = effect_repr_aux true env c u_c  in
         match uu____22580 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1647_22616 = env  in
        {
          solver = (uu___1647_22616.solver);
          range = (uu___1647_22616.range);
          curmodule = (uu___1647_22616.curmodule);
          gamma = (uu___1647_22616.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1647_22616.gamma_cache);
          modules = (uu___1647_22616.modules);
          expected_typ = (uu___1647_22616.expected_typ);
          sigtab = (uu___1647_22616.sigtab);
          attrtab = (uu___1647_22616.attrtab);
          is_pattern = (uu___1647_22616.is_pattern);
          instantiate_imp = (uu___1647_22616.instantiate_imp);
          effects = (uu___1647_22616.effects);
          generalize = (uu___1647_22616.generalize);
          letrecs = (uu___1647_22616.letrecs);
          top_level = (uu___1647_22616.top_level);
          check_uvars = (uu___1647_22616.check_uvars);
          use_eq = (uu___1647_22616.use_eq);
          is_iface = (uu___1647_22616.is_iface);
          admit = (uu___1647_22616.admit);
          lax = (uu___1647_22616.lax);
          lax_universes = (uu___1647_22616.lax_universes);
          phase1 = (uu___1647_22616.phase1);
          failhard = (uu___1647_22616.failhard);
          nosynth = (uu___1647_22616.nosynth);
          uvar_subtyping = (uu___1647_22616.uvar_subtyping);
          tc_term = (uu___1647_22616.tc_term);
          type_of = (uu___1647_22616.type_of);
          universe_of = (uu___1647_22616.universe_of);
          check_type_of = (uu___1647_22616.check_type_of);
          use_bv_sorts = (uu___1647_22616.use_bv_sorts);
          qtbl_name_and_index = (uu___1647_22616.qtbl_name_and_index);
          normalized_eff_names = (uu___1647_22616.normalized_eff_names);
          fv_delta_depths = (uu___1647_22616.fv_delta_depths);
          proof_ns = (uu___1647_22616.proof_ns);
          synth_hook = (uu___1647_22616.synth_hook);
          splice = (uu___1647_22616.splice);
          postprocess = (uu___1647_22616.postprocess);
          is_native_tactic = (uu___1647_22616.is_native_tactic);
          identifier_info = (uu___1647_22616.identifier_info);
          tc_hooks = (uu___1647_22616.tc_hooks);
          dsenv = (uu___1647_22616.dsenv);
          nbe = (uu___1647_22616.nbe);
          strict_args_tab = (uu___1647_22616.strict_args_tab);
          erasable_types_tab = (uu___1647_22616.erasable_types_tab)
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
    fun uu____22635  ->
      match uu____22635 with
      | (ed,quals) ->
          let effects =
            let uu___1656_22649 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1656_22649.order);
              joins = (uu___1656_22649.joins)
            }  in
          let uu___1659_22658 = env  in
          {
            solver = (uu___1659_22658.solver);
            range = (uu___1659_22658.range);
            curmodule = (uu___1659_22658.curmodule);
            gamma = (uu___1659_22658.gamma);
            gamma_sig = (uu___1659_22658.gamma_sig);
            gamma_cache = (uu___1659_22658.gamma_cache);
            modules = (uu___1659_22658.modules);
            expected_typ = (uu___1659_22658.expected_typ);
            sigtab = (uu___1659_22658.sigtab);
            attrtab = (uu___1659_22658.attrtab);
            is_pattern = (uu___1659_22658.is_pattern);
            instantiate_imp = (uu___1659_22658.instantiate_imp);
            effects;
            generalize = (uu___1659_22658.generalize);
            letrecs = (uu___1659_22658.letrecs);
            top_level = (uu___1659_22658.top_level);
            check_uvars = (uu___1659_22658.check_uvars);
            use_eq = (uu___1659_22658.use_eq);
            is_iface = (uu___1659_22658.is_iface);
            admit = (uu___1659_22658.admit);
            lax = (uu___1659_22658.lax);
            lax_universes = (uu___1659_22658.lax_universes);
            phase1 = (uu___1659_22658.phase1);
            failhard = (uu___1659_22658.failhard);
            nosynth = (uu___1659_22658.nosynth);
            uvar_subtyping = (uu___1659_22658.uvar_subtyping);
            tc_term = (uu___1659_22658.tc_term);
            type_of = (uu___1659_22658.type_of);
            universe_of = (uu___1659_22658.universe_of);
            check_type_of = (uu___1659_22658.check_type_of);
            use_bv_sorts = (uu___1659_22658.use_bv_sorts);
            qtbl_name_and_index = (uu___1659_22658.qtbl_name_and_index);
            normalized_eff_names = (uu___1659_22658.normalized_eff_names);
            fv_delta_depths = (uu___1659_22658.fv_delta_depths);
            proof_ns = (uu___1659_22658.proof_ns);
            synth_hook = (uu___1659_22658.synth_hook);
            splice = (uu___1659_22658.splice);
            postprocess = (uu___1659_22658.postprocess);
            is_native_tactic = (uu___1659_22658.is_native_tactic);
            identifier_info = (uu___1659_22658.identifier_info);
            tc_hooks = (uu___1659_22658.tc_hooks);
            dsenv = (uu___1659_22658.dsenv);
            nbe = (uu___1659_22658.nbe);
            strict_args_tab = (uu___1659_22658.strict_args_tab);
            erasable_types_tab = (uu___1659_22658.erasable_types_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____22698 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____22698  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____22856 = (e1.mlift).mlift_wp u t wp  in
                            let uu____22857 = l1 u t wp e  in
                            l2 u t uu____22856 uu____22857))
            | uu____22858 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____22930 = inst_tscheme_with lift_t [u]  in
        match uu____22930 with
        | (uu____22937,lift_t1) ->
            let uu____22939 =
              let uu____22946 =
                let uu____22947 =
                  let uu____22964 =
                    let uu____22975 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22984 =
                      let uu____22995 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____22995]  in
                    uu____22975 :: uu____22984  in
                  (lift_t1, uu____22964)  in
                FStar_Syntax_Syntax.Tm_app uu____22947  in
              FStar_Syntax_Syntax.mk uu____22946  in
            uu____22939 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____23105 = inst_tscheme_with lift_t [u]  in
        match uu____23105 with
        | (uu____23112,lift_t1) ->
            let uu____23114 =
              let uu____23121 =
                let uu____23122 =
                  let uu____23139 =
                    let uu____23150 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____23159 =
                      let uu____23170 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____23179 =
                        let uu____23190 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____23190]  in
                      uu____23170 :: uu____23179  in
                    uu____23150 :: uu____23159  in
                  (lift_t1, uu____23139)  in
                FStar_Syntax_Syntax.Tm_app uu____23122  in
              FStar_Syntax_Syntax.mk uu____23121  in
            uu____23114 FStar_Pervasives_Native.None
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
          let uu____23292 =
            let uu____23293 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____23293
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____23292  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____23302 =
          let uu____23304 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____23304  in
        let uu____23305 =
          let uu____23307 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____23335 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____23335)
             in
          FStar_Util.dflt "none" uu____23307  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____23302 uu____23305
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____23364  ->
                match uu____23364 with
                | (e,uu____23372) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____23395 =
        match uu____23395 with
        | (i,j) ->
            let uu____23406 = FStar_Ident.lid_equals i j  in
            if uu____23406
            then
              FStar_All.pipe_right (id_edge i)
                (fun _23413  -> FStar_Pervasives_Native.Some _23413)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____23442 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____23452 = FStar_Ident.lid_equals i k  in
                    if uu____23452
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____23466 = FStar_Ident.lid_equals j k
                                 in
                              if uu____23466
                              then []
                              else
                                (let uu____23473 =
                                   let uu____23482 = find_edge order1 (i, k)
                                      in
                                   let uu____23485 = find_edge order1 (k, j)
                                      in
                                   (uu____23482, uu____23485)  in
                                 match uu____23473 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____23500 = compose_edges e1 e2
                                        in
                                     [uu____23500]
                                 | uu____23501 -> [])))))
             in
          FStar_List.append order1 uu____23442  in
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
              let uu____23531 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____23534 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____23534
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____23531
              then
                let uu____23541 =
                  let uu____23547 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____23547)
                   in
                let uu____23551 = get_range env  in
                FStar_Errors.raise_error uu____23541 uu____23551
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____23629 = FStar_Ident.lid_equals i j  in
                           if uu____23629
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____23681 =
                                         let uu____23690 =
                                           find_edge order2 (i, k)  in
                                         let uu____23693 =
                                           find_edge order2 (j, k)  in
                                         (uu____23690, uu____23693)  in
                                       match uu____23681 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____23735,uu____23736)
                                                ->
                                                let uu____23743 =
                                                  let uu____23750 =
                                                    let uu____23752 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23752
                                                     in
                                                  let uu____23755 =
                                                    let uu____23757 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23757
                                                     in
                                                  (uu____23750, uu____23755)
                                                   in
                                                (match uu____23743 with
                                                 | (true ,true ) ->
                                                     let uu____23774 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____23774
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
                                       | uu____23817 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1786_23890 = env.effects  in
         { decls = (uu___1786_23890.decls); order = order2; joins }  in
       let uu___1789_23891 = env  in
       {
         solver = (uu___1789_23891.solver);
         range = (uu___1789_23891.range);
         curmodule = (uu___1789_23891.curmodule);
         gamma = (uu___1789_23891.gamma);
         gamma_sig = (uu___1789_23891.gamma_sig);
         gamma_cache = (uu___1789_23891.gamma_cache);
         modules = (uu___1789_23891.modules);
         expected_typ = (uu___1789_23891.expected_typ);
         sigtab = (uu___1789_23891.sigtab);
         attrtab = (uu___1789_23891.attrtab);
         is_pattern = (uu___1789_23891.is_pattern);
         instantiate_imp = (uu___1789_23891.instantiate_imp);
         effects;
         generalize = (uu___1789_23891.generalize);
         letrecs = (uu___1789_23891.letrecs);
         top_level = (uu___1789_23891.top_level);
         check_uvars = (uu___1789_23891.check_uvars);
         use_eq = (uu___1789_23891.use_eq);
         is_iface = (uu___1789_23891.is_iface);
         admit = (uu___1789_23891.admit);
         lax = (uu___1789_23891.lax);
         lax_universes = (uu___1789_23891.lax_universes);
         phase1 = (uu___1789_23891.phase1);
         failhard = (uu___1789_23891.failhard);
         nosynth = (uu___1789_23891.nosynth);
         uvar_subtyping = (uu___1789_23891.uvar_subtyping);
         tc_term = (uu___1789_23891.tc_term);
         type_of = (uu___1789_23891.type_of);
         universe_of = (uu___1789_23891.universe_of);
         check_type_of = (uu___1789_23891.check_type_of);
         use_bv_sorts = (uu___1789_23891.use_bv_sorts);
         qtbl_name_and_index = (uu___1789_23891.qtbl_name_and_index);
         normalized_eff_names = (uu___1789_23891.normalized_eff_names);
         fv_delta_depths = (uu___1789_23891.fv_delta_depths);
         proof_ns = (uu___1789_23891.proof_ns);
         synth_hook = (uu___1789_23891.synth_hook);
         splice = (uu___1789_23891.splice);
         postprocess = (uu___1789_23891.postprocess);
         is_native_tactic = (uu___1789_23891.is_native_tactic);
         identifier_info = (uu___1789_23891.identifier_info);
         tc_hooks = (uu___1789_23891.tc_hooks);
         dsenv = (uu___1789_23891.dsenv);
         nbe = (uu___1789_23891.nbe);
         strict_args_tab = (uu___1789_23891.strict_args_tab);
         erasable_types_tab = (uu___1789_23891.erasable_types_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1793_23903 = env  in
      {
        solver = (uu___1793_23903.solver);
        range = (uu___1793_23903.range);
        curmodule = (uu___1793_23903.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1793_23903.gamma_sig);
        gamma_cache = (uu___1793_23903.gamma_cache);
        modules = (uu___1793_23903.modules);
        expected_typ = (uu___1793_23903.expected_typ);
        sigtab = (uu___1793_23903.sigtab);
        attrtab = (uu___1793_23903.attrtab);
        is_pattern = (uu___1793_23903.is_pattern);
        instantiate_imp = (uu___1793_23903.instantiate_imp);
        effects = (uu___1793_23903.effects);
        generalize = (uu___1793_23903.generalize);
        letrecs = (uu___1793_23903.letrecs);
        top_level = (uu___1793_23903.top_level);
        check_uvars = (uu___1793_23903.check_uvars);
        use_eq = (uu___1793_23903.use_eq);
        is_iface = (uu___1793_23903.is_iface);
        admit = (uu___1793_23903.admit);
        lax = (uu___1793_23903.lax);
        lax_universes = (uu___1793_23903.lax_universes);
        phase1 = (uu___1793_23903.phase1);
        failhard = (uu___1793_23903.failhard);
        nosynth = (uu___1793_23903.nosynth);
        uvar_subtyping = (uu___1793_23903.uvar_subtyping);
        tc_term = (uu___1793_23903.tc_term);
        type_of = (uu___1793_23903.type_of);
        universe_of = (uu___1793_23903.universe_of);
        check_type_of = (uu___1793_23903.check_type_of);
        use_bv_sorts = (uu___1793_23903.use_bv_sorts);
        qtbl_name_and_index = (uu___1793_23903.qtbl_name_and_index);
        normalized_eff_names = (uu___1793_23903.normalized_eff_names);
        fv_delta_depths = (uu___1793_23903.fv_delta_depths);
        proof_ns = (uu___1793_23903.proof_ns);
        synth_hook = (uu___1793_23903.synth_hook);
        splice = (uu___1793_23903.splice);
        postprocess = (uu___1793_23903.postprocess);
        is_native_tactic = (uu___1793_23903.is_native_tactic);
        identifier_info = (uu___1793_23903.identifier_info);
        tc_hooks = (uu___1793_23903.tc_hooks);
        dsenv = (uu___1793_23903.dsenv);
        nbe = (uu___1793_23903.nbe);
        strict_args_tab = (uu___1793_23903.strict_args_tab);
        erasable_types_tab = (uu___1793_23903.erasable_types_tab)
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
            (let uu___1806_23961 = env  in
             {
               solver = (uu___1806_23961.solver);
               range = (uu___1806_23961.range);
               curmodule = (uu___1806_23961.curmodule);
               gamma = rest;
               gamma_sig = (uu___1806_23961.gamma_sig);
               gamma_cache = (uu___1806_23961.gamma_cache);
               modules = (uu___1806_23961.modules);
               expected_typ = (uu___1806_23961.expected_typ);
               sigtab = (uu___1806_23961.sigtab);
               attrtab = (uu___1806_23961.attrtab);
               is_pattern = (uu___1806_23961.is_pattern);
               instantiate_imp = (uu___1806_23961.instantiate_imp);
               effects = (uu___1806_23961.effects);
               generalize = (uu___1806_23961.generalize);
               letrecs = (uu___1806_23961.letrecs);
               top_level = (uu___1806_23961.top_level);
               check_uvars = (uu___1806_23961.check_uvars);
               use_eq = (uu___1806_23961.use_eq);
               is_iface = (uu___1806_23961.is_iface);
               admit = (uu___1806_23961.admit);
               lax = (uu___1806_23961.lax);
               lax_universes = (uu___1806_23961.lax_universes);
               phase1 = (uu___1806_23961.phase1);
               failhard = (uu___1806_23961.failhard);
               nosynth = (uu___1806_23961.nosynth);
               uvar_subtyping = (uu___1806_23961.uvar_subtyping);
               tc_term = (uu___1806_23961.tc_term);
               type_of = (uu___1806_23961.type_of);
               universe_of = (uu___1806_23961.universe_of);
               check_type_of = (uu___1806_23961.check_type_of);
               use_bv_sorts = (uu___1806_23961.use_bv_sorts);
               qtbl_name_and_index = (uu___1806_23961.qtbl_name_and_index);
               normalized_eff_names = (uu___1806_23961.normalized_eff_names);
               fv_delta_depths = (uu___1806_23961.fv_delta_depths);
               proof_ns = (uu___1806_23961.proof_ns);
               synth_hook = (uu___1806_23961.synth_hook);
               splice = (uu___1806_23961.splice);
               postprocess = (uu___1806_23961.postprocess);
               is_native_tactic = (uu___1806_23961.is_native_tactic);
               identifier_info = (uu___1806_23961.identifier_info);
               tc_hooks = (uu___1806_23961.tc_hooks);
               dsenv = (uu___1806_23961.dsenv);
               nbe = (uu___1806_23961.nbe);
               strict_args_tab = (uu___1806_23961.strict_args_tab);
               erasable_types_tab = (uu___1806_23961.erasable_types_tab)
             }))
    | uu____23962 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23991  ->
             match uu____23991 with | (x,uu____23999) -> push_bv env1 x) env
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
            let uu___1820_24034 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1820_24034.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1820_24034.FStar_Syntax_Syntax.index);
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
        let uu____24107 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24107 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24135 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24135)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1841_24151 = env  in
      {
        solver = (uu___1841_24151.solver);
        range = (uu___1841_24151.range);
        curmodule = (uu___1841_24151.curmodule);
        gamma = (uu___1841_24151.gamma);
        gamma_sig = (uu___1841_24151.gamma_sig);
        gamma_cache = (uu___1841_24151.gamma_cache);
        modules = (uu___1841_24151.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1841_24151.sigtab);
        attrtab = (uu___1841_24151.attrtab);
        is_pattern = (uu___1841_24151.is_pattern);
        instantiate_imp = (uu___1841_24151.instantiate_imp);
        effects = (uu___1841_24151.effects);
        generalize = (uu___1841_24151.generalize);
        letrecs = (uu___1841_24151.letrecs);
        top_level = (uu___1841_24151.top_level);
        check_uvars = (uu___1841_24151.check_uvars);
        use_eq = false;
        is_iface = (uu___1841_24151.is_iface);
        admit = (uu___1841_24151.admit);
        lax = (uu___1841_24151.lax);
        lax_universes = (uu___1841_24151.lax_universes);
        phase1 = (uu___1841_24151.phase1);
        failhard = (uu___1841_24151.failhard);
        nosynth = (uu___1841_24151.nosynth);
        uvar_subtyping = (uu___1841_24151.uvar_subtyping);
        tc_term = (uu___1841_24151.tc_term);
        type_of = (uu___1841_24151.type_of);
        universe_of = (uu___1841_24151.universe_of);
        check_type_of = (uu___1841_24151.check_type_of);
        use_bv_sorts = (uu___1841_24151.use_bv_sorts);
        qtbl_name_and_index = (uu___1841_24151.qtbl_name_and_index);
        normalized_eff_names = (uu___1841_24151.normalized_eff_names);
        fv_delta_depths = (uu___1841_24151.fv_delta_depths);
        proof_ns = (uu___1841_24151.proof_ns);
        synth_hook = (uu___1841_24151.synth_hook);
        splice = (uu___1841_24151.splice);
        postprocess = (uu___1841_24151.postprocess);
        is_native_tactic = (uu___1841_24151.is_native_tactic);
        identifier_info = (uu___1841_24151.identifier_info);
        tc_hooks = (uu___1841_24151.tc_hooks);
        dsenv = (uu___1841_24151.dsenv);
        nbe = (uu___1841_24151.nbe);
        strict_args_tab = (uu___1841_24151.strict_args_tab);
        erasable_types_tab = (uu___1841_24151.erasable_types_tab)
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
    let uu____24182 = expected_typ env_  in
    ((let uu___1848_24188 = env_  in
      {
        solver = (uu___1848_24188.solver);
        range = (uu___1848_24188.range);
        curmodule = (uu___1848_24188.curmodule);
        gamma = (uu___1848_24188.gamma);
        gamma_sig = (uu___1848_24188.gamma_sig);
        gamma_cache = (uu___1848_24188.gamma_cache);
        modules = (uu___1848_24188.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1848_24188.sigtab);
        attrtab = (uu___1848_24188.attrtab);
        is_pattern = (uu___1848_24188.is_pattern);
        instantiate_imp = (uu___1848_24188.instantiate_imp);
        effects = (uu___1848_24188.effects);
        generalize = (uu___1848_24188.generalize);
        letrecs = (uu___1848_24188.letrecs);
        top_level = (uu___1848_24188.top_level);
        check_uvars = (uu___1848_24188.check_uvars);
        use_eq = false;
        is_iface = (uu___1848_24188.is_iface);
        admit = (uu___1848_24188.admit);
        lax = (uu___1848_24188.lax);
        lax_universes = (uu___1848_24188.lax_universes);
        phase1 = (uu___1848_24188.phase1);
        failhard = (uu___1848_24188.failhard);
        nosynth = (uu___1848_24188.nosynth);
        uvar_subtyping = (uu___1848_24188.uvar_subtyping);
        tc_term = (uu___1848_24188.tc_term);
        type_of = (uu___1848_24188.type_of);
        universe_of = (uu___1848_24188.universe_of);
        check_type_of = (uu___1848_24188.check_type_of);
        use_bv_sorts = (uu___1848_24188.use_bv_sorts);
        qtbl_name_and_index = (uu___1848_24188.qtbl_name_and_index);
        normalized_eff_names = (uu___1848_24188.normalized_eff_names);
        fv_delta_depths = (uu___1848_24188.fv_delta_depths);
        proof_ns = (uu___1848_24188.proof_ns);
        synth_hook = (uu___1848_24188.synth_hook);
        splice = (uu___1848_24188.splice);
        postprocess = (uu___1848_24188.postprocess);
        is_native_tactic = (uu___1848_24188.is_native_tactic);
        identifier_info = (uu___1848_24188.identifier_info);
        tc_hooks = (uu___1848_24188.tc_hooks);
        dsenv = (uu___1848_24188.dsenv);
        nbe = (uu___1848_24188.nbe);
        strict_args_tab = (uu___1848_24188.strict_args_tab);
        erasable_types_tab = (uu___1848_24188.erasable_types_tab)
      }), uu____24182)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24200 =
      let uu____24203 = FStar_Ident.id_of_text ""  in [uu____24203]  in
    FStar_Ident.lid_of_ids uu____24200  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24210 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24210
        then
          let uu____24215 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24215 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1856_24243 = env  in
       {
         solver = (uu___1856_24243.solver);
         range = (uu___1856_24243.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1856_24243.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1856_24243.expected_typ);
         sigtab = (uu___1856_24243.sigtab);
         attrtab = (uu___1856_24243.attrtab);
         is_pattern = (uu___1856_24243.is_pattern);
         instantiate_imp = (uu___1856_24243.instantiate_imp);
         effects = (uu___1856_24243.effects);
         generalize = (uu___1856_24243.generalize);
         letrecs = (uu___1856_24243.letrecs);
         top_level = (uu___1856_24243.top_level);
         check_uvars = (uu___1856_24243.check_uvars);
         use_eq = (uu___1856_24243.use_eq);
         is_iface = (uu___1856_24243.is_iface);
         admit = (uu___1856_24243.admit);
         lax = (uu___1856_24243.lax);
         lax_universes = (uu___1856_24243.lax_universes);
         phase1 = (uu___1856_24243.phase1);
         failhard = (uu___1856_24243.failhard);
         nosynth = (uu___1856_24243.nosynth);
         uvar_subtyping = (uu___1856_24243.uvar_subtyping);
         tc_term = (uu___1856_24243.tc_term);
         type_of = (uu___1856_24243.type_of);
         universe_of = (uu___1856_24243.universe_of);
         check_type_of = (uu___1856_24243.check_type_of);
         use_bv_sorts = (uu___1856_24243.use_bv_sorts);
         qtbl_name_and_index = (uu___1856_24243.qtbl_name_and_index);
         normalized_eff_names = (uu___1856_24243.normalized_eff_names);
         fv_delta_depths = (uu___1856_24243.fv_delta_depths);
         proof_ns = (uu___1856_24243.proof_ns);
         synth_hook = (uu___1856_24243.synth_hook);
         splice = (uu___1856_24243.splice);
         postprocess = (uu___1856_24243.postprocess);
         is_native_tactic = (uu___1856_24243.is_native_tactic);
         identifier_info = (uu___1856_24243.identifier_info);
         tc_hooks = (uu___1856_24243.tc_hooks);
         dsenv = (uu___1856_24243.dsenv);
         nbe = (uu___1856_24243.nbe);
         strict_args_tab = (uu___1856_24243.strict_args_tab);
         erasable_types_tab = (uu___1856_24243.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24295)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24299,(uu____24300,t)))::tl1
          ->
          let uu____24321 =
            let uu____24324 = FStar_Syntax_Free.uvars t  in
            ext out uu____24324  in
          aux uu____24321 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24327;
            FStar_Syntax_Syntax.index = uu____24328;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24336 =
            let uu____24339 = FStar_Syntax_Free.uvars t  in
            ext out uu____24339  in
          aux uu____24336 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24397)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24401,(uu____24402,t)))::tl1
          ->
          let uu____24423 =
            let uu____24426 = FStar_Syntax_Free.univs t  in
            ext out uu____24426  in
          aux uu____24423 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24429;
            FStar_Syntax_Syntax.index = uu____24430;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24438 =
            let uu____24441 = FStar_Syntax_Free.univs t  in
            ext out uu____24441  in
          aux uu____24438 tl1
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
          let uu____24503 = FStar_Util.set_add uname out  in
          aux uu____24503 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24506,(uu____24507,t)))::tl1
          ->
          let uu____24528 =
            let uu____24531 = FStar_Syntax_Free.univnames t  in
            ext out uu____24531  in
          aux uu____24528 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24534;
            FStar_Syntax_Syntax.index = uu____24535;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24543 =
            let uu____24546 = FStar_Syntax_Free.univnames t  in
            ext out uu____24546  in
          aux uu____24543 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24567  ->
            match uu___11_24567 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24571 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24584 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24595 =
      let uu____24604 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24604
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24595 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24652 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24665  ->
              match uu___12_24665 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24668 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24668
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24674) ->
                  let uu____24691 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24691))
       in
    FStar_All.pipe_right uu____24652 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24705  ->
    match uu___13_24705 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24711 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24711
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24734  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24789) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24822,uu____24823) -> false  in
      let uu____24837 =
        FStar_List.tryFind
          (fun uu____24859  ->
             match uu____24859 with | (p,uu____24870) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24837 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24889,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24919 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24919
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1999_24941 = e  in
        {
          solver = (uu___1999_24941.solver);
          range = (uu___1999_24941.range);
          curmodule = (uu___1999_24941.curmodule);
          gamma = (uu___1999_24941.gamma);
          gamma_sig = (uu___1999_24941.gamma_sig);
          gamma_cache = (uu___1999_24941.gamma_cache);
          modules = (uu___1999_24941.modules);
          expected_typ = (uu___1999_24941.expected_typ);
          sigtab = (uu___1999_24941.sigtab);
          attrtab = (uu___1999_24941.attrtab);
          is_pattern = (uu___1999_24941.is_pattern);
          instantiate_imp = (uu___1999_24941.instantiate_imp);
          effects = (uu___1999_24941.effects);
          generalize = (uu___1999_24941.generalize);
          letrecs = (uu___1999_24941.letrecs);
          top_level = (uu___1999_24941.top_level);
          check_uvars = (uu___1999_24941.check_uvars);
          use_eq = (uu___1999_24941.use_eq);
          is_iface = (uu___1999_24941.is_iface);
          admit = (uu___1999_24941.admit);
          lax = (uu___1999_24941.lax);
          lax_universes = (uu___1999_24941.lax_universes);
          phase1 = (uu___1999_24941.phase1);
          failhard = (uu___1999_24941.failhard);
          nosynth = (uu___1999_24941.nosynth);
          uvar_subtyping = (uu___1999_24941.uvar_subtyping);
          tc_term = (uu___1999_24941.tc_term);
          type_of = (uu___1999_24941.type_of);
          universe_of = (uu___1999_24941.universe_of);
          check_type_of = (uu___1999_24941.check_type_of);
          use_bv_sorts = (uu___1999_24941.use_bv_sorts);
          qtbl_name_and_index = (uu___1999_24941.qtbl_name_and_index);
          normalized_eff_names = (uu___1999_24941.normalized_eff_names);
          fv_delta_depths = (uu___1999_24941.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1999_24941.synth_hook);
          splice = (uu___1999_24941.splice);
          postprocess = (uu___1999_24941.postprocess);
          is_native_tactic = (uu___1999_24941.is_native_tactic);
          identifier_info = (uu___1999_24941.identifier_info);
          tc_hooks = (uu___1999_24941.tc_hooks);
          dsenv = (uu___1999_24941.dsenv);
          nbe = (uu___1999_24941.nbe);
          strict_args_tab = (uu___1999_24941.strict_args_tab);
          erasable_types_tab = (uu___1999_24941.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2008_24989 = e  in
      {
        solver = (uu___2008_24989.solver);
        range = (uu___2008_24989.range);
        curmodule = (uu___2008_24989.curmodule);
        gamma = (uu___2008_24989.gamma);
        gamma_sig = (uu___2008_24989.gamma_sig);
        gamma_cache = (uu___2008_24989.gamma_cache);
        modules = (uu___2008_24989.modules);
        expected_typ = (uu___2008_24989.expected_typ);
        sigtab = (uu___2008_24989.sigtab);
        attrtab = (uu___2008_24989.attrtab);
        is_pattern = (uu___2008_24989.is_pattern);
        instantiate_imp = (uu___2008_24989.instantiate_imp);
        effects = (uu___2008_24989.effects);
        generalize = (uu___2008_24989.generalize);
        letrecs = (uu___2008_24989.letrecs);
        top_level = (uu___2008_24989.top_level);
        check_uvars = (uu___2008_24989.check_uvars);
        use_eq = (uu___2008_24989.use_eq);
        is_iface = (uu___2008_24989.is_iface);
        admit = (uu___2008_24989.admit);
        lax = (uu___2008_24989.lax);
        lax_universes = (uu___2008_24989.lax_universes);
        phase1 = (uu___2008_24989.phase1);
        failhard = (uu___2008_24989.failhard);
        nosynth = (uu___2008_24989.nosynth);
        uvar_subtyping = (uu___2008_24989.uvar_subtyping);
        tc_term = (uu___2008_24989.tc_term);
        type_of = (uu___2008_24989.type_of);
        universe_of = (uu___2008_24989.universe_of);
        check_type_of = (uu___2008_24989.check_type_of);
        use_bv_sorts = (uu___2008_24989.use_bv_sorts);
        qtbl_name_and_index = (uu___2008_24989.qtbl_name_and_index);
        normalized_eff_names = (uu___2008_24989.normalized_eff_names);
        fv_delta_depths = (uu___2008_24989.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2008_24989.synth_hook);
        splice = (uu___2008_24989.splice);
        postprocess = (uu___2008_24989.postprocess);
        is_native_tactic = (uu___2008_24989.is_native_tactic);
        identifier_info = (uu___2008_24989.identifier_info);
        tc_hooks = (uu___2008_24989.tc_hooks);
        dsenv = (uu___2008_24989.dsenv);
        nbe = (uu___2008_24989.nbe);
        strict_args_tab = (uu___2008_24989.strict_args_tab);
        erasable_types_tab = (uu___2008_24989.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25005 = FStar_Syntax_Free.names t  in
      let uu____25008 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25005 uu____25008
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25031 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25031
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25041 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25041
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25062 =
      match uu____25062 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25082 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25082)
       in
    let uu____25090 =
      let uu____25094 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25094 FStar_List.rev  in
    FStar_All.pipe_right uu____25090 (FStar_String.concat " ")
  
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
                  (let uu____25164 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25164 with
                   | FStar_Pervasives_Native.Some uu____25168 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25171 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____25181;
        univ_ineqs = uu____25182; implicits = uu____25183;_} -> true
    | uu____25195 -> false
  
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
          let uu___2052_25226 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2052_25226.deferred);
            univ_ineqs = (uu___2052_25226.univ_ineqs);
            implicits = (uu___2052_25226.implicits)
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
          let uu____25265 = FStar_Options.defensive ()  in
          if uu____25265
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25271 =
              let uu____25273 =
                let uu____25275 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25275  in
              Prims.op_Negation uu____25273  in
            (if uu____25271
             then
               let uu____25282 =
                 let uu____25288 =
                   let uu____25290 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25292 =
                     let uu____25294 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25294
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25290 uu____25292
                    in
                 (FStar_Errors.Warning_Defensive, uu____25288)  in
               FStar_Errors.log_issue rng uu____25282
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
          let uu____25334 =
            let uu____25336 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25336  in
          if uu____25334
          then ()
          else
            (let uu____25341 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25341 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25367 =
            let uu____25369 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25369  in
          if uu____25367
          then ()
          else
            (let uu____25374 = bound_vars e  in
             def_check_closed_in rng msg uu____25374 t)
  
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
          let uu___2089_25413 = g  in
          let uu____25414 =
            let uu____25415 =
              let uu____25416 =
                let uu____25423 =
                  let uu____25424 =
                    let uu____25441 =
                      let uu____25452 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25452]  in
                    (f, uu____25441)  in
                  FStar_Syntax_Syntax.Tm_app uu____25424  in
                FStar_Syntax_Syntax.mk uu____25423  in
              uu____25416 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25489  -> FStar_TypeChecker_Common.NonTrivial _25489)
              uu____25415
             in
          {
            guard_f = uu____25414;
            deferred = (uu___2089_25413.deferred);
            univ_ineqs = (uu___2089_25413.univ_ineqs);
            implicits = (uu___2089_25413.implicits)
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
          let uu___2096_25507 = g  in
          let uu____25508 =
            let uu____25509 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25509  in
          {
            guard_f = uu____25508;
            deferred = (uu___2096_25507.deferred);
            univ_ineqs = (uu___2096_25507.univ_ineqs);
            implicits = (uu___2096_25507.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2101_25526 = g  in
          let uu____25527 =
            let uu____25528 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25528  in
          {
            guard_f = uu____25527;
            deferred = (uu___2101_25526.deferred);
            univ_ineqs = (uu___2101_25526.univ_ineqs);
            implicits = (uu___2101_25526.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2105_25530 = g  in
          let uu____25531 =
            let uu____25532 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25532  in
          {
            guard_f = uu____25531;
            deferred = (uu___2105_25530.deferred);
            univ_ineqs = (uu___2105_25530.univ_ineqs);
            implicits = (uu___2105_25530.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25539 ->
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
          let uu____25556 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25556
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25563 =
      let uu____25564 = FStar_Syntax_Util.unmeta t  in
      uu____25564.FStar_Syntax_Syntax.n  in
    match uu____25563 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25568 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25611 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25611;
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
                       let uu____25706 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25706
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2160_25713 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2160_25713.deferred);
              univ_ineqs = (uu___2160_25713.univ_ineqs);
              implicits = (uu___2160_25713.implicits)
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
               let uu____25747 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25747
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
            let uu___2175_25774 = g  in
            let uu____25775 =
              let uu____25776 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25776  in
            {
              guard_f = uu____25775;
              deferred = (uu___2175_25774.deferred);
              univ_ineqs = (uu___2175_25774.univ_ineqs);
              implicits = (uu___2175_25774.implicits)
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
              let uu____25834 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25834 with
              | FStar_Pervasives_Native.Some
                  (uu____25859::(tm,uu____25861)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25925 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25943 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25943;
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
                      let uu___2197_25975 = trivial_guard  in
                      {
                        guard_f = (uu___2197_25975.guard_f);
                        deferred = (uu___2197_25975.deferred);
                        univ_ineqs = (uu___2197_25975.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25993  -> ());
    push = (fun uu____25995  -> ());
    pop = (fun uu____25998  -> ());
    snapshot =
      (fun uu____26001  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26020  -> fun uu____26021  -> ());
    encode_sig = (fun uu____26036  -> fun uu____26037  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26043 =
             let uu____26050 = FStar_Options.peek ()  in (e, g, uu____26050)
              in
           [uu____26043]);
    solve = (fun uu____26066  -> fun uu____26067  -> fun uu____26068  -> ());
    finish = (fun uu____26075  -> ());
    refresh = (fun uu____26077  -> ())
  } 