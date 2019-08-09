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
  mlift_t: FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ;
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
let (__proj__Mkmlift__item__mlift_t :
  mlift -> FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_t
  
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_term
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> solver
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> range
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> curmodule
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> gamma
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> gamma_sig
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> gamma_cache
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> modules
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> expected_typ
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> sigtab
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> attrtab
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> is_pattern
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> instantiate_imp
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> effects
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> generalize
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> letrecs
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> top_level
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> check_uvars
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> use_eq
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> is_iface
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> admit1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> lax1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> lax_universes
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> phase1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> failhard
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> nosynth
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> uvar_subtyping
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> tc_term
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> type_of
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> universe_of
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> check_type_of
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> use_bv_sorts
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        qtbl_name_and_index
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        normalized_eff_names
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> fv_delta_depths
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> proof_ns
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> synth_hook
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> splice1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> postprocess
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> is_native_tactic
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> identifier_info
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> tc_hooks
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> dsenv
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> nbe1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> strict_args_tab
  
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
           (fun uu___0_12422  ->
              match uu___0_12422 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12425 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12425  in
                  let uu____12426 =
                    let uu____12427 = FStar_Syntax_Subst.compress y  in
                    uu____12427.FStar_Syntax_Syntax.n  in
                  (match uu____12426 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12431 =
                         let uu___335_12432 = y1  in
                         let uu____12433 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___335_12432.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___335_12432.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12433
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12431
                   | uu____12436 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___341_12450 = env  in
      let uu____12451 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___341_12450.solver);
        range = (uu___341_12450.range);
        curmodule = (uu___341_12450.curmodule);
        gamma = uu____12451;
        gamma_sig = (uu___341_12450.gamma_sig);
        gamma_cache = (uu___341_12450.gamma_cache);
        modules = (uu___341_12450.modules);
        expected_typ = (uu___341_12450.expected_typ);
        sigtab = (uu___341_12450.sigtab);
        attrtab = (uu___341_12450.attrtab);
        is_pattern = (uu___341_12450.is_pattern);
        instantiate_imp = (uu___341_12450.instantiate_imp);
        effects = (uu___341_12450.effects);
        generalize = (uu___341_12450.generalize);
        letrecs = (uu___341_12450.letrecs);
        top_level = (uu___341_12450.top_level);
        check_uvars = (uu___341_12450.check_uvars);
        use_eq = (uu___341_12450.use_eq);
        is_iface = (uu___341_12450.is_iface);
        admit = (uu___341_12450.admit);
        lax = (uu___341_12450.lax);
        lax_universes = (uu___341_12450.lax_universes);
        phase1 = (uu___341_12450.phase1);
        failhard = (uu___341_12450.failhard);
        nosynth = (uu___341_12450.nosynth);
        uvar_subtyping = (uu___341_12450.uvar_subtyping);
        tc_term = (uu___341_12450.tc_term);
        type_of = (uu___341_12450.type_of);
        universe_of = (uu___341_12450.universe_of);
        check_type_of = (uu___341_12450.check_type_of);
        use_bv_sorts = (uu___341_12450.use_bv_sorts);
        qtbl_name_and_index = (uu___341_12450.qtbl_name_and_index);
        normalized_eff_names = (uu___341_12450.normalized_eff_names);
        fv_delta_depths = (uu___341_12450.fv_delta_depths);
        proof_ns = (uu___341_12450.proof_ns);
        synth_hook = (uu___341_12450.synth_hook);
        splice = (uu___341_12450.splice);
        postprocess = (uu___341_12450.postprocess);
        is_native_tactic = (uu___341_12450.is_native_tactic);
        identifier_info = (uu___341_12450.identifier_info);
        tc_hooks = (uu___341_12450.tc_hooks);
        dsenv = (uu___341_12450.dsenv);
        nbe = (uu___341_12450.nbe);
        strict_args_tab = (uu___341_12450.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12459  -> fun uu____12460  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___348_12482 = env  in
      {
        solver = (uu___348_12482.solver);
        range = (uu___348_12482.range);
        curmodule = (uu___348_12482.curmodule);
        gamma = (uu___348_12482.gamma);
        gamma_sig = (uu___348_12482.gamma_sig);
        gamma_cache = (uu___348_12482.gamma_cache);
        modules = (uu___348_12482.modules);
        expected_typ = (uu___348_12482.expected_typ);
        sigtab = (uu___348_12482.sigtab);
        attrtab = (uu___348_12482.attrtab);
        is_pattern = (uu___348_12482.is_pattern);
        instantiate_imp = (uu___348_12482.instantiate_imp);
        effects = (uu___348_12482.effects);
        generalize = (uu___348_12482.generalize);
        letrecs = (uu___348_12482.letrecs);
        top_level = (uu___348_12482.top_level);
        check_uvars = (uu___348_12482.check_uvars);
        use_eq = (uu___348_12482.use_eq);
        is_iface = (uu___348_12482.is_iface);
        admit = (uu___348_12482.admit);
        lax = (uu___348_12482.lax);
        lax_universes = (uu___348_12482.lax_universes);
        phase1 = (uu___348_12482.phase1);
        failhard = (uu___348_12482.failhard);
        nosynth = (uu___348_12482.nosynth);
        uvar_subtyping = (uu___348_12482.uvar_subtyping);
        tc_term = (uu___348_12482.tc_term);
        type_of = (uu___348_12482.type_of);
        universe_of = (uu___348_12482.universe_of);
        check_type_of = (uu___348_12482.check_type_of);
        use_bv_sorts = (uu___348_12482.use_bv_sorts);
        qtbl_name_and_index = (uu___348_12482.qtbl_name_and_index);
        normalized_eff_names = (uu___348_12482.normalized_eff_names);
        fv_delta_depths = (uu___348_12482.fv_delta_depths);
        proof_ns = (uu___348_12482.proof_ns);
        synth_hook = (uu___348_12482.synth_hook);
        splice = (uu___348_12482.splice);
        postprocess = (uu___348_12482.postprocess);
        is_native_tactic = (uu___348_12482.is_native_tactic);
        identifier_info = (uu___348_12482.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___348_12482.dsenv);
        nbe = (uu___348_12482.nbe);
        strict_args_tab = (uu___348_12482.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___352_12494 = e  in
      let uu____12495 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___352_12494.solver);
        range = (uu___352_12494.range);
        curmodule = (uu___352_12494.curmodule);
        gamma = (uu___352_12494.gamma);
        gamma_sig = (uu___352_12494.gamma_sig);
        gamma_cache = (uu___352_12494.gamma_cache);
        modules = (uu___352_12494.modules);
        expected_typ = (uu___352_12494.expected_typ);
        sigtab = (uu___352_12494.sigtab);
        attrtab = (uu___352_12494.attrtab);
        is_pattern = (uu___352_12494.is_pattern);
        instantiate_imp = (uu___352_12494.instantiate_imp);
        effects = (uu___352_12494.effects);
        generalize = (uu___352_12494.generalize);
        letrecs = (uu___352_12494.letrecs);
        top_level = (uu___352_12494.top_level);
        check_uvars = (uu___352_12494.check_uvars);
        use_eq = (uu___352_12494.use_eq);
        is_iface = (uu___352_12494.is_iface);
        admit = (uu___352_12494.admit);
        lax = (uu___352_12494.lax);
        lax_universes = (uu___352_12494.lax_universes);
        phase1 = (uu___352_12494.phase1);
        failhard = (uu___352_12494.failhard);
        nosynth = (uu___352_12494.nosynth);
        uvar_subtyping = (uu___352_12494.uvar_subtyping);
        tc_term = (uu___352_12494.tc_term);
        type_of = (uu___352_12494.type_of);
        universe_of = (uu___352_12494.universe_of);
        check_type_of = (uu___352_12494.check_type_of);
        use_bv_sorts = (uu___352_12494.use_bv_sorts);
        qtbl_name_and_index = (uu___352_12494.qtbl_name_and_index);
        normalized_eff_names = (uu___352_12494.normalized_eff_names);
        fv_delta_depths = (uu___352_12494.fv_delta_depths);
        proof_ns = (uu___352_12494.proof_ns);
        synth_hook = (uu___352_12494.synth_hook);
        splice = (uu___352_12494.splice);
        postprocess = (uu___352_12494.postprocess);
        is_native_tactic = (uu___352_12494.is_native_tactic);
        identifier_info = (uu___352_12494.identifier_info);
        tc_hooks = (uu___352_12494.tc_hooks);
        dsenv = uu____12495;
        nbe = (uu___352_12494.nbe);
        strict_args_tab = (uu___352_12494.strict_args_tab)
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
      | (NoDelta ,uu____12524) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12527,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12529,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12532 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12546 . unit -> 'Auu____12546 FStar_Util.smap =
  fun uu____12553  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12559 . unit -> 'Auu____12559 FStar_Util.smap =
  fun uu____12566  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____12704 = new_gamma_cache ()  in
                  let uu____12707 = new_sigtab ()  in
                  let uu____12710 = new_sigtab ()  in
                  let uu____12717 =
                    let uu____12732 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____12732, FStar_Pervasives_Native.None)  in
                  let uu____12753 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12757 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____12761 = FStar_Options.using_facts_from ()  in
                  let uu____12762 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12765 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____12766 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12704;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12707;
                    attrtab = uu____12710;
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
                    qtbl_name_and_index = uu____12717;
                    normalized_eff_names = uu____12753;
                    fv_delta_depths = uu____12757;
                    proof_ns = uu____12761;
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
                    is_native_tactic = (fun uu____12841  -> false);
                    identifier_info = uu____12762;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12765;
                    nbe = nbe1;
                    strict_args_tab = uu____12766
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
  fun uu____12920  ->
    let uu____12921 = FStar_ST.op_Bang query_indices  in
    match uu____12921 with
    | [] -> failwith "Empty query indices!"
    | uu____12976 ->
        let uu____12986 =
          let uu____12996 =
            let uu____13004 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13004  in
          let uu____13058 = FStar_ST.op_Bang query_indices  in uu____12996 ::
            uu____13058
           in
        FStar_ST.op_Colon_Equals query_indices uu____12986
  
let (pop_query_indices : unit -> unit) =
  fun uu____13154  ->
    let uu____13155 = FStar_ST.op_Bang query_indices  in
    match uu____13155 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13282  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13319  ->
    match uu____13319 with
    | (l,n1) ->
        let uu____13329 = FStar_ST.op_Bang query_indices  in
        (match uu____13329 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13451 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13474  ->
    let uu____13475 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13475
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13543 =
       let uu____13546 = FStar_ST.op_Bang stack  in env :: uu____13546  in
     FStar_ST.op_Colon_Equals stack uu____13543);
    (let uu___420_13595 = env  in
     let uu____13596 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13599 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13602 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13609 =
       let uu____13624 =
         let uu____13628 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13628  in
       let uu____13660 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13624, uu____13660)  in
     let uu____13709 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13712 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13715 =
       let uu____13718 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13718  in
     let uu____13738 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___420_13595.solver);
       range = (uu___420_13595.range);
       curmodule = (uu___420_13595.curmodule);
       gamma = (uu___420_13595.gamma);
       gamma_sig = (uu___420_13595.gamma_sig);
       gamma_cache = uu____13596;
       modules = (uu___420_13595.modules);
       expected_typ = (uu___420_13595.expected_typ);
       sigtab = uu____13599;
       attrtab = uu____13602;
       is_pattern = (uu___420_13595.is_pattern);
       instantiate_imp = (uu___420_13595.instantiate_imp);
       effects = (uu___420_13595.effects);
       generalize = (uu___420_13595.generalize);
       letrecs = (uu___420_13595.letrecs);
       top_level = (uu___420_13595.top_level);
       check_uvars = (uu___420_13595.check_uvars);
       use_eq = (uu___420_13595.use_eq);
       is_iface = (uu___420_13595.is_iface);
       admit = (uu___420_13595.admit);
       lax = (uu___420_13595.lax);
       lax_universes = (uu___420_13595.lax_universes);
       phase1 = (uu___420_13595.phase1);
       failhard = (uu___420_13595.failhard);
       nosynth = (uu___420_13595.nosynth);
       uvar_subtyping = (uu___420_13595.uvar_subtyping);
       tc_term = (uu___420_13595.tc_term);
       type_of = (uu___420_13595.type_of);
       universe_of = (uu___420_13595.universe_of);
       check_type_of = (uu___420_13595.check_type_of);
       use_bv_sorts = (uu___420_13595.use_bv_sorts);
       qtbl_name_and_index = uu____13609;
       normalized_eff_names = uu____13709;
       fv_delta_depths = uu____13712;
       proof_ns = (uu___420_13595.proof_ns);
       synth_hook = (uu___420_13595.synth_hook);
       splice = (uu___420_13595.splice);
       postprocess = (uu___420_13595.postprocess);
       is_native_tactic = (uu___420_13595.is_native_tactic);
       identifier_info = uu____13715;
       tc_hooks = (uu___420_13595.tc_hooks);
       dsenv = (uu___420_13595.dsenv);
       nbe = (uu___420_13595.nbe);
       strict_args_tab = uu____13738
     })
  
let (pop_stack : unit -> env) =
  fun uu____13756  ->
    let uu____13757 = FStar_ST.op_Bang stack  in
    match uu____13757 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13811 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13901  ->
           let uu____13902 = snapshot_stack env  in
           match uu____13902 with
           | (stack_depth,env1) ->
               let uu____13936 = snapshot_query_indices ()  in
               (match uu____13936 with
                | (query_indices_depth,()) ->
                    let uu____13969 = (env1.solver).snapshot msg  in
                    (match uu____13969 with
                     | (solver_depth,()) ->
                         let uu____14026 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14026 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___445_14093 = env1  in
                                 {
                                   solver = (uu___445_14093.solver);
                                   range = (uu___445_14093.range);
                                   curmodule = (uu___445_14093.curmodule);
                                   gamma = (uu___445_14093.gamma);
                                   gamma_sig = (uu___445_14093.gamma_sig);
                                   gamma_cache = (uu___445_14093.gamma_cache);
                                   modules = (uu___445_14093.modules);
                                   expected_typ =
                                     (uu___445_14093.expected_typ);
                                   sigtab = (uu___445_14093.sigtab);
                                   attrtab = (uu___445_14093.attrtab);
                                   is_pattern = (uu___445_14093.is_pattern);
                                   instantiate_imp =
                                     (uu___445_14093.instantiate_imp);
                                   effects = (uu___445_14093.effects);
                                   generalize = (uu___445_14093.generalize);
                                   letrecs = (uu___445_14093.letrecs);
                                   top_level = (uu___445_14093.top_level);
                                   check_uvars = (uu___445_14093.check_uvars);
                                   use_eq = (uu___445_14093.use_eq);
                                   is_iface = (uu___445_14093.is_iface);
                                   admit = (uu___445_14093.admit);
                                   lax = (uu___445_14093.lax);
                                   lax_universes =
                                     (uu___445_14093.lax_universes);
                                   phase1 = (uu___445_14093.phase1);
                                   failhard = (uu___445_14093.failhard);
                                   nosynth = (uu___445_14093.nosynth);
                                   uvar_subtyping =
                                     (uu___445_14093.uvar_subtyping);
                                   tc_term = (uu___445_14093.tc_term);
                                   type_of = (uu___445_14093.type_of);
                                   universe_of = (uu___445_14093.universe_of);
                                   check_type_of =
                                     (uu___445_14093.check_type_of);
                                   use_bv_sorts =
                                     (uu___445_14093.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___445_14093.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___445_14093.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___445_14093.fv_delta_depths);
                                   proof_ns = (uu___445_14093.proof_ns);
                                   synth_hook = (uu___445_14093.synth_hook);
                                   splice = (uu___445_14093.splice);
                                   postprocess = (uu___445_14093.postprocess);
                                   is_native_tactic =
                                     (uu___445_14093.is_native_tactic);
                                   identifier_info =
                                     (uu___445_14093.identifier_info);
                                   tc_hooks = (uu___445_14093.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___445_14093.nbe);
                                   strict_args_tab =
                                     (uu___445_14093.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14127  ->
             let uu____14128 =
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
             match uu____14128 with
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
                             ((let uu____14308 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14308
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14324 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14324
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14356,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14398 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14428  ->
                  match uu____14428 with
                  | (m,uu____14436) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14398 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___490_14451 = env  in
               {
                 solver = (uu___490_14451.solver);
                 range = (uu___490_14451.range);
                 curmodule = (uu___490_14451.curmodule);
                 gamma = (uu___490_14451.gamma);
                 gamma_sig = (uu___490_14451.gamma_sig);
                 gamma_cache = (uu___490_14451.gamma_cache);
                 modules = (uu___490_14451.modules);
                 expected_typ = (uu___490_14451.expected_typ);
                 sigtab = (uu___490_14451.sigtab);
                 attrtab = (uu___490_14451.attrtab);
                 is_pattern = (uu___490_14451.is_pattern);
                 instantiate_imp = (uu___490_14451.instantiate_imp);
                 effects = (uu___490_14451.effects);
                 generalize = (uu___490_14451.generalize);
                 letrecs = (uu___490_14451.letrecs);
                 top_level = (uu___490_14451.top_level);
                 check_uvars = (uu___490_14451.check_uvars);
                 use_eq = (uu___490_14451.use_eq);
                 is_iface = (uu___490_14451.is_iface);
                 admit = (uu___490_14451.admit);
                 lax = (uu___490_14451.lax);
                 lax_universes = (uu___490_14451.lax_universes);
                 phase1 = (uu___490_14451.phase1);
                 failhard = (uu___490_14451.failhard);
                 nosynth = (uu___490_14451.nosynth);
                 uvar_subtyping = (uu___490_14451.uvar_subtyping);
                 tc_term = (uu___490_14451.tc_term);
                 type_of = (uu___490_14451.type_of);
                 universe_of = (uu___490_14451.universe_of);
                 check_type_of = (uu___490_14451.check_type_of);
                 use_bv_sorts = (uu___490_14451.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___490_14451.normalized_eff_names);
                 fv_delta_depths = (uu___490_14451.fv_delta_depths);
                 proof_ns = (uu___490_14451.proof_ns);
                 synth_hook = (uu___490_14451.synth_hook);
                 splice = (uu___490_14451.splice);
                 postprocess = (uu___490_14451.postprocess);
                 is_native_tactic = (uu___490_14451.is_native_tactic);
                 identifier_info = (uu___490_14451.identifier_info);
                 tc_hooks = (uu___490_14451.tc_hooks);
                 dsenv = (uu___490_14451.dsenv);
                 nbe = (uu___490_14451.nbe);
                 strict_args_tab = (uu___490_14451.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14468,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___499_14484 = env  in
               {
                 solver = (uu___499_14484.solver);
                 range = (uu___499_14484.range);
                 curmodule = (uu___499_14484.curmodule);
                 gamma = (uu___499_14484.gamma);
                 gamma_sig = (uu___499_14484.gamma_sig);
                 gamma_cache = (uu___499_14484.gamma_cache);
                 modules = (uu___499_14484.modules);
                 expected_typ = (uu___499_14484.expected_typ);
                 sigtab = (uu___499_14484.sigtab);
                 attrtab = (uu___499_14484.attrtab);
                 is_pattern = (uu___499_14484.is_pattern);
                 instantiate_imp = (uu___499_14484.instantiate_imp);
                 effects = (uu___499_14484.effects);
                 generalize = (uu___499_14484.generalize);
                 letrecs = (uu___499_14484.letrecs);
                 top_level = (uu___499_14484.top_level);
                 check_uvars = (uu___499_14484.check_uvars);
                 use_eq = (uu___499_14484.use_eq);
                 is_iface = (uu___499_14484.is_iface);
                 admit = (uu___499_14484.admit);
                 lax = (uu___499_14484.lax);
                 lax_universes = (uu___499_14484.lax_universes);
                 phase1 = (uu___499_14484.phase1);
                 failhard = (uu___499_14484.failhard);
                 nosynth = (uu___499_14484.nosynth);
                 uvar_subtyping = (uu___499_14484.uvar_subtyping);
                 tc_term = (uu___499_14484.tc_term);
                 type_of = (uu___499_14484.type_of);
                 universe_of = (uu___499_14484.universe_of);
                 check_type_of = (uu___499_14484.check_type_of);
                 use_bv_sorts = (uu___499_14484.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___499_14484.normalized_eff_names);
                 fv_delta_depths = (uu___499_14484.fv_delta_depths);
                 proof_ns = (uu___499_14484.proof_ns);
                 synth_hook = (uu___499_14484.synth_hook);
                 splice = (uu___499_14484.splice);
                 postprocess = (uu___499_14484.postprocess);
                 is_native_tactic = (uu___499_14484.is_native_tactic);
                 identifier_info = (uu___499_14484.identifier_info);
                 tc_hooks = (uu___499_14484.tc_hooks);
                 dsenv = (uu___499_14484.dsenv);
                 nbe = (uu___499_14484.nbe);
                 strict_args_tab = (uu___499_14484.strict_args_tab)
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
        (let uu___506_14527 = e  in
         {
           solver = (uu___506_14527.solver);
           range = r;
           curmodule = (uu___506_14527.curmodule);
           gamma = (uu___506_14527.gamma);
           gamma_sig = (uu___506_14527.gamma_sig);
           gamma_cache = (uu___506_14527.gamma_cache);
           modules = (uu___506_14527.modules);
           expected_typ = (uu___506_14527.expected_typ);
           sigtab = (uu___506_14527.sigtab);
           attrtab = (uu___506_14527.attrtab);
           is_pattern = (uu___506_14527.is_pattern);
           instantiate_imp = (uu___506_14527.instantiate_imp);
           effects = (uu___506_14527.effects);
           generalize = (uu___506_14527.generalize);
           letrecs = (uu___506_14527.letrecs);
           top_level = (uu___506_14527.top_level);
           check_uvars = (uu___506_14527.check_uvars);
           use_eq = (uu___506_14527.use_eq);
           is_iface = (uu___506_14527.is_iface);
           admit = (uu___506_14527.admit);
           lax = (uu___506_14527.lax);
           lax_universes = (uu___506_14527.lax_universes);
           phase1 = (uu___506_14527.phase1);
           failhard = (uu___506_14527.failhard);
           nosynth = (uu___506_14527.nosynth);
           uvar_subtyping = (uu___506_14527.uvar_subtyping);
           tc_term = (uu___506_14527.tc_term);
           type_of = (uu___506_14527.type_of);
           universe_of = (uu___506_14527.universe_of);
           check_type_of = (uu___506_14527.check_type_of);
           use_bv_sorts = (uu___506_14527.use_bv_sorts);
           qtbl_name_and_index = (uu___506_14527.qtbl_name_and_index);
           normalized_eff_names = (uu___506_14527.normalized_eff_names);
           fv_delta_depths = (uu___506_14527.fv_delta_depths);
           proof_ns = (uu___506_14527.proof_ns);
           synth_hook = (uu___506_14527.synth_hook);
           splice = (uu___506_14527.splice);
           postprocess = (uu___506_14527.postprocess);
           is_native_tactic = (uu___506_14527.is_native_tactic);
           identifier_info = (uu___506_14527.identifier_info);
           tc_hooks = (uu___506_14527.tc_hooks);
           dsenv = (uu___506_14527.dsenv);
           nbe = (uu___506_14527.nbe);
           strict_args_tab = (uu___506_14527.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14547 =
        let uu____14548 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14548 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14547
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14603 =
          let uu____14604 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14604 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14603
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14659 =
          let uu____14660 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14660 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14659
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14715 =
        let uu____14716 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14716 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14715
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___523_14780 = env  in
      {
        solver = (uu___523_14780.solver);
        range = (uu___523_14780.range);
        curmodule = lid;
        gamma = (uu___523_14780.gamma);
        gamma_sig = (uu___523_14780.gamma_sig);
        gamma_cache = (uu___523_14780.gamma_cache);
        modules = (uu___523_14780.modules);
        expected_typ = (uu___523_14780.expected_typ);
        sigtab = (uu___523_14780.sigtab);
        attrtab = (uu___523_14780.attrtab);
        is_pattern = (uu___523_14780.is_pattern);
        instantiate_imp = (uu___523_14780.instantiate_imp);
        effects = (uu___523_14780.effects);
        generalize = (uu___523_14780.generalize);
        letrecs = (uu___523_14780.letrecs);
        top_level = (uu___523_14780.top_level);
        check_uvars = (uu___523_14780.check_uvars);
        use_eq = (uu___523_14780.use_eq);
        is_iface = (uu___523_14780.is_iface);
        admit = (uu___523_14780.admit);
        lax = (uu___523_14780.lax);
        lax_universes = (uu___523_14780.lax_universes);
        phase1 = (uu___523_14780.phase1);
        failhard = (uu___523_14780.failhard);
        nosynth = (uu___523_14780.nosynth);
        uvar_subtyping = (uu___523_14780.uvar_subtyping);
        tc_term = (uu___523_14780.tc_term);
        type_of = (uu___523_14780.type_of);
        universe_of = (uu___523_14780.universe_of);
        check_type_of = (uu___523_14780.check_type_of);
        use_bv_sorts = (uu___523_14780.use_bv_sorts);
        qtbl_name_and_index = (uu___523_14780.qtbl_name_and_index);
        normalized_eff_names = (uu___523_14780.normalized_eff_names);
        fv_delta_depths = (uu___523_14780.fv_delta_depths);
        proof_ns = (uu___523_14780.proof_ns);
        synth_hook = (uu___523_14780.synth_hook);
        splice = (uu___523_14780.splice);
        postprocess = (uu___523_14780.postprocess);
        is_native_tactic = (uu___523_14780.is_native_tactic);
        identifier_info = (uu___523_14780.identifier_info);
        tc_hooks = (uu___523_14780.tc_hooks);
        dsenv = (uu___523_14780.dsenv);
        nbe = (uu___523_14780.nbe);
        strict_args_tab = (uu___523_14780.strict_args_tab)
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
      let uu____14811 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14811
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14824 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14824)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14839 =
      let uu____14841 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14841  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14839)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14850  ->
    let uu____14851 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14851
  
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
      | ((formals,t),uu____14951) ->
          let vs = mk_univ_subst formals us  in
          let uu____14975 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14975)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14992  ->
    match uu___1_14992 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15018  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15038 = inst_tscheme t  in
      match uu____15038 with
      | (us,t1) ->
          let uu____15049 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15049)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____15070  ->
          match uu____15070 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____15092 =
                         let uu____15094 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____15098 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____15102 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____15104 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____15094 uu____15098 uu____15102 uu____15104
                          in
                       failwith uu____15092)
                    else ();
                    (let uu____15109 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____15109))
               | uu____15118 ->
                   let uu____15119 =
                     let uu____15121 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____15121
                      in
                   failwith uu____15119)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15133 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15144 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15155 -> false
  
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
             | ([],uu____15203) -> Maybe
             | (uu____15210,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15230 -> No  in
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
          let uu____15324 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15324 with
          | FStar_Pervasives_Native.None  ->
              let uu____15347 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15391  ->
                     match uu___2_15391 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15430 = FStar_Ident.lid_equals lid l  in
                         if uu____15430
                         then
                           let uu____15453 =
                             let uu____15472 =
                               let uu____15487 = inst_tscheme t  in
                               FStar_Util.Inl uu____15487  in
                             let uu____15502 = FStar_Ident.range_of_lid l  in
                             (uu____15472, uu____15502)  in
                           FStar_Pervasives_Native.Some uu____15453
                         else FStar_Pervasives_Native.None
                     | uu____15555 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15347
                (fun uu____15593  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15602  ->
                        match uu___3_15602 with
                        | (uu____15605,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15607);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15608;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15609;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15610;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15611;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15631 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15631
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
                                  uu____15683 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15690 -> cache t  in
                            let uu____15691 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15691 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15697 =
                                   let uu____15698 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15698)
                                    in
                                 maybe_cache uu____15697)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15769 = find_in_sigtab env lid  in
         match uu____15769 with
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
      let uu____15850 = lookup_qname env lid  in
      match uu____15850 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15871,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15985 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15985 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16030 =
          let uu____16033 = lookup_attr env1 attr  in se1 :: uu____16033  in
        FStar_Util.smap_add (attrtab env1) attr uu____16030  in
      FStar_List.iter
        (fun attr  ->
           let uu____16043 =
             let uu____16044 = FStar_Syntax_Subst.compress attr  in
             uu____16044.FStar_Syntax_Syntax.n  in
           match uu____16043 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16048 =
                 let uu____16050 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16050.FStar_Ident.str  in
               add_one1 env se uu____16048
           | uu____16051 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16074) ->
          add_sigelts env ses
      | uu____16083 ->
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
            | uu____16098 -> ()))

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
        (fun uu___4_16130  ->
           match uu___4_16130 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16148 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16210,lb::[]),uu____16212) ->
            let uu____16221 =
              let uu____16230 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16239 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16230, uu____16239)  in
            FStar_Pervasives_Native.Some uu____16221
        | FStar_Syntax_Syntax.Sig_let ((uu____16252,lbs),uu____16254) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16286 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16299 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16299
                     then
                       let uu____16312 =
                         let uu____16321 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16330 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16321, uu____16330)  in
                       FStar_Pervasives_Native.Some uu____16312
                     else FStar_Pervasives_Native.None)
        | uu____16353 -> FStar_Pervasives_Native.None
  
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
          let uu____16422 =
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
                  let uu____16458 =
                    let uu____16460 =
                      let uu____16462 =
                        let uu____16464 =
                          let uu____16466 =
                            FStar_Util.string_of_int
                              ((FStar_List.length
                                  ne.FStar_Syntax_Syntax.univs)
                                 +
                                 (FStar_List.length
                                    (FStar_Pervasives_Native.fst
                                       ne.FStar_Syntax_Syntax.signature)))
                             in
                          let uu____16472 =
                            let uu____16474 =
                              FStar_Util.string_of_int (FStar_List.length us)
                               in
                            Prims.op_Hat ", got " uu____16474  in
                          Prims.op_Hat uu____16466 uu____16472  in
                        Prims.op_Hat ", expected " uu____16464  in
                      Prims.op_Hat
                        (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                        uu____16462
                       in
                    Prims.op_Hat
                      "effect_signature: insufficient number of universes for the signature of "
                      uu____16460
                     in
                  failwith uu____16458
                else
                  (let uu____16489 =
                     FStar_List.splitAt
                       (FStar_List.length ne.FStar_Syntax_Syntax.univs) us
                      in
                   match uu____16489 with
                   | (ne_us,sig_us) ->
                       ((FStar_Pervasives_Native.Some ne_us),
                         (FStar_Pervasives_Native.Some sig_us)))
             in
          (match uu____16422 with
           | (ne_us,sig_us) ->
               let uu____16540 =
                 inst_tscheme1 sig_us ne.FStar_Syntax_Syntax.signature  in
               (match uu____16540 with
                | (sig_us1,signature_t) ->
                    let uu____16557 =
                      let uu____16562 =
                        let uu____16563 =
                          let uu____16566 =
                            FStar_Syntax_Syntax.mk_Total signature_t  in
                          FStar_Syntax_Util.arrow
                            ne.FStar_Syntax_Syntax.binders uu____16566
                           in
                        ((ne.FStar_Syntax_Syntax.univs), uu____16563)  in
                      inst_tscheme1 ne_us uu____16562  in
                    (match uu____16557 with
                     | (ne_us1,signature_t1) ->
                         FStar_Pervasives_Native.Some
                           (((FStar_List.append ne_us1 sig_us1),
                              signature_t1), (se.FStar_Syntax_Syntax.sigrng)))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16600,uu____16601) ->
          let uu____16606 =
            let uu____16615 =
              let uu____16620 =
                let uu____16621 =
                  let uu____16624 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16624  in
                (us, uu____16621)  in
              inst_tscheme1 us_opt uu____16620  in
            (uu____16615, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16606
      | uu____16643 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16732 =
          match uu____16732 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16828,uvs,t,uu____16831,uu____16832,uu____16833);
                      FStar_Syntax_Syntax.sigrng = uu____16834;
                      FStar_Syntax_Syntax.sigquals = uu____16835;
                      FStar_Syntax_Syntax.sigmeta = uu____16836;
                      FStar_Syntax_Syntax.sigattrs = uu____16837;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16860 =
                     let uu____16869 = inst_tscheme1 (uvs, t)  in
                     (uu____16869, rng)  in
                   FStar_Pervasives_Native.Some uu____16860
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16893;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16895;
                      FStar_Syntax_Syntax.sigattrs = uu____16896;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16913 =
                     let uu____16915 = in_cur_mod env l  in uu____16915 = Yes
                      in
                   if uu____16913
                   then
                     let uu____16927 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16927
                      then
                        let uu____16943 =
                          let uu____16952 = inst_tscheme1 (uvs, t)  in
                          (uu____16952, rng)  in
                        FStar_Pervasives_Native.Some uu____16943
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16985 =
                        let uu____16994 = inst_tscheme1 (uvs, t)  in
                        (uu____16994, rng)  in
                      FStar_Pervasives_Native.Some uu____16985)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17019,uu____17020);
                      FStar_Syntax_Syntax.sigrng = uu____17021;
                      FStar_Syntax_Syntax.sigquals = uu____17022;
                      FStar_Syntax_Syntax.sigmeta = uu____17023;
                      FStar_Syntax_Syntax.sigattrs = uu____17024;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17065 =
                          let uu____17074 = inst_tscheme1 (uvs, k)  in
                          (uu____17074, rng)  in
                        FStar_Pervasives_Native.Some uu____17065
                    | uu____17095 ->
                        let uu____17096 =
                          let uu____17105 =
                            let uu____17110 =
                              let uu____17111 =
                                let uu____17114 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17114
                                 in
                              (uvs, uu____17111)  in
                            inst_tscheme1 uu____17110  in
                          (uu____17105, rng)  in
                        FStar_Pervasives_Native.Some uu____17096)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17137,uu____17138);
                      FStar_Syntax_Syntax.sigrng = uu____17139;
                      FStar_Syntax_Syntax.sigquals = uu____17140;
                      FStar_Syntax_Syntax.sigmeta = uu____17141;
                      FStar_Syntax_Syntax.sigattrs = uu____17142;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17184 =
                          let uu____17193 = inst_tscheme_with (uvs, k) us  in
                          (uu____17193, rng)  in
                        FStar_Pervasives_Native.Some uu____17184
                    | uu____17214 ->
                        let uu____17215 =
                          let uu____17224 =
                            let uu____17229 =
                              let uu____17230 =
                                let uu____17233 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17233
                                 in
                              (uvs, uu____17230)  in
                            inst_tscheme_with uu____17229 us  in
                          (uu____17224, rng)  in
                        FStar_Pervasives_Native.Some uu____17215)
               | FStar_Util.Inr se ->
                   let uu____17269 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17290;
                          FStar_Syntax_Syntax.sigrng = uu____17291;
                          FStar_Syntax_Syntax.sigquals = uu____17292;
                          FStar_Syntax_Syntax.sigmeta = uu____17293;
                          FStar_Syntax_Syntax.sigattrs = uu____17294;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17309 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____17269
                     (FStar_Util.map_option
                        (fun uu____17357  ->
                           match uu____17357 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17388 =
          let uu____17399 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17399 mapper  in
        match uu____17388 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17473 =
              let uu____17484 =
                let uu____17491 =
                  let uu___867_17494 = t  in
                  let uu____17495 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___867_17494.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17495;
                    FStar_Syntax_Syntax.vars =
                      (uu___867_17494.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17491)  in
              (uu____17484, r)  in
            FStar_Pervasives_Native.Some uu____17473
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17544 = lookup_qname env l  in
      match uu____17544 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17565 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17619 = try_lookup_bv env bv  in
      match uu____17619 with
      | FStar_Pervasives_Native.None  ->
          let uu____17634 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17634 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17650 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17651 =
            let uu____17652 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17652  in
          (uu____17650, uu____17651)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17674 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17674 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17740 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17740  in
          let uu____17741 =
            let uu____17750 =
              let uu____17755 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17755)  in
            (uu____17750, r1)  in
          FStar_Pervasives_Native.Some uu____17741
  
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
        let uu____17790 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17790 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17823,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17848 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17848  in
            let uu____17849 =
              let uu____17854 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17854, r1)  in
            FStar_Pervasives_Native.Some uu____17849
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17878 = try_lookup_lid env l  in
      match uu____17878 with
      | FStar_Pervasives_Native.None  ->
          let uu____17905 = name_not_found l  in
          let uu____17911 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17905 uu____17911
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17954  ->
              match uu___5_17954 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17958 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17979 = lookup_qname env lid  in
      match uu____17979 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17988,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17991;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17993;
              FStar_Syntax_Syntax.sigattrs = uu____17994;_},FStar_Pervasives_Native.None
            ),uu____17995)
          ->
          let uu____18044 =
            let uu____18051 =
              let uu____18052 =
                let uu____18055 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18055 t  in
              (uvs, uu____18052)  in
            (uu____18051, q)  in
          FStar_Pervasives_Native.Some uu____18044
      | uu____18068 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18090 = lookup_qname env lid  in
      match uu____18090 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18095,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18098;
              FStar_Syntax_Syntax.sigquals = uu____18099;
              FStar_Syntax_Syntax.sigmeta = uu____18100;
              FStar_Syntax_Syntax.sigattrs = uu____18101;_},FStar_Pervasives_Native.None
            ),uu____18102)
          ->
          let uu____18151 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18151 (uvs, t)
      | uu____18156 ->
          let uu____18157 = name_not_found lid  in
          let uu____18163 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18157 uu____18163
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18183 = lookup_qname env lid  in
      match uu____18183 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18188,uvs,t,uu____18191,uu____18192,uu____18193);
              FStar_Syntax_Syntax.sigrng = uu____18194;
              FStar_Syntax_Syntax.sigquals = uu____18195;
              FStar_Syntax_Syntax.sigmeta = uu____18196;
              FStar_Syntax_Syntax.sigattrs = uu____18197;_},FStar_Pervasives_Native.None
            ),uu____18198)
          ->
          let uu____18253 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18253 (uvs, t)
      | uu____18258 ->
          let uu____18259 = name_not_found lid  in
          let uu____18265 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18259 uu____18265
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18288 = lookup_qname env lid  in
      match uu____18288 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18296,uu____18297,uu____18298,uu____18299,uu____18300,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18302;
              FStar_Syntax_Syntax.sigquals = uu____18303;
              FStar_Syntax_Syntax.sigmeta = uu____18304;
              FStar_Syntax_Syntax.sigattrs = uu____18305;_},uu____18306),uu____18307)
          -> (true, dcs)
      | uu____18370 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18386 = lookup_qname env lid  in
      match uu____18386 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18387,uu____18388,uu____18389,l,uu____18391,uu____18392);
              FStar_Syntax_Syntax.sigrng = uu____18393;
              FStar_Syntax_Syntax.sigquals = uu____18394;
              FStar_Syntax_Syntax.sigmeta = uu____18395;
              FStar_Syntax_Syntax.sigattrs = uu____18396;_},uu____18397),uu____18398)
          -> l
      | uu____18455 ->
          let uu____18456 =
            let uu____18458 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18458  in
          failwith uu____18456
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18528)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18585) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18609 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18609
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18644 -> FStar_Pervasives_Native.None)
          | uu____18653 -> FStar_Pervasives_Native.None
  
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
        let uu____18715 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18715
  
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
        let uu____18748 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18748
  
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
             (FStar_Util.Inl uu____18800,uu____18801) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18850),uu____18851) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18900 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18918 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18928 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18945 ->
                  let uu____18952 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18952
              | FStar_Syntax_Syntax.Sig_let ((uu____18953,lbs),uu____18955)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18971 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18971
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18978 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18986 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18987 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18994 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18995 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18996 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18997 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19010 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19028 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19028
           (fun d_opt  ->
              let uu____19041 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19041
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19051 =
                   let uu____19054 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19054  in
                 match uu____19051 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19055 =
                       let uu____19057 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19057
                        in
                     failwith uu____19055
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19062 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19062
                       then
                         let uu____19065 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19067 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19069 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19065 uu____19067 uu____19069
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
        (FStar_Util.Inr (se,uu____19094),uu____19095) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19144 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19166),uu____19167) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19216 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19238 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19238
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19261 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19261 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19285 =
                      let uu____19286 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19286.FStar_Syntax_Syntax.n  in
                    match uu____19285 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19291 -> false))
  
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
        let uu____19328 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19328.FStar_Ident.str  in
      let uu____19329 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19329 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19357 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19357  in
          let res =
            match attrs with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some attrs1 ->
                FStar_Util.find_map attrs1
                  (fun x  ->
                     let uu____19385 =
                       FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                         FStar_Parser_Const.strict_on_arguments_attr
                        in
                     FStar_Pervasives_Native.fst uu____19385)
             in
          (FStar_Util.smap_add env.strict_args_tab s res; res)
      | FStar_Pervasives_Native.Some l -> l
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____19435 = lookup_qname env ftv  in
      match uu____19435 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19439) ->
          let uu____19484 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____19484 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19505,t),r) ->
               let uu____19520 =
                 let uu____19521 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19521 t  in
               FStar_Pervasives_Native.Some uu____19520)
      | uu____19522 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19534 = try_lookup_effect_lid env ftv  in
      match uu____19534 with
      | FStar_Pervasives_Native.None  ->
          let uu____19537 = name_not_found ftv  in
          let uu____19543 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19537 uu____19543
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
        let uu____19567 = lookup_qname env lid0  in
        match uu____19567 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19578);
                FStar_Syntax_Syntax.sigrng = uu____19579;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19581;
                FStar_Syntax_Syntax.sigattrs = uu____19582;_},FStar_Pervasives_Native.None
              ),uu____19583)
            ->
            let lid1 =
              let uu____19637 =
                let uu____19638 = FStar_Ident.range_of_lid lid  in
                let uu____19639 =
                  let uu____19640 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19640  in
                FStar_Range.set_use_range uu____19638 uu____19639  in
              FStar_Ident.set_lid_range lid uu____19637  in
            let uu____19641 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19647  ->
                      match uu___6_19647 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19650 -> false))
               in
            if uu____19641
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19669 =
                      let uu____19671 =
                        let uu____19673 = get_range env  in
                        FStar_Range.string_of_range uu____19673  in
                      let uu____19674 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19676 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19671 uu____19674 uu____19676
                       in
                    failwith uu____19669)
                  in
               match (binders, univs1) with
               | ([],uu____19697) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19723,uu____19724::uu____19725::uu____19726) ->
                   let uu____19747 =
                     let uu____19749 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19751 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19749 uu____19751
                      in
                   failwith uu____19747
               | uu____19762 ->
                   let uu____19777 =
                     let uu____19782 =
                       let uu____19783 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19783)  in
                     inst_tscheme_with uu____19782 insts  in
                   (match uu____19777 with
                    | (uu____19796,t) ->
                        let t1 =
                          let uu____19799 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19799 t  in
                        let uu____19800 =
                          let uu____19801 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19801.FStar_Syntax_Syntax.n  in
                        (match uu____19800 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19836 -> failwith "Impossible")))
        | uu____19844 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19868 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19868 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19881,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19888 = find1 l2  in
            (match uu____19888 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19895 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19895 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19899 = find1 l  in
            (match uu____19899 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19904 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19904
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19919 = lookup_qname env l1  in
      match uu____19919 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19922;
              FStar_Syntax_Syntax.sigrng = uu____19923;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19925;
              FStar_Syntax_Syntax.sigattrs = uu____19926;_},uu____19927),uu____19928)
          -> q
      | uu____19979 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20003 =
          let uu____20004 =
            let uu____20006 = FStar_Util.string_of_int i  in
            let uu____20008 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20006 uu____20008
             in
          failwith uu____20004  in
        let uu____20011 = lookup_datacon env lid  in
        match uu____20011 with
        | (uu____20016,t) ->
            let uu____20018 =
              let uu____20019 = FStar_Syntax_Subst.compress t  in
              uu____20019.FStar_Syntax_Syntax.n  in
            (match uu____20018 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20023) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20067 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20067
                      FStar_Pervasives_Native.fst)
             | uu____20078 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20092 = lookup_qname env l  in
      match uu____20092 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20094,uu____20095,uu____20096);
              FStar_Syntax_Syntax.sigrng = uu____20097;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20099;
              FStar_Syntax_Syntax.sigattrs = uu____20100;_},uu____20101),uu____20102)
          ->
          FStar_Util.for_some
            (fun uu___7_20155  ->
               match uu___7_20155 with
               | FStar_Syntax_Syntax.Projector uu____20157 -> true
               | uu____20163 -> false) quals
      | uu____20165 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20179 = lookup_qname env lid  in
      match uu____20179 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20181,uu____20182,uu____20183,uu____20184,uu____20185,uu____20186);
              FStar_Syntax_Syntax.sigrng = uu____20187;
              FStar_Syntax_Syntax.sigquals = uu____20188;
              FStar_Syntax_Syntax.sigmeta = uu____20189;
              FStar_Syntax_Syntax.sigattrs = uu____20190;_},uu____20191),uu____20192)
          -> true
      | uu____20250 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20264 = lookup_qname env lid  in
      match uu____20264 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20266,uu____20267,uu____20268,uu____20269,uu____20270,uu____20271);
              FStar_Syntax_Syntax.sigrng = uu____20272;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20274;
              FStar_Syntax_Syntax.sigattrs = uu____20275;_},uu____20276),uu____20277)
          ->
          FStar_Util.for_some
            (fun uu___8_20338  ->
               match uu___8_20338 with
               | FStar_Syntax_Syntax.RecordType uu____20340 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20350 -> true
               | uu____20360 -> false) quals
      | uu____20362 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20372,uu____20373);
            FStar_Syntax_Syntax.sigrng = uu____20374;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20376;
            FStar_Syntax_Syntax.sigattrs = uu____20377;_},uu____20378),uu____20379)
        ->
        FStar_Util.for_some
          (fun uu___9_20436  ->
             match uu___9_20436 with
             | FStar_Syntax_Syntax.Action uu____20438 -> true
             | uu____20440 -> false) quals
    | uu____20442 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20456 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20456
  
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
      let uu____20473 =
        let uu____20474 = FStar_Syntax_Util.un_uinst head1  in
        uu____20474.FStar_Syntax_Syntax.n  in
      match uu____20473 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20480 ->
               true
           | uu____20483 -> false)
      | uu____20485 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20499 = lookup_qname env l  in
      match uu____20499 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20502),uu____20503) ->
          FStar_Util.for_some
            (fun uu___10_20551  ->
               match uu___10_20551 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20554 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20556 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20632 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20650) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20668 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20676 ->
                 FStar_Pervasives_Native.Some true
             | uu____20695 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20698 =
        let uu____20702 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20702 mapper  in
      match uu____20698 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20762 = lookup_qname env lid  in
      match uu____20762 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20766,uu____20767,tps,uu____20769,uu____20770,uu____20771);
              FStar_Syntax_Syntax.sigrng = uu____20772;
              FStar_Syntax_Syntax.sigquals = uu____20773;
              FStar_Syntax_Syntax.sigmeta = uu____20774;
              FStar_Syntax_Syntax.sigattrs = uu____20775;_},uu____20776),uu____20777)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20843 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20889  ->
              match uu____20889 with
              | (d,uu____20898) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20914 = effect_decl_opt env l  in
      match uu____20914 with
      | FStar_Pervasives_Native.None  ->
          let uu____20929 = name_not_found l  in
          let uu____20935 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20929 uu____20935
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_t = FStar_Pervasives_Native.None;
    mlift_wp = (fun uu____20955  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20974  ->
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
        let uu____21006 = FStar_Ident.lid_equals l1 l2  in
        if uu____21006
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21017 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21017
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21028 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21081  ->
                        match uu____21081 with
                        | (m1,m2,uu____21095,uu____21096,uu____21097) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21028 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21114 =
                    let uu____21120 =
                      let uu____21122 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21124 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21122
                        uu____21124
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21120)
                     in
                  FStar_Errors.raise_error uu____21114 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21134,uu____21135,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21169 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21169
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
  'Auu____21189 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21189) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21218 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21244  ->
                match uu____21244 with
                | (d,uu____21251) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21218 with
      | FStar_Pervasives_Native.None  ->
          let uu____21262 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21262
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21277 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21277 with
           | (uu____21288,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21306)::(wp,uu____21308)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21364 -> failwith "Impossible"))
  
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
            let uu___1524_21414 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1524_21414.order);
              joins = (uu___1524_21414.joins)
            }  in
          let uu___1527_21423 = env  in
          {
            solver = (uu___1527_21423.solver);
            range = (uu___1527_21423.range);
            curmodule = (uu___1527_21423.curmodule);
            gamma = (uu___1527_21423.gamma);
            gamma_sig = (uu___1527_21423.gamma_sig);
            gamma_cache = (uu___1527_21423.gamma_cache);
            modules = (uu___1527_21423.modules);
            expected_typ = (uu___1527_21423.expected_typ);
            sigtab = (uu___1527_21423.sigtab);
            attrtab = (uu___1527_21423.attrtab);
            is_pattern = (uu___1527_21423.is_pattern);
            instantiate_imp = (uu___1527_21423.instantiate_imp);
            effects;
            generalize = (uu___1527_21423.generalize);
            letrecs = (uu___1527_21423.letrecs);
            top_level = (uu___1527_21423.top_level);
            check_uvars = (uu___1527_21423.check_uvars);
            use_eq = (uu___1527_21423.use_eq);
            is_iface = (uu___1527_21423.is_iface);
            admit = (uu___1527_21423.admit);
            lax = (uu___1527_21423.lax);
            lax_universes = (uu___1527_21423.lax_universes);
            phase1 = (uu___1527_21423.phase1);
            failhard = (uu___1527_21423.failhard);
            nosynth = (uu___1527_21423.nosynth);
            uvar_subtyping = (uu___1527_21423.uvar_subtyping);
            tc_term = (uu___1527_21423.tc_term);
            type_of = (uu___1527_21423.type_of);
            universe_of = (uu___1527_21423.universe_of);
            check_type_of = (uu___1527_21423.check_type_of);
            use_bv_sorts = (uu___1527_21423.use_bv_sorts);
            qtbl_name_and_index = (uu___1527_21423.qtbl_name_and_index);
            normalized_eff_names = (uu___1527_21423.normalized_eff_names);
            fv_delta_depths = (uu___1527_21423.fv_delta_depths);
            proof_ns = (uu___1527_21423.proof_ns);
            synth_hook = (uu___1527_21423.synth_hook);
            splice = (uu___1527_21423.splice);
            postprocess = (uu___1527_21423.postprocess);
            is_native_tactic = (uu___1527_21423.is_native_tactic);
            identifier_info = (uu___1527_21423.identifier_info);
            tc_hooks = (uu___1527_21423.tc_hooks);
            dsenv = (uu___1527_21423.dsenv);
            nbe = (uu___1527_21423.nbe);
            strict_args_tab = (uu___1527_21423.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let src_ed = get_effect_decl env sub1.FStar_Syntax_Syntax.source
             in
          let dst_ed = get_effect_decl env sub1.FStar_Syntax_Syntax.target
             in
          if
            src_ed.FStar_Syntax_Syntax.is_layered ||
              dst_ed.FStar_Syntax_Syntax.is_layered
          then
            let edge =
              {
                msource = (sub1.FStar_Syntax_Syntax.source);
                mtarget = (sub1.FStar_Syntax_Syntax.target);
                mlift =
                  {
                    mlift_t = (sub1.FStar_Syntax_Syntax.lift_wp);
                    mlift_wp =
                      (fun uu____21432  ->
                         fun uu____21433  ->
                           fun uu____21434  -> FStar_Syntax_Syntax.tun);
                    mlift_term = FStar_Pervasives_Native.None
                  }
              }  in
            let uu___1538_21447 = env  in
            {
              solver = (uu___1538_21447.solver);
              range = (uu___1538_21447.range);
              curmodule = (uu___1538_21447.curmodule);
              gamma = (uu___1538_21447.gamma);
              gamma_sig = (uu___1538_21447.gamma_sig);
              gamma_cache = (uu___1538_21447.gamma_cache);
              modules = (uu___1538_21447.modules);
              expected_typ = (uu___1538_21447.expected_typ);
              sigtab = (uu___1538_21447.sigtab);
              attrtab = (uu___1538_21447.attrtab);
              is_pattern = (uu___1538_21447.is_pattern);
              instantiate_imp = (uu___1538_21447.instantiate_imp);
              effects =
                (let uu___1540_21449 = env.effects  in
                 {
                   decls = (uu___1540_21449.decls);
                   order = (edge :: ((env.effects).order));
                   joins = (uu___1540_21449.joins)
                 });
              generalize = (uu___1538_21447.generalize);
              letrecs = (uu___1538_21447.letrecs);
              top_level = (uu___1538_21447.top_level);
              check_uvars = (uu___1538_21447.check_uvars);
              use_eq = (uu___1538_21447.use_eq);
              is_iface = (uu___1538_21447.is_iface);
              admit = (uu___1538_21447.admit);
              lax = (uu___1538_21447.lax);
              lax_universes = (uu___1538_21447.lax_universes);
              phase1 = (uu___1538_21447.phase1);
              failhard = (uu___1538_21447.failhard);
              nosynth = (uu___1538_21447.nosynth);
              uvar_subtyping = (uu___1538_21447.uvar_subtyping);
              tc_term = (uu___1538_21447.tc_term);
              type_of = (uu___1538_21447.type_of);
              universe_of = (uu___1538_21447.universe_of);
              check_type_of = (uu___1538_21447.check_type_of);
              use_bv_sorts = (uu___1538_21447.use_bv_sorts);
              qtbl_name_and_index = (uu___1538_21447.qtbl_name_and_index);
              normalized_eff_names = (uu___1538_21447.normalized_eff_names);
              fv_delta_depths = (uu___1538_21447.fv_delta_depths);
              proof_ns = (uu___1538_21447.proof_ns);
              synth_hook = (uu___1538_21447.synth_hook);
              splice = (uu___1538_21447.splice);
              postprocess = (uu___1538_21447.postprocess);
              is_native_tactic = (uu___1538_21447.is_native_tactic);
              identifier_info = (uu___1538_21447.identifier_info);
              tc_hooks = (uu___1538_21447.tc_hooks);
              dsenv = (uu___1538_21447.dsenv);
              nbe = (uu___1538_21447.nbe);
              strict_args_tab = (uu___1538_21447.strict_args_tab)
            }
          else
            (let compose_edges e1 e2 =
               let composed_lift =
                 let mlift_wp u r wp1 =
                   let uu____21480 = (e1.mlift).mlift_wp u r wp1  in
                   (e2.mlift).mlift_wp u r uu____21480  in
                 let mlift_term =
                   match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term))
                   with
                   | (FStar_Pervasives_Native.Some
                      l1,FStar_Pervasives_Native.Some l2) ->
                       FStar_Pervasives_Native.Some
                         ((fun u  ->
                             fun t  ->
                               fun wp  ->
                                 fun e  ->
                                   let uu____21638 =
                                     (e1.mlift).mlift_wp u t wp  in
                                   let uu____21639 = l1 u t wp e  in
                                   l2 u t uu____21638 uu____21639))
                   | uu____21640 -> FStar_Pervasives_Native.None  in
                 {
                   mlift_t = FStar_Pervasives_Native.None;
                   mlift_wp;
                   mlift_term
                 }  in
               {
                 msource = (e1.msource);
                 mtarget = (e2.mtarget);
                 mlift = composed_lift
               }  in
             let mk_mlift_wp lift_t u r wp1 =
               let uu____21712 = inst_tscheme_with lift_t [u]  in
               match uu____21712 with
               | (uu____21719,lift_t1) ->
                   let uu____21721 =
                     let uu____21728 =
                       let uu____21729 =
                         let uu____21746 =
                           let uu____21757 = FStar_Syntax_Syntax.as_arg r  in
                           let uu____21766 =
                             let uu____21777 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____21777]  in
                           uu____21757 :: uu____21766  in
                         (lift_t1, uu____21746)  in
                       FStar_Syntax_Syntax.Tm_app uu____21729  in
                     FStar_Syntax_Syntax.mk uu____21728  in
                   uu____21721 FStar_Pervasives_Native.None
                     wp1.FStar_Syntax_Syntax.pos
                in
             let sub_mlift_wp =
               match sub1.FStar_Syntax_Syntax.lift_wp with
               | FStar_Pervasives_Native.Some sub_lift_wp ->
                   mk_mlift_wp sub_lift_wp
               | FStar_Pervasives_Native.None  ->
                   failwith
                     "sub effect should've been elaborated at this stage"
                in
             let mk_mlift_term lift_t u r wp1 e =
               let uu____21887 = inst_tscheme_with lift_t [u]  in
               match uu____21887 with
               | (uu____21894,lift_t1) ->
                   let uu____21896 =
                     let uu____21903 =
                       let uu____21904 =
                         let uu____21921 =
                           let uu____21932 = FStar_Syntax_Syntax.as_arg r  in
                           let uu____21941 =
                             let uu____21952 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             let uu____21961 =
                               let uu____21972 = FStar_Syntax_Syntax.as_arg e
                                  in
                               [uu____21972]  in
                             uu____21952 :: uu____21961  in
                           uu____21932 :: uu____21941  in
                         (lift_t1, uu____21921)  in
                       FStar_Syntax_Syntax.Tm_app uu____21904  in
                     FStar_Syntax_Syntax.mk uu____21903  in
                   uu____21896 FStar_Pervasives_Native.None
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
                   {
                     mlift_t = FStar_Pervasives_Native.None;
                     mlift_wp = sub_mlift_wp;
                     mlift_term = sub_mlift_term
                   }
               }  in
             let id_edge l =
               {
                 msource = (sub1.FStar_Syntax_Syntax.source);
                 mtarget = (sub1.FStar_Syntax_Syntax.target);
                 mlift = identity_mlift
               }  in
             let print_mlift l =
               let bogus_term s =
                 let uu____22074 =
                   let uu____22075 =
                     FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                   FStar_Syntax_Syntax.lid_as_fv uu____22075
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____22074  in
               let arg = bogus_term "ARG"  in
               let wp = bogus_term "WP"  in
               let e = bogus_term "COMP"  in
               let uu____22084 =
                 let uu____22086 =
                   l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
                 FStar_Syntax_Print.term_to_string uu____22086  in
               let uu____22087 =
                 let uu____22089 =
                   FStar_Util.map_opt l.mlift_term
                     (fun l1  ->
                        let uu____22117 =
                          l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                        FStar_Syntax_Print.term_to_string uu____22117)
                    in
                 FStar_Util.dflt "none" uu____22089  in
               FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22084
                 uu____22087
                in
             let order = edge :: ((env.effects).order)  in
             let ms =
               FStar_All.pipe_right (env.effects).decls
                 (FStar_List.map
                    (fun uu____22146  ->
                       match uu____22146 with
                       | (e,uu____22154) -> e.FStar_Syntax_Syntax.mname))
                in
             let find_edge order1 uu____22177 =
               match uu____22177 with
               | (i,j) ->
                   let uu____22188 = FStar_Ident.lid_equals i j  in
                   if uu____22188
                   then
                     FStar_All.pipe_right (id_edge i)
                       (fun _22195  -> FStar_Pervasives_Native.Some _22195)
                   else
                     FStar_All.pipe_right order1
                       (FStar_Util.find_opt
                          (fun e  ->
                             (FStar_Ident.lid_equals e.msource i) &&
                               (FStar_Ident.lid_equals e.mtarget j)))
                in
             let order1 =
               let fold_fun order1 k =
                 let uu____22224 =
                   FStar_All.pipe_right ms
                     (FStar_List.collect
                        (fun i  ->
                           let uu____22234 = FStar_Ident.lid_equals i k  in
                           if uu____22234
                           then []
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.collect
                                  (fun j  ->
                                     let uu____22248 =
                                       FStar_Ident.lid_equals j k  in
                                     if uu____22248
                                     then []
                                     else
                                       (let uu____22255 =
                                          let uu____22264 =
                                            find_edge order1 (i, k)  in
                                          let uu____22267 =
                                            find_edge order1 (k, j)  in
                                          (uu____22264, uu____22267)  in
                                        match uu____22255 with
                                        | (FStar_Pervasives_Native.Some
                                           e1,FStar_Pervasives_Native.Some
                                           e2) ->
                                            let uu____22282 =
                                              compose_edges e1 e2  in
                                            [uu____22282]
                                        | uu____22283 -> [])))))
                    in
                 FStar_List.append order1 uu____22224  in
               FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)
                in
             let order2 =
               FStar_Util.remove_dups
                 (fun e1  ->
                    fun e2  ->
                      (FStar_Ident.lid_equals e1.msource e2.msource) &&
                        (FStar_Ident.lid_equals e1.mtarget e2.mtarget))
                 order1
                in
             FStar_All.pipe_right order2
               (FStar_List.iter
                  (fun edge1  ->
                     let uu____22313 =
                       (FStar_Ident.lid_equals edge1.msource
                          FStar_Parser_Const.effect_DIV_lid)
                         &&
                         (let uu____22316 =
                            lookup_effect_quals env edge1.mtarget  in
                          FStar_All.pipe_right uu____22316
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect))
                        in
                     if uu____22313
                     then
                       let uu____22323 =
                         let uu____22329 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                           uu____22329)
                          in
                       let uu____22333 = get_range env  in
                       FStar_Errors.raise_error uu____22323 uu____22333
                     else ()));
             (let joins =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        FStar_All.pipe_right ms
                          (FStar_List.collect
                             (fun j  ->
                                let join_opt =
                                  let uu____22411 =
                                    FStar_Ident.lid_equals i j  in
                                  if uu____22411
                                  then
                                    FStar_Pervasives_Native.Some
                                      (i, (id_edge i), (id_edge i))
                                  else
                                    FStar_All.pipe_right ms
                                      (FStar_List.fold_left
                                         (fun bopt  ->
                                            fun k  ->
                                              let uu____22463 =
                                                let uu____22472 =
                                                  find_edge order2 (i, k)  in
                                                let uu____22475 =
                                                  find_edge order2 (j, k)  in
                                                (uu____22472, uu____22475)
                                                 in
                                              match uu____22463 with
                                              | (FStar_Pervasives_Native.Some
                                                 ik,FStar_Pervasives_Native.Some
                                                 jk) ->
                                                  (match bopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.Some
                                                         (k, ik, jk)
                                                   | FStar_Pervasives_Native.Some
                                                       (ub,uu____22517,uu____22518)
                                                       ->
                                                       let uu____22525 =
                                                         let uu____22532 =
                                                           let uu____22534 =
                                                             find_edge order2
                                                               (k, ub)
                                                              in
                                                           FStar_Util.is_some
                                                             uu____22534
                                                            in
                                                         let uu____22537 =
                                                           let uu____22539 =
                                                             find_edge order2
                                                               (ub, k)
                                                              in
                                                           FStar_Util.is_some
                                                             uu____22539
                                                            in
                                                         (uu____22532,
                                                           uu____22537)
                                                          in
                                                       (match uu____22525
                                                        with
                                                        | (true ,true ) ->
                                                            let uu____22556 =
                                                              FStar_Ident.lid_equals
                                                                k ub
                                                               in
                                                            if uu____22556
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
                                              | uu____22599 -> bopt)
                                         FStar_Pervasives_Native.None)
                                   in
                                match join_opt with
                                | FStar_Pervasives_Native.None  -> []
                                | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                    [(i, j, k, (e1.mlift), (e2.mlift))]))))
                 in
              let effects =
                let uu___1665_22672 = env.effects  in
                { decls = (uu___1665_22672.decls); order = order2; joins }
                 in
              let uu___1668_22673 = env  in
              {
                solver = (uu___1668_22673.solver);
                range = (uu___1668_22673.range);
                curmodule = (uu___1668_22673.curmodule);
                gamma = (uu___1668_22673.gamma);
                gamma_sig = (uu___1668_22673.gamma_sig);
                gamma_cache = (uu___1668_22673.gamma_cache);
                modules = (uu___1668_22673.modules);
                expected_typ = (uu___1668_22673.expected_typ);
                sigtab = (uu___1668_22673.sigtab);
                attrtab = (uu___1668_22673.attrtab);
                is_pattern = (uu___1668_22673.is_pattern);
                instantiate_imp = (uu___1668_22673.instantiate_imp);
                effects;
                generalize = (uu___1668_22673.generalize);
                letrecs = (uu___1668_22673.letrecs);
                top_level = (uu___1668_22673.top_level);
                check_uvars = (uu___1668_22673.check_uvars);
                use_eq = (uu___1668_22673.use_eq);
                is_iface = (uu___1668_22673.is_iface);
                admit = (uu___1668_22673.admit);
                lax = (uu___1668_22673.lax);
                lax_universes = (uu___1668_22673.lax_universes);
                phase1 = (uu___1668_22673.phase1);
                failhard = (uu___1668_22673.failhard);
                nosynth = (uu___1668_22673.nosynth);
                uvar_subtyping = (uu___1668_22673.uvar_subtyping);
                tc_term = (uu___1668_22673.tc_term);
                type_of = (uu___1668_22673.type_of);
                universe_of = (uu___1668_22673.universe_of);
                check_type_of = (uu___1668_22673.check_type_of);
                use_bv_sorts = (uu___1668_22673.use_bv_sorts);
                qtbl_name_and_index = (uu___1668_22673.qtbl_name_and_index);
                normalized_eff_names = (uu___1668_22673.normalized_eff_names);
                fv_delta_depths = (uu___1668_22673.fv_delta_depths);
                proof_ns = (uu___1668_22673.proof_ns);
                synth_hook = (uu___1668_22673.synth_hook);
                splice = (uu___1668_22673.splice);
                postprocess = (uu___1668_22673.postprocess);
                is_native_tactic = (uu___1668_22673.is_native_tactic);
                identifier_info = (uu___1668_22673.identifier_info);
                tc_hooks = (uu___1668_22673.tc_hooks);
                dsenv = (uu___1668_22673.dsenv);
                nbe = (uu___1668_22673.nbe);
                strict_args_tab = (uu___1668_22673.strict_args_tab)
              }))
      | uu____22674 -> env
  
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
        | uu____22703 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22716 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22716 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22733 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22733 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22758 =
                     let uu____22764 =
                       let uu____22766 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22774 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22785 =
                         let uu____22787 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22787  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22766 uu____22774 uu____22785
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22764)
                      in
                   FStar_Errors.raise_error uu____22758
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22795 =
                     let uu____22806 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22806 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22843  ->
                        fun uu____22844  ->
                          match (uu____22843, uu____22844) with
                          | ((x,uu____22874),(t,uu____22876)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22795
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22907 =
                     let uu___1706_22908 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1706_22908.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1706_22908.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1706_22908.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1706_22908.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22907
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22920 .
    'Auu____22920 ->
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
          let uu____22950 = effect_decl_opt env effect_name  in
          match uu____22950 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22993 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____23016 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____23055 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____23055
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____23060 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____23060
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____23071 =
                     let uu____23074 = get_range env  in
                     let uu____23075 =
                       let uu____23082 =
                         let uu____23083 =
                           let uu____23100 =
                             let uu____23111 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23111; wp]  in
                           (repr, uu____23100)  in
                         FStar_Syntax_Syntax.Tm_app uu____23083  in
                       FStar_Syntax_Syntax.mk uu____23082  in
                     uu____23075 FStar_Pervasives_Native.None uu____23074  in
                   FStar_Pervasives_Native.Some uu____23071)
  
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
      | uu____23255 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23270 =
        let uu____23271 = FStar_Syntax_Subst.compress t  in
        uu____23271.FStar_Syntax_Syntax.n  in
      match uu____23270 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23275,c) ->
          is_reifiable_comp env c
      | uu____23297 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23317 =
           let uu____23319 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23319  in
         if uu____23317
         then
           let uu____23322 =
             let uu____23328 =
               let uu____23330 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23330
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23328)  in
           let uu____23334 = get_range env  in
           FStar_Errors.raise_error uu____23322 uu____23334
         else ());
        (let uu____23337 = effect_repr_aux true env c u_c  in
         match uu____23337 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1771_23373 = env  in
        {
          solver = (uu___1771_23373.solver);
          range = (uu___1771_23373.range);
          curmodule = (uu___1771_23373.curmodule);
          gamma = (uu___1771_23373.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1771_23373.gamma_cache);
          modules = (uu___1771_23373.modules);
          expected_typ = (uu___1771_23373.expected_typ);
          sigtab = (uu___1771_23373.sigtab);
          attrtab = (uu___1771_23373.attrtab);
          is_pattern = (uu___1771_23373.is_pattern);
          instantiate_imp = (uu___1771_23373.instantiate_imp);
          effects = (uu___1771_23373.effects);
          generalize = (uu___1771_23373.generalize);
          letrecs = (uu___1771_23373.letrecs);
          top_level = (uu___1771_23373.top_level);
          check_uvars = (uu___1771_23373.check_uvars);
          use_eq = (uu___1771_23373.use_eq);
          is_iface = (uu___1771_23373.is_iface);
          admit = (uu___1771_23373.admit);
          lax = (uu___1771_23373.lax);
          lax_universes = (uu___1771_23373.lax_universes);
          phase1 = (uu___1771_23373.phase1);
          failhard = (uu___1771_23373.failhard);
          nosynth = (uu___1771_23373.nosynth);
          uvar_subtyping = (uu___1771_23373.uvar_subtyping);
          tc_term = (uu___1771_23373.tc_term);
          type_of = (uu___1771_23373.type_of);
          universe_of = (uu___1771_23373.universe_of);
          check_type_of = (uu___1771_23373.check_type_of);
          use_bv_sorts = (uu___1771_23373.use_bv_sorts);
          qtbl_name_and_index = (uu___1771_23373.qtbl_name_and_index);
          normalized_eff_names = (uu___1771_23373.normalized_eff_names);
          fv_delta_depths = (uu___1771_23373.fv_delta_depths);
          proof_ns = (uu___1771_23373.proof_ns);
          synth_hook = (uu___1771_23373.synth_hook);
          splice = (uu___1771_23373.splice);
          postprocess = (uu___1771_23373.postprocess);
          is_native_tactic = (uu___1771_23373.is_native_tactic);
          identifier_info = (uu___1771_23373.identifier_info);
          tc_hooks = (uu___1771_23373.tc_hooks);
          dsenv = (uu___1771_23373.dsenv);
          nbe = (uu___1771_23373.nbe);
          strict_args_tab = (uu___1771_23373.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1778_23387 = env  in
      {
        solver = (uu___1778_23387.solver);
        range = (uu___1778_23387.range);
        curmodule = (uu___1778_23387.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1778_23387.gamma_sig);
        gamma_cache = (uu___1778_23387.gamma_cache);
        modules = (uu___1778_23387.modules);
        expected_typ = (uu___1778_23387.expected_typ);
        sigtab = (uu___1778_23387.sigtab);
        attrtab = (uu___1778_23387.attrtab);
        is_pattern = (uu___1778_23387.is_pattern);
        instantiate_imp = (uu___1778_23387.instantiate_imp);
        effects = (uu___1778_23387.effects);
        generalize = (uu___1778_23387.generalize);
        letrecs = (uu___1778_23387.letrecs);
        top_level = (uu___1778_23387.top_level);
        check_uvars = (uu___1778_23387.check_uvars);
        use_eq = (uu___1778_23387.use_eq);
        is_iface = (uu___1778_23387.is_iface);
        admit = (uu___1778_23387.admit);
        lax = (uu___1778_23387.lax);
        lax_universes = (uu___1778_23387.lax_universes);
        phase1 = (uu___1778_23387.phase1);
        failhard = (uu___1778_23387.failhard);
        nosynth = (uu___1778_23387.nosynth);
        uvar_subtyping = (uu___1778_23387.uvar_subtyping);
        tc_term = (uu___1778_23387.tc_term);
        type_of = (uu___1778_23387.type_of);
        universe_of = (uu___1778_23387.universe_of);
        check_type_of = (uu___1778_23387.check_type_of);
        use_bv_sorts = (uu___1778_23387.use_bv_sorts);
        qtbl_name_and_index = (uu___1778_23387.qtbl_name_and_index);
        normalized_eff_names = (uu___1778_23387.normalized_eff_names);
        fv_delta_depths = (uu___1778_23387.fv_delta_depths);
        proof_ns = (uu___1778_23387.proof_ns);
        synth_hook = (uu___1778_23387.synth_hook);
        splice = (uu___1778_23387.splice);
        postprocess = (uu___1778_23387.postprocess);
        is_native_tactic = (uu___1778_23387.is_native_tactic);
        identifier_info = (uu___1778_23387.identifier_info);
        tc_hooks = (uu___1778_23387.tc_hooks);
        dsenv = (uu___1778_23387.dsenv);
        nbe = (uu___1778_23387.nbe);
        strict_args_tab = (uu___1778_23387.strict_args_tab)
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
            (let uu___1791_23445 = env  in
             {
               solver = (uu___1791_23445.solver);
               range = (uu___1791_23445.range);
               curmodule = (uu___1791_23445.curmodule);
               gamma = rest;
               gamma_sig = (uu___1791_23445.gamma_sig);
               gamma_cache = (uu___1791_23445.gamma_cache);
               modules = (uu___1791_23445.modules);
               expected_typ = (uu___1791_23445.expected_typ);
               sigtab = (uu___1791_23445.sigtab);
               attrtab = (uu___1791_23445.attrtab);
               is_pattern = (uu___1791_23445.is_pattern);
               instantiate_imp = (uu___1791_23445.instantiate_imp);
               effects = (uu___1791_23445.effects);
               generalize = (uu___1791_23445.generalize);
               letrecs = (uu___1791_23445.letrecs);
               top_level = (uu___1791_23445.top_level);
               check_uvars = (uu___1791_23445.check_uvars);
               use_eq = (uu___1791_23445.use_eq);
               is_iface = (uu___1791_23445.is_iface);
               admit = (uu___1791_23445.admit);
               lax = (uu___1791_23445.lax);
               lax_universes = (uu___1791_23445.lax_universes);
               phase1 = (uu___1791_23445.phase1);
               failhard = (uu___1791_23445.failhard);
               nosynth = (uu___1791_23445.nosynth);
               uvar_subtyping = (uu___1791_23445.uvar_subtyping);
               tc_term = (uu___1791_23445.tc_term);
               type_of = (uu___1791_23445.type_of);
               universe_of = (uu___1791_23445.universe_of);
               check_type_of = (uu___1791_23445.check_type_of);
               use_bv_sorts = (uu___1791_23445.use_bv_sorts);
               qtbl_name_and_index = (uu___1791_23445.qtbl_name_and_index);
               normalized_eff_names = (uu___1791_23445.normalized_eff_names);
               fv_delta_depths = (uu___1791_23445.fv_delta_depths);
               proof_ns = (uu___1791_23445.proof_ns);
               synth_hook = (uu___1791_23445.synth_hook);
               splice = (uu___1791_23445.splice);
               postprocess = (uu___1791_23445.postprocess);
               is_native_tactic = (uu___1791_23445.is_native_tactic);
               identifier_info = (uu___1791_23445.identifier_info);
               tc_hooks = (uu___1791_23445.tc_hooks);
               dsenv = (uu___1791_23445.dsenv);
               nbe = (uu___1791_23445.nbe);
               strict_args_tab = (uu___1791_23445.strict_args_tab)
             }))
    | uu____23446 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23475  ->
             match uu____23475 with | (x,uu____23483) -> push_bv env1 x) env
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
            let uu___1805_23518 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1805_23518.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1805_23518.FStar_Syntax_Syntax.index);
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
      (let uu___1816_23560 = env  in
       {
         solver = (uu___1816_23560.solver);
         range = (uu___1816_23560.range);
         curmodule = (uu___1816_23560.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1816_23560.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1816_23560.sigtab);
         attrtab = (uu___1816_23560.attrtab);
         is_pattern = (uu___1816_23560.is_pattern);
         instantiate_imp = (uu___1816_23560.instantiate_imp);
         effects = (uu___1816_23560.effects);
         generalize = (uu___1816_23560.generalize);
         letrecs = (uu___1816_23560.letrecs);
         top_level = (uu___1816_23560.top_level);
         check_uvars = (uu___1816_23560.check_uvars);
         use_eq = (uu___1816_23560.use_eq);
         is_iface = (uu___1816_23560.is_iface);
         admit = (uu___1816_23560.admit);
         lax = (uu___1816_23560.lax);
         lax_universes = (uu___1816_23560.lax_universes);
         phase1 = (uu___1816_23560.phase1);
         failhard = (uu___1816_23560.failhard);
         nosynth = (uu___1816_23560.nosynth);
         uvar_subtyping = (uu___1816_23560.uvar_subtyping);
         tc_term = (uu___1816_23560.tc_term);
         type_of = (uu___1816_23560.type_of);
         universe_of = (uu___1816_23560.universe_of);
         check_type_of = (uu___1816_23560.check_type_of);
         use_bv_sorts = (uu___1816_23560.use_bv_sorts);
         qtbl_name_and_index = (uu___1816_23560.qtbl_name_and_index);
         normalized_eff_names = (uu___1816_23560.normalized_eff_names);
         fv_delta_depths = (uu___1816_23560.fv_delta_depths);
         proof_ns = (uu___1816_23560.proof_ns);
         synth_hook = (uu___1816_23560.synth_hook);
         splice = (uu___1816_23560.splice);
         postprocess = (uu___1816_23560.postprocess);
         is_native_tactic = (uu___1816_23560.is_native_tactic);
         identifier_info = (uu___1816_23560.identifier_info);
         tc_hooks = (uu___1816_23560.tc_hooks);
         dsenv = (uu___1816_23560.dsenv);
         nbe = (uu___1816_23560.nbe);
         strict_args_tab = (uu___1816_23560.strict_args_tab)
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
        let uu____23604 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23604 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23632 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23632)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1831_23648 = env  in
      {
        solver = (uu___1831_23648.solver);
        range = (uu___1831_23648.range);
        curmodule = (uu___1831_23648.curmodule);
        gamma = (uu___1831_23648.gamma);
        gamma_sig = (uu___1831_23648.gamma_sig);
        gamma_cache = (uu___1831_23648.gamma_cache);
        modules = (uu___1831_23648.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1831_23648.sigtab);
        attrtab = (uu___1831_23648.attrtab);
        is_pattern = (uu___1831_23648.is_pattern);
        instantiate_imp = (uu___1831_23648.instantiate_imp);
        effects = (uu___1831_23648.effects);
        generalize = (uu___1831_23648.generalize);
        letrecs = (uu___1831_23648.letrecs);
        top_level = (uu___1831_23648.top_level);
        check_uvars = (uu___1831_23648.check_uvars);
        use_eq = false;
        is_iface = (uu___1831_23648.is_iface);
        admit = (uu___1831_23648.admit);
        lax = (uu___1831_23648.lax);
        lax_universes = (uu___1831_23648.lax_universes);
        phase1 = (uu___1831_23648.phase1);
        failhard = (uu___1831_23648.failhard);
        nosynth = (uu___1831_23648.nosynth);
        uvar_subtyping = (uu___1831_23648.uvar_subtyping);
        tc_term = (uu___1831_23648.tc_term);
        type_of = (uu___1831_23648.type_of);
        universe_of = (uu___1831_23648.universe_of);
        check_type_of = (uu___1831_23648.check_type_of);
        use_bv_sorts = (uu___1831_23648.use_bv_sorts);
        qtbl_name_and_index = (uu___1831_23648.qtbl_name_and_index);
        normalized_eff_names = (uu___1831_23648.normalized_eff_names);
        fv_delta_depths = (uu___1831_23648.fv_delta_depths);
        proof_ns = (uu___1831_23648.proof_ns);
        synth_hook = (uu___1831_23648.synth_hook);
        splice = (uu___1831_23648.splice);
        postprocess = (uu___1831_23648.postprocess);
        is_native_tactic = (uu___1831_23648.is_native_tactic);
        identifier_info = (uu___1831_23648.identifier_info);
        tc_hooks = (uu___1831_23648.tc_hooks);
        dsenv = (uu___1831_23648.dsenv);
        nbe = (uu___1831_23648.nbe);
        strict_args_tab = (uu___1831_23648.strict_args_tab)
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
    let uu____23679 = expected_typ env_  in
    ((let uu___1838_23685 = env_  in
      {
        solver = (uu___1838_23685.solver);
        range = (uu___1838_23685.range);
        curmodule = (uu___1838_23685.curmodule);
        gamma = (uu___1838_23685.gamma);
        gamma_sig = (uu___1838_23685.gamma_sig);
        gamma_cache = (uu___1838_23685.gamma_cache);
        modules = (uu___1838_23685.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1838_23685.sigtab);
        attrtab = (uu___1838_23685.attrtab);
        is_pattern = (uu___1838_23685.is_pattern);
        instantiate_imp = (uu___1838_23685.instantiate_imp);
        effects = (uu___1838_23685.effects);
        generalize = (uu___1838_23685.generalize);
        letrecs = (uu___1838_23685.letrecs);
        top_level = (uu___1838_23685.top_level);
        check_uvars = (uu___1838_23685.check_uvars);
        use_eq = false;
        is_iface = (uu___1838_23685.is_iface);
        admit = (uu___1838_23685.admit);
        lax = (uu___1838_23685.lax);
        lax_universes = (uu___1838_23685.lax_universes);
        phase1 = (uu___1838_23685.phase1);
        failhard = (uu___1838_23685.failhard);
        nosynth = (uu___1838_23685.nosynth);
        uvar_subtyping = (uu___1838_23685.uvar_subtyping);
        tc_term = (uu___1838_23685.tc_term);
        type_of = (uu___1838_23685.type_of);
        universe_of = (uu___1838_23685.universe_of);
        check_type_of = (uu___1838_23685.check_type_of);
        use_bv_sorts = (uu___1838_23685.use_bv_sorts);
        qtbl_name_and_index = (uu___1838_23685.qtbl_name_and_index);
        normalized_eff_names = (uu___1838_23685.normalized_eff_names);
        fv_delta_depths = (uu___1838_23685.fv_delta_depths);
        proof_ns = (uu___1838_23685.proof_ns);
        synth_hook = (uu___1838_23685.synth_hook);
        splice = (uu___1838_23685.splice);
        postprocess = (uu___1838_23685.postprocess);
        is_native_tactic = (uu___1838_23685.is_native_tactic);
        identifier_info = (uu___1838_23685.identifier_info);
        tc_hooks = (uu___1838_23685.tc_hooks);
        dsenv = (uu___1838_23685.dsenv);
        nbe = (uu___1838_23685.nbe);
        strict_args_tab = (uu___1838_23685.strict_args_tab)
      }), uu____23679)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23697 =
      let uu____23700 = FStar_Ident.id_of_text ""  in [uu____23700]  in
    FStar_Ident.lid_of_ids uu____23697  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23707 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23707
        then
          let uu____23712 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23712 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1846_23740 = env  in
       {
         solver = (uu___1846_23740.solver);
         range = (uu___1846_23740.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1846_23740.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1846_23740.expected_typ);
         sigtab = (uu___1846_23740.sigtab);
         attrtab = (uu___1846_23740.attrtab);
         is_pattern = (uu___1846_23740.is_pattern);
         instantiate_imp = (uu___1846_23740.instantiate_imp);
         effects = (uu___1846_23740.effects);
         generalize = (uu___1846_23740.generalize);
         letrecs = (uu___1846_23740.letrecs);
         top_level = (uu___1846_23740.top_level);
         check_uvars = (uu___1846_23740.check_uvars);
         use_eq = (uu___1846_23740.use_eq);
         is_iface = (uu___1846_23740.is_iface);
         admit = (uu___1846_23740.admit);
         lax = (uu___1846_23740.lax);
         lax_universes = (uu___1846_23740.lax_universes);
         phase1 = (uu___1846_23740.phase1);
         failhard = (uu___1846_23740.failhard);
         nosynth = (uu___1846_23740.nosynth);
         uvar_subtyping = (uu___1846_23740.uvar_subtyping);
         tc_term = (uu___1846_23740.tc_term);
         type_of = (uu___1846_23740.type_of);
         universe_of = (uu___1846_23740.universe_of);
         check_type_of = (uu___1846_23740.check_type_of);
         use_bv_sorts = (uu___1846_23740.use_bv_sorts);
         qtbl_name_and_index = (uu___1846_23740.qtbl_name_and_index);
         normalized_eff_names = (uu___1846_23740.normalized_eff_names);
         fv_delta_depths = (uu___1846_23740.fv_delta_depths);
         proof_ns = (uu___1846_23740.proof_ns);
         synth_hook = (uu___1846_23740.synth_hook);
         splice = (uu___1846_23740.splice);
         postprocess = (uu___1846_23740.postprocess);
         is_native_tactic = (uu___1846_23740.is_native_tactic);
         identifier_info = (uu___1846_23740.identifier_info);
         tc_hooks = (uu___1846_23740.tc_hooks);
         dsenv = (uu___1846_23740.dsenv);
         nbe = (uu___1846_23740.nbe);
         strict_args_tab = (uu___1846_23740.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23792)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23796,(uu____23797,t)))::tl1
          ->
          let uu____23818 =
            let uu____23821 = FStar_Syntax_Free.uvars t  in
            ext out uu____23821  in
          aux uu____23818 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23824;
            FStar_Syntax_Syntax.index = uu____23825;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23833 =
            let uu____23836 = FStar_Syntax_Free.uvars t  in
            ext out uu____23836  in
          aux uu____23833 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23894)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23898,(uu____23899,t)))::tl1
          ->
          let uu____23920 =
            let uu____23923 = FStar_Syntax_Free.univs t  in
            ext out uu____23923  in
          aux uu____23920 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23926;
            FStar_Syntax_Syntax.index = uu____23927;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23935 =
            let uu____23938 = FStar_Syntax_Free.univs t  in
            ext out uu____23938  in
          aux uu____23935 tl1
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
          let uu____24000 = FStar_Util.set_add uname out  in
          aux uu____24000 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24003,(uu____24004,t)))::tl1
          ->
          let uu____24025 =
            let uu____24028 = FStar_Syntax_Free.univnames t  in
            ext out uu____24028  in
          aux uu____24025 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24031;
            FStar_Syntax_Syntax.index = uu____24032;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24040 =
            let uu____24043 = FStar_Syntax_Free.univnames t  in
            ext out uu____24043  in
          aux uu____24040 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24064  ->
            match uu___11_24064 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24068 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24081 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24092 =
      let uu____24101 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24101
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24092 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24149 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24162  ->
              match uu___12_24162 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24165 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24165
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24171) ->
                  let uu____24188 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24188))
       in
    FStar_All.pipe_right uu____24149 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24202  ->
    match uu___13_24202 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24208 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24208
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24231  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24286) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24319,uu____24320) -> false  in
      let uu____24334 =
        FStar_List.tryFind
          (fun uu____24356  ->
             match uu____24356 with | (p,uu____24367) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24334 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24386,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24416 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24416
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1989_24438 = e  in
        {
          solver = (uu___1989_24438.solver);
          range = (uu___1989_24438.range);
          curmodule = (uu___1989_24438.curmodule);
          gamma = (uu___1989_24438.gamma);
          gamma_sig = (uu___1989_24438.gamma_sig);
          gamma_cache = (uu___1989_24438.gamma_cache);
          modules = (uu___1989_24438.modules);
          expected_typ = (uu___1989_24438.expected_typ);
          sigtab = (uu___1989_24438.sigtab);
          attrtab = (uu___1989_24438.attrtab);
          is_pattern = (uu___1989_24438.is_pattern);
          instantiate_imp = (uu___1989_24438.instantiate_imp);
          effects = (uu___1989_24438.effects);
          generalize = (uu___1989_24438.generalize);
          letrecs = (uu___1989_24438.letrecs);
          top_level = (uu___1989_24438.top_level);
          check_uvars = (uu___1989_24438.check_uvars);
          use_eq = (uu___1989_24438.use_eq);
          is_iface = (uu___1989_24438.is_iface);
          admit = (uu___1989_24438.admit);
          lax = (uu___1989_24438.lax);
          lax_universes = (uu___1989_24438.lax_universes);
          phase1 = (uu___1989_24438.phase1);
          failhard = (uu___1989_24438.failhard);
          nosynth = (uu___1989_24438.nosynth);
          uvar_subtyping = (uu___1989_24438.uvar_subtyping);
          tc_term = (uu___1989_24438.tc_term);
          type_of = (uu___1989_24438.type_of);
          universe_of = (uu___1989_24438.universe_of);
          check_type_of = (uu___1989_24438.check_type_of);
          use_bv_sorts = (uu___1989_24438.use_bv_sorts);
          qtbl_name_and_index = (uu___1989_24438.qtbl_name_and_index);
          normalized_eff_names = (uu___1989_24438.normalized_eff_names);
          fv_delta_depths = (uu___1989_24438.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1989_24438.synth_hook);
          splice = (uu___1989_24438.splice);
          postprocess = (uu___1989_24438.postprocess);
          is_native_tactic = (uu___1989_24438.is_native_tactic);
          identifier_info = (uu___1989_24438.identifier_info);
          tc_hooks = (uu___1989_24438.tc_hooks);
          dsenv = (uu___1989_24438.dsenv);
          nbe = (uu___1989_24438.nbe);
          strict_args_tab = (uu___1989_24438.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1998_24486 = e  in
      {
        solver = (uu___1998_24486.solver);
        range = (uu___1998_24486.range);
        curmodule = (uu___1998_24486.curmodule);
        gamma = (uu___1998_24486.gamma);
        gamma_sig = (uu___1998_24486.gamma_sig);
        gamma_cache = (uu___1998_24486.gamma_cache);
        modules = (uu___1998_24486.modules);
        expected_typ = (uu___1998_24486.expected_typ);
        sigtab = (uu___1998_24486.sigtab);
        attrtab = (uu___1998_24486.attrtab);
        is_pattern = (uu___1998_24486.is_pattern);
        instantiate_imp = (uu___1998_24486.instantiate_imp);
        effects = (uu___1998_24486.effects);
        generalize = (uu___1998_24486.generalize);
        letrecs = (uu___1998_24486.letrecs);
        top_level = (uu___1998_24486.top_level);
        check_uvars = (uu___1998_24486.check_uvars);
        use_eq = (uu___1998_24486.use_eq);
        is_iface = (uu___1998_24486.is_iface);
        admit = (uu___1998_24486.admit);
        lax = (uu___1998_24486.lax);
        lax_universes = (uu___1998_24486.lax_universes);
        phase1 = (uu___1998_24486.phase1);
        failhard = (uu___1998_24486.failhard);
        nosynth = (uu___1998_24486.nosynth);
        uvar_subtyping = (uu___1998_24486.uvar_subtyping);
        tc_term = (uu___1998_24486.tc_term);
        type_of = (uu___1998_24486.type_of);
        universe_of = (uu___1998_24486.universe_of);
        check_type_of = (uu___1998_24486.check_type_of);
        use_bv_sorts = (uu___1998_24486.use_bv_sorts);
        qtbl_name_and_index = (uu___1998_24486.qtbl_name_and_index);
        normalized_eff_names = (uu___1998_24486.normalized_eff_names);
        fv_delta_depths = (uu___1998_24486.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1998_24486.synth_hook);
        splice = (uu___1998_24486.splice);
        postprocess = (uu___1998_24486.postprocess);
        is_native_tactic = (uu___1998_24486.is_native_tactic);
        identifier_info = (uu___1998_24486.identifier_info);
        tc_hooks = (uu___1998_24486.tc_hooks);
        dsenv = (uu___1998_24486.dsenv);
        nbe = (uu___1998_24486.nbe);
        strict_args_tab = (uu___1998_24486.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24502 = FStar_Syntax_Free.names t  in
      let uu____24505 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24502 uu____24505
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24528 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24528
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24538 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24538
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24559 =
      match uu____24559 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24579 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24579)
       in
    let uu____24587 =
      let uu____24591 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24591 FStar_List.rev  in
    FStar_All.pipe_right uu____24587 (FStar_String.concat " ")
  
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
                  (let uu____24661 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24661 with
                   | FStar_Pervasives_Native.Some uu____24665 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24668 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24678;
        univ_ineqs = uu____24679; implicits = uu____24680;_} -> true
    | uu____24692 -> false
  
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
          let uu___2042_24723 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2042_24723.deferred);
            univ_ineqs = (uu___2042_24723.univ_ineqs);
            implicits = (uu___2042_24723.implicits)
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
          let uu____24762 = FStar_Options.defensive ()  in
          if uu____24762
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24768 =
              let uu____24770 =
                let uu____24772 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24772  in
              Prims.op_Negation uu____24770  in
            (if uu____24768
             then
               let uu____24779 =
                 let uu____24785 =
                   let uu____24787 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24789 =
                     let uu____24791 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24791
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24787 uu____24789
                    in
                 (FStar_Errors.Warning_Defensive, uu____24785)  in
               FStar_Errors.log_issue rng uu____24779
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
          let uu____24831 =
            let uu____24833 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24833  in
          if uu____24831
          then ()
          else
            (let uu____24838 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24838 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24864 =
            let uu____24866 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24866  in
          if uu____24864
          then ()
          else
            (let uu____24871 = bound_vars e  in
             def_check_closed_in rng msg uu____24871 t)
  
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
          let uu___2079_24910 = g  in
          let uu____24911 =
            let uu____24912 =
              let uu____24913 =
                let uu____24920 =
                  let uu____24921 =
                    let uu____24938 =
                      let uu____24949 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24949]  in
                    (f, uu____24938)  in
                  FStar_Syntax_Syntax.Tm_app uu____24921  in
                FStar_Syntax_Syntax.mk uu____24920  in
              uu____24913 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24986  -> FStar_TypeChecker_Common.NonTrivial _24986)
              uu____24912
             in
          {
            guard_f = uu____24911;
            deferred = (uu___2079_24910.deferred);
            univ_ineqs = (uu___2079_24910.univ_ineqs);
            implicits = (uu___2079_24910.implicits)
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
          let uu___2086_25004 = g  in
          let uu____25005 =
            let uu____25006 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25006  in
          {
            guard_f = uu____25005;
            deferred = (uu___2086_25004.deferred);
            univ_ineqs = (uu___2086_25004.univ_ineqs);
            implicits = (uu___2086_25004.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2091_25023 = g  in
          let uu____25024 =
            let uu____25025 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25025  in
          {
            guard_f = uu____25024;
            deferred = (uu___2091_25023.deferred);
            univ_ineqs = (uu___2091_25023.univ_ineqs);
            implicits = (uu___2091_25023.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2095_25027 = g  in
          let uu____25028 =
            let uu____25029 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25029  in
          {
            guard_f = uu____25028;
            deferred = (uu___2095_25027.deferred);
            univ_ineqs = (uu___2095_25027.univ_ineqs);
            implicits = (uu___2095_25027.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25036 ->
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
          let uu____25053 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25053
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25060 =
      let uu____25061 = FStar_Syntax_Util.unmeta t  in
      uu____25061.FStar_Syntax_Syntax.n  in
    match uu____25060 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25065 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25108 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25108;
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
                       let uu____25203 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25203
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2150_25210 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2150_25210.deferred);
              univ_ineqs = (uu___2150_25210.univ_ineqs);
              implicits = (uu___2150_25210.implicits)
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
               let uu____25244 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25244
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
            let uu___2165_25271 = g  in
            let uu____25272 =
              let uu____25273 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25273  in
            {
              guard_f = uu____25272;
              deferred = (uu___2165_25271.deferred);
              univ_ineqs = (uu___2165_25271.univ_ineqs);
              implicits = (uu___2165_25271.implicits)
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
              let uu____25331 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25331 with
              | FStar_Pervasives_Native.Some
                  (uu____25356::(tm,uu____25358)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25422 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25440 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25440;
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
                      let uu___2187_25472 = trivial_guard  in
                      {
                        guard_f = (uu___2187_25472.guard_f);
                        deferred = (uu___2187_25472.deferred);
                        univ_ineqs = (uu___2187_25472.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25490  -> ());
    push = (fun uu____25492  -> ());
    pop = (fun uu____25495  -> ());
    snapshot =
      (fun uu____25498  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25517  -> fun uu____25518  -> ());
    encode_sig = (fun uu____25533  -> fun uu____25534  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25540 =
             let uu____25547 = FStar_Options.peek ()  in (e, g, uu____25547)
              in
           [uu____25540]);
    solve = (fun uu____25563  -> fun uu____25564  -> fun uu____25565  -> ());
    finish = (fun uu____25572  -> ());
    refresh = (fun uu____25574  -> ())
  } 