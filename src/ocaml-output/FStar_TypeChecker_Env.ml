open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding of Prims.bool 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____117 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____128 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____139 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____151 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____169 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____180 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____191 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding _0 -> true | uu____204 -> false
  
let (__proj__Eager_unfolding__item___0 : step -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding _0 -> _0 
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____225 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____236 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____248 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____269 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____296 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____323 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____347 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____358 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____369 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____380 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____391 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____402 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____413 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____424 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____435 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____446 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____457 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____468 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____479 -> false
  
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
      | (Eager_unfolding (true ),Eager_unfolding (true )) -> true
      | (Eager_unfolding (false ),Eager_unfolding (false )) -> true
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
      | uu____544 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only of Prims.bool 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____576 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____587 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only _0 -> true
    | uu____600 -> false
  
let (__proj__Eager_unfolding_only__item___0 : delta_level -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding_only _0 -> _0 
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____622 -> false
  
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
           (fun uu___0_12809  ->
              match uu___0_12809 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12812 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12812  in
                  let uu____12813 =
                    let uu____12814 = FStar_Syntax_Subst.compress y  in
                    uu____12814.FStar_Syntax_Syntax.n  in
                  (match uu____12813 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12818 =
                         let uu___345_12819 = y1  in
                         let uu____12820 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___345_12819.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___345_12819.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12820
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12818
                   | uu____12823 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___351_12837 = env  in
      let uu____12838 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___351_12837.solver);
        range = (uu___351_12837.range);
        curmodule = (uu___351_12837.curmodule);
        gamma = uu____12838;
        gamma_sig = (uu___351_12837.gamma_sig);
        gamma_cache = (uu___351_12837.gamma_cache);
        modules = (uu___351_12837.modules);
        expected_typ = (uu___351_12837.expected_typ);
        sigtab = (uu___351_12837.sigtab);
        attrtab = (uu___351_12837.attrtab);
        is_pattern = (uu___351_12837.is_pattern);
        instantiate_imp = (uu___351_12837.instantiate_imp);
        effects = (uu___351_12837.effects);
        generalize = (uu___351_12837.generalize);
        letrecs = (uu___351_12837.letrecs);
        top_level = (uu___351_12837.top_level);
        check_uvars = (uu___351_12837.check_uvars);
        use_eq = (uu___351_12837.use_eq);
        is_iface = (uu___351_12837.is_iface);
        admit = (uu___351_12837.admit);
        lax = (uu___351_12837.lax);
        lax_universes = (uu___351_12837.lax_universes);
        phase1 = (uu___351_12837.phase1);
        failhard = (uu___351_12837.failhard);
        nosynth = (uu___351_12837.nosynth);
        uvar_subtyping = (uu___351_12837.uvar_subtyping);
        tc_term = (uu___351_12837.tc_term);
        type_of = (uu___351_12837.type_of);
        universe_of = (uu___351_12837.universe_of);
        check_type_of = (uu___351_12837.check_type_of);
        use_bv_sorts = (uu___351_12837.use_bv_sorts);
        qtbl_name_and_index = (uu___351_12837.qtbl_name_and_index);
        normalized_eff_names = (uu___351_12837.normalized_eff_names);
        fv_delta_depths = (uu___351_12837.fv_delta_depths);
        proof_ns = (uu___351_12837.proof_ns);
        synth_hook = (uu___351_12837.synth_hook);
        splice = (uu___351_12837.splice);
        postprocess = (uu___351_12837.postprocess);
        is_native_tactic = (uu___351_12837.is_native_tactic);
        identifier_info = (uu___351_12837.identifier_info);
        tc_hooks = (uu___351_12837.tc_hooks);
        dsenv = (uu___351_12837.dsenv);
        nbe = (uu___351_12837.nbe);
        strict_args_tab = (uu___351_12837.strict_args_tab);
        erasable_types_tab = (uu___351_12837.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12846  -> fun uu____12847  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___358_12869 = env  in
      {
        solver = (uu___358_12869.solver);
        range = (uu___358_12869.range);
        curmodule = (uu___358_12869.curmodule);
        gamma = (uu___358_12869.gamma);
        gamma_sig = (uu___358_12869.gamma_sig);
        gamma_cache = (uu___358_12869.gamma_cache);
        modules = (uu___358_12869.modules);
        expected_typ = (uu___358_12869.expected_typ);
        sigtab = (uu___358_12869.sigtab);
        attrtab = (uu___358_12869.attrtab);
        is_pattern = (uu___358_12869.is_pattern);
        instantiate_imp = (uu___358_12869.instantiate_imp);
        effects = (uu___358_12869.effects);
        generalize = (uu___358_12869.generalize);
        letrecs = (uu___358_12869.letrecs);
        top_level = (uu___358_12869.top_level);
        check_uvars = (uu___358_12869.check_uvars);
        use_eq = (uu___358_12869.use_eq);
        is_iface = (uu___358_12869.is_iface);
        admit = (uu___358_12869.admit);
        lax = (uu___358_12869.lax);
        lax_universes = (uu___358_12869.lax_universes);
        phase1 = (uu___358_12869.phase1);
        failhard = (uu___358_12869.failhard);
        nosynth = (uu___358_12869.nosynth);
        uvar_subtyping = (uu___358_12869.uvar_subtyping);
        tc_term = (uu___358_12869.tc_term);
        type_of = (uu___358_12869.type_of);
        universe_of = (uu___358_12869.universe_of);
        check_type_of = (uu___358_12869.check_type_of);
        use_bv_sorts = (uu___358_12869.use_bv_sorts);
        qtbl_name_and_index = (uu___358_12869.qtbl_name_and_index);
        normalized_eff_names = (uu___358_12869.normalized_eff_names);
        fv_delta_depths = (uu___358_12869.fv_delta_depths);
        proof_ns = (uu___358_12869.proof_ns);
        synth_hook = (uu___358_12869.synth_hook);
        splice = (uu___358_12869.splice);
        postprocess = (uu___358_12869.postprocess);
        is_native_tactic = (uu___358_12869.is_native_tactic);
        identifier_info = (uu___358_12869.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___358_12869.dsenv);
        nbe = (uu___358_12869.nbe);
        strict_args_tab = (uu___358_12869.strict_args_tab);
        erasable_types_tab = (uu___358_12869.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___362_12881 = e  in
      let uu____12882 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___362_12881.solver);
        range = (uu___362_12881.range);
        curmodule = (uu___362_12881.curmodule);
        gamma = (uu___362_12881.gamma);
        gamma_sig = (uu___362_12881.gamma_sig);
        gamma_cache = (uu___362_12881.gamma_cache);
        modules = (uu___362_12881.modules);
        expected_typ = (uu___362_12881.expected_typ);
        sigtab = (uu___362_12881.sigtab);
        attrtab = (uu___362_12881.attrtab);
        is_pattern = (uu___362_12881.is_pattern);
        instantiate_imp = (uu___362_12881.instantiate_imp);
        effects = (uu___362_12881.effects);
        generalize = (uu___362_12881.generalize);
        letrecs = (uu___362_12881.letrecs);
        top_level = (uu___362_12881.top_level);
        check_uvars = (uu___362_12881.check_uvars);
        use_eq = (uu___362_12881.use_eq);
        is_iface = (uu___362_12881.is_iface);
        admit = (uu___362_12881.admit);
        lax = (uu___362_12881.lax);
        lax_universes = (uu___362_12881.lax_universes);
        phase1 = (uu___362_12881.phase1);
        failhard = (uu___362_12881.failhard);
        nosynth = (uu___362_12881.nosynth);
        uvar_subtyping = (uu___362_12881.uvar_subtyping);
        tc_term = (uu___362_12881.tc_term);
        type_of = (uu___362_12881.type_of);
        universe_of = (uu___362_12881.universe_of);
        check_type_of = (uu___362_12881.check_type_of);
        use_bv_sorts = (uu___362_12881.use_bv_sorts);
        qtbl_name_and_index = (uu___362_12881.qtbl_name_and_index);
        normalized_eff_names = (uu___362_12881.normalized_eff_names);
        fv_delta_depths = (uu___362_12881.fv_delta_depths);
        proof_ns = (uu___362_12881.proof_ns);
        synth_hook = (uu___362_12881.synth_hook);
        splice = (uu___362_12881.splice);
        postprocess = (uu___362_12881.postprocess);
        is_native_tactic = (uu___362_12881.is_native_tactic);
        identifier_info = (uu___362_12881.identifier_info);
        tc_hooks = (uu___362_12881.tc_hooks);
        dsenv = uu____12882;
        nbe = (uu___362_12881.nbe);
        strict_args_tab = (uu___362_12881.strict_args_tab);
        erasable_types_tab = (uu___362_12881.erasable_types_tab)
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
      | (NoDelta ,uu____12911) -> true
      | (Eager_unfolding_only
         uu____12913,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold
         uu____12916,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12918,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12921 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12935 . unit -> 'Auu____12935 FStar_Util.smap =
  fun uu____12942  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12948 . unit -> 'Auu____12948 FStar_Util.smap =
  fun uu____12955  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13093 = new_gamma_cache ()  in
                  let uu____13096 = new_sigtab ()  in
                  let uu____13099 = new_sigtab ()  in
                  let uu____13106 =
                    let uu____13121 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13121, FStar_Pervasives_Native.None)  in
                  let uu____13142 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13146 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13150 = FStar_Options.using_facts_from ()  in
                  let uu____13151 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13154 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13155 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13169 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13093;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13096;
                    attrtab = uu____13099;
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
                    qtbl_name_and_index = uu____13106;
                    normalized_eff_names = uu____13142;
                    fv_delta_depths = uu____13146;
                    proof_ns = uu____13150;
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
                    is_native_tactic = (fun uu____13236  -> false);
                    identifier_info = uu____13151;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13154;
                    nbe = nbe1;
                    strict_args_tab = uu____13155;
                    erasable_types_tab = uu____13169
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
  fun uu____13315  ->
    let uu____13316 = FStar_ST.op_Bang query_indices  in
    match uu____13316 with
    | [] -> failwith "Empty query indices!"
    | uu____13371 ->
        let uu____13381 =
          let uu____13391 =
            let uu____13399 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13399  in
          let uu____13453 = FStar_ST.op_Bang query_indices  in uu____13391 ::
            uu____13453
           in
        FStar_ST.op_Colon_Equals query_indices uu____13381
  
let (pop_query_indices : unit -> unit) =
  fun uu____13549  ->
    let uu____13550 = FStar_ST.op_Bang query_indices  in
    match uu____13550 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13677  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13714  ->
    match uu____13714 with
    | (l,n1) ->
        let uu____13724 = FStar_ST.op_Bang query_indices  in
        (match uu____13724 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13846 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13869  ->
    let uu____13870 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13870
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13938 =
       let uu____13941 = FStar_ST.op_Bang stack  in env :: uu____13941  in
     FStar_ST.op_Colon_Equals stack uu____13938);
    (let uu___431_13990 = env  in
     let uu____13991 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13994 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13997 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14004 =
       let uu____14019 =
         let uu____14023 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14023  in
       let uu____14055 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14019, uu____14055)  in
     let uu____14104 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14107 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14110 =
       let uu____14113 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14113  in
     let uu____14133 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14146 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___431_13990.solver);
       range = (uu___431_13990.range);
       curmodule = (uu___431_13990.curmodule);
       gamma = (uu___431_13990.gamma);
       gamma_sig = (uu___431_13990.gamma_sig);
       gamma_cache = uu____13991;
       modules = (uu___431_13990.modules);
       expected_typ = (uu___431_13990.expected_typ);
       sigtab = uu____13994;
       attrtab = uu____13997;
       is_pattern = (uu___431_13990.is_pattern);
       instantiate_imp = (uu___431_13990.instantiate_imp);
       effects = (uu___431_13990.effects);
       generalize = (uu___431_13990.generalize);
       letrecs = (uu___431_13990.letrecs);
       top_level = (uu___431_13990.top_level);
       check_uvars = (uu___431_13990.check_uvars);
       use_eq = (uu___431_13990.use_eq);
       is_iface = (uu___431_13990.is_iface);
       admit = (uu___431_13990.admit);
       lax = (uu___431_13990.lax);
       lax_universes = (uu___431_13990.lax_universes);
       phase1 = (uu___431_13990.phase1);
       failhard = (uu___431_13990.failhard);
       nosynth = (uu___431_13990.nosynth);
       uvar_subtyping = (uu___431_13990.uvar_subtyping);
       tc_term = (uu___431_13990.tc_term);
       type_of = (uu___431_13990.type_of);
       universe_of = (uu___431_13990.universe_of);
       check_type_of = (uu___431_13990.check_type_of);
       use_bv_sorts = (uu___431_13990.use_bv_sorts);
       qtbl_name_and_index = uu____14004;
       normalized_eff_names = uu____14104;
       fv_delta_depths = uu____14107;
       proof_ns = (uu___431_13990.proof_ns);
       synth_hook = (uu___431_13990.synth_hook);
       splice = (uu___431_13990.splice);
       postprocess = (uu___431_13990.postprocess);
       is_native_tactic = (uu___431_13990.is_native_tactic);
       identifier_info = uu____14110;
       tc_hooks = (uu___431_13990.tc_hooks);
       dsenv = (uu___431_13990.dsenv);
       nbe = (uu___431_13990.nbe);
       strict_args_tab = uu____14133;
       erasable_types_tab = uu____14146
     })
  
let (pop_stack : unit -> env) =
  fun uu____14156  ->
    let uu____14157 = FStar_ST.op_Bang stack  in
    match uu____14157 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14211 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14301  ->
           let uu____14302 = snapshot_stack env  in
           match uu____14302 with
           | (stack_depth,env1) ->
               let uu____14336 = snapshot_query_indices ()  in
               (match uu____14336 with
                | (query_indices_depth,()) ->
                    let uu____14369 = (env1.solver).snapshot msg  in
                    (match uu____14369 with
                     | (solver_depth,()) ->
                         let uu____14426 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14426 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___456_14493 = env1  in
                                 {
                                   solver = (uu___456_14493.solver);
                                   range = (uu___456_14493.range);
                                   curmodule = (uu___456_14493.curmodule);
                                   gamma = (uu___456_14493.gamma);
                                   gamma_sig = (uu___456_14493.gamma_sig);
                                   gamma_cache = (uu___456_14493.gamma_cache);
                                   modules = (uu___456_14493.modules);
                                   expected_typ =
                                     (uu___456_14493.expected_typ);
                                   sigtab = (uu___456_14493.sigtab);
                                   attrtab = (uu___456_14493.attrtab);
                                   is_pattern = (uu___456_14493.is_pattern);
                                   instantiate_imp =
                                     (uu___456_14493.instantiate_imp);
                                   effects = (uu___456_14493.effects);
                                   generalize = (uu___456_14493.generalize);
                                   letrecs = (uu___456_14493.letrecs);
                                   top_level = (uu___456_14493.top_level);
                                   check_uvars = (uu___456_14493.check_uvars);
                                   use_eq = (uu___456_14493.use_eq);
                                   is_iface = (uu___456_14493.is_iface);
                                   admit = (uu___456_14493.admit);
                                   lax = (uu___456_14493.lax);
                                   lax_universes =
                                     (uu___456_14493.lax_universes);
                                   phase1 = (uu___456_14493.phase1);
                                   failhard = (uu___456_14493.failhard);
                                   nosynth = (uu___456_14493.nosynth);
                                   uvar_subtyping =
                                     (uu___456_14493.uvar_subtyping);
                                   tc_term = (uu___456_14493.tc_term);
                                   type_of = (uu___456_14493.type_of);
                                   universe_of = (uu___456_14493.universe_of);
                                   check_type_of =
                                     (uu___456_14493.check_type_of);
                                   use_bv_sorts =
                                     (uu___456_14493.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___456_14493.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___456_14493.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___456_14493.fv_delta_depths);
                                   proof_ns = (uu___456_14493.proof_ns);
                                   synth_hook = (uu___456_14493.synth_hook);
                                   splice = (uu___456_14493.splice);
                                   postprocess = (uu___456_14493.postprocess);
                                   is_native_tactic =
                                     (uu___456_14493.is_native_tactic);
                                   identifier_info =
                                     (uu___456_14493.identifier_info);
                                   tc_hooks = (uu___456_14493.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___456_14493.nbe);
                                   strict_args_tab =
                                     (uu___456_14493.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___456_14493.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14527  ->
             let uu____14528 =
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
             match uu____14528 with
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
                             ((let uu____14708 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14708
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14724 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14724
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14756,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14798 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14828  ->
                  match uu____14828 with
                  | (m,uu____14836) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14798 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___501_14851 = env  in
               {
                 solver = (uu___501_14851.solver);
                 range = (uu___501_14851.range);
                 curmodule = (uu___501_14851.curmodule);
                 gamma = (uu___501_14851.gamma);
                 gamma_sig = (uu___501_14851.gamma_sig);
                 gamma_cache = (uu___501_14851.gamma_cache);
                 modules = (uu___501_14851.modules);
                 expected_typ = (uu___501_14851.expected_typ);
                 sigtab = (uu___501_14851.sigtab);
                 attrtab = (uu___501_14851.attrtab);
                 is_pattern = (uu___501_14851.is_pattern);
                 instantiate_imp = (uu___501_14851.instantiate_imp);
                 effects = (uu___501_14851.effects);
                 generalize = (uu___501_14851.generalize);
                 letrecs = (uu___501_14851.letrecs);
                 top_level = (uu___501_14851.top_level);
                 check_uvars = (uu___501_14851.check_uvars);
                 use_eq = (uu___501_14851.use_eq);
                 is_iface = (uu___501_14851.is_iface);
                 admit = (uu___501_14851.admit);
                 lax = (uu___501_14851.lax);
                 lax_universes = (uu___501_14851.lax_universes);
                 phase1 = (uu___501_14851.phase1);
                 failhard = (uu___501_14851.failhard);
                 nosynth = (uu___501_14851.nosynth);
                 uvar_subtyping = (uu___501_14851.uvar_subtyping);
                 tc_term = (uu___501_14851.tc_term);
                 type_of = (uu___501_14851.type_of);
                 universe_of = (uu___501_14851.universe_of);
                 check_type_of = (uu___501_14851.check_type_of);
                 use_bv_sorts = (uu___501_14851.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___501_14851.normalized_eff_names);
                 fv_delta_depths = (uu___501_14851.fv_delta_depths);
                 proof_ns = (uu___501_14851.proof_ns);
                 synth_hook = (uu___501_14851.synth_hook);
                 splice = (uu___501_14851.splice);
                 postprocess = (uu___501_14851.postprocess);
                 is_native_tactic = (uu___501_14851.is_native_tactic);
                 identifier_info = (uu___501_14851.identifier_info);
                 tc_hooks = (uu___501_14851.tc_hooks);
                 dsenv = (uu___501_14851.dsenv);
                 nbe = (uu___501_14851.nbe);
                 strict_args_tab = (uu___501_14851.strict_args_tab);
                 erasable_types_tab = (uu___501_14851.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14868,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___510_14884 = env  in
               {
                 solver = (uu___510_14884.solver);
                 range = (uu___510_14884.range);
                 curmodule = (uu___510_14884.curmodule);
                 gamma = (uu___510_14884.gamma);
                 gamma_sig = (uu___510_14884.gamma_sig);
                 gamma_cache = (uu___510_14884.gamma_cache);
                 modules = (uu___510_14884.modules);
                 expected_typ = (uu___510_14884.expected_typ);
                 sigtab = (uu___510_14884.sigtab);
                 attrtab = (uu___510_14884.attrtab);
                 is_pattern = (uu___510_14884.is_pattern);
                 instantiate_imp = (uu___510_14884.instantiate_imp);
                 effects = (uu___510_14884.effects);
                 generalize = (uu___510_14884.generalize);
                 letrecs = (uu___510_14884.letrecs);
                 top_level = (uu___510_14884.top_level);
                 check_uvars = (uu___510_14884.check_uvars);
                 use_eq = (uu___510_14884.use_eq);
                 is_iface = (uu___510_14884.is_iface);
                 admit = (uu___510_14884.admit);
                 lax = (uu___510_14884.lax);
                 lax_universes = (uu___510_14884.lax_universes);
                 phase1 = (uu___510_14884.phase1);
                 failhard = (uu___510_14884.failhard);
                 nosynth = (uu___510_14884.nosynth);
                 uvar_subtyping = (uu___510_14884.uvar_subtyping);
                 tc_term = (uu___510_14884.tc_term);
                 type_of = (uu___510_14884.type_of);
                 universe_of = (uu___510_14884.universe_of);
                 check_type_of = (uu___510_14884.check_type_of);
                 use_bv_sorts = (uu___510_14884.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___510_14884.normalized_eff_names);
                 fv_delta_depths = (uu___510_14884.fv_delta_depths);
                 proof_ns = (uu___510_14884.proof_ns);
                 synth_hook = (uu___510_14884.synth_hook);
                 splice = (uu___510_14884.splice);
                 postprocess = (uu___510_14884.postprocess);
                 is_native_tactic = (uu___510_14884.is_native_tactic);
                 identifier_info = (uu___510_14884.identifier_info);
                 tc_hooks = (uu___510_14884.tc_hooks);
                 dsenv = (uu___510_14884.dsenv);
                 nbe = (uu___510_14884.nbe);
                 strict_args_tab = (uu___510_14884.strict_args_tab);
                 erasable_types_tab = (uu___510_14884.erasable_types_tab)
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
        (let uu___517_14927 = e  in
         {
           solver = (uu___517_14927.solver);
           range = r;
           curmodule = (uu___517_14927.curmodule);
           gamma = (uu___517_14927.gamma);
           gamma_sig = (uu___517_14927.gamma_sig);
           gamma_cache = (uu___517_14927.gamma_cache);
           modules = (uu___517_14927.modules);
           expected_typ = (uu___517_14927.expected_typ);
           sigtab = (uu___517_14927.sigtab);
           attrtab = (uu___517_14927.attrtab);
           is_pattern = (uu___517_14927.is_pattern);
           instantiate_imp = (uu___517_14927.instantiate_imp);
           effects = (uu___517_14927.effects);
           generalize = (uu___517_14927.generalize);
           letrecs = (uu___517_14927.letrecs);
           top_level = (uu___517_14927.top_level);
           check_uvars = (uu___517_14927.check_uvars);
           use_eq = (uu___517_14927.use_eq);
           is_iface = (uu___517_14927.is_iface);
           admit = (uu___517_14927.admit);
           lax = (uu___517_14927.lax);
           lax_universes = (uu___517_14927.lax_universes);
           phase1 = (uu___517_14927.phase1);
           failhard = (uu___517_14927.failhard);
           nosynth = (uu___517_14927.nosynth);
           uvar_subtyping = (uu___517_14927.uvar_subtyping);
           tc_term = (uu___517_14927.tc_term);
           type_of = (uu___517_14927.type_of);
           universe_of = (uu___517_14927.universe_of);
           check_type_of = (uu___517_14927.check_type_of);
           use_bv_sorts = (uu___517_14927.use_bv_sorts);
           qtbl_name_and_index = (uu___517_14927.qtbl_name_and_index);
           normalized_eff_names = (uu___517_14927.normalized_eff_names);
           fv_delta_depths = (uu___517_14927.fv_delta_depths);
           proof_ns = (uu___517_14927.proof_ns);
           synth_hook = (uu___517_14927.synth_hook);
           splice = (uu___517_14927.splice);
           postprocess = (uu___517_14927.postprocess);
           is_native_tactic = (uu___517_14927.is_native_tactic);
           identifier_info = (uu___517_14927.identifier_info);
           tc_hooks = (uu___517_14927.tc_hooks);
           dsenv = (uu___517_14927.dsenv);
           nbe = (uu___517_14927.nbe);
           strict_args_tab = (uu___517_14927.strict_args_tab);
           erasable_types_tab = (uu___517_14927.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14947 =
        let uu____14948 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14948 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14947
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15003 =
          let uu____15004 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15004 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15003
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15059 =
          let uu____15060 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15060 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15059
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15115 =
        let uu____15116 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15116 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15115
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___534_15180 = env  in
      {
        solver = (uu___534_15180.solver);
        range = (uu___534_15180.range);
        curmodule = lid;
        gamma = (uu___534_15180.gamma);
        gamma_sig = (uu___534_15180.gamma_sig);
        gamma_cache = (uu___534_15180.gamma_cache);
        modules = (uu___534_15180.modules);
        expected_typ = (uu___534_15180.expected_typ);
        sigtab = (uu___534_15180.sigtab);
        attrtab = (uu___534_15180.attrtab);
        is_pattern = (uu___534_15180.is_pattern);
        instantiate_imp = (uu___534_15180.instantiate_imp);
        effects = (uu___534_15180.effects);
        generalize = (uu___534_15180.generalize);
        letrecs = (uu___534_15180.letrecs);
        top_level = (uu___534_15180.top_level);
        check_uvars = (uu___534_15180.check_uvars);
        use_eq = (uu___534_15180.use_eq);
        is_iface = (uu___534_15180.is_iface);
        admit = (uu___534_15180.admit);
        lax = (uu___534_15180.lax);
        lax_universes = (uu___534_15180.lax_universes);
        phase1 = (uu___534_15180.phase1);
        failhard = (uu___534_15180.failhard);
        nosynth = (uu___534_15180.nosynth);
        uvar_subtyping = (uu___534_15180.uvar_subtyping);
        tc_term = (uu___534_15180.tc_term);
        type_of = (uu___534_15180.type_of);
        universe_of = (uu___534_15180.universe_of);
        check_type_of = (uu___534_15180.check_type_of);
        use_bv_sorts = (uu___534_15180.use_bv_sorts);
        qtbl_name_and_index = (uu___534_15180.qtbl_name_and_index);
        normalized_eff_names = (uu___534_15180.normalized_eff_names);
        fv_delta_depths = (uu___534_15180.fv_delta_depths);
        proof_ns = (uu___534_15180.proof_ns);
        synth_hook = (uu___534_15180.synth_hook);
        splice = (uu___534_15180.splice);
        postprocess = (uu___534_15180.postprocess);
        is_native_tactic = (uu___534_15180.is_native_tactic);
        identifier_info = (uu___534_15180.identifier_info);
        tc_hooks = (uu___534_15180.tc_hooks);
        dsenv = (uu___534_15180.dsenv);
        nbe = (uu___534_15180.nbe);
        strict_args_tab = (uu___534_15180.strict_args_tab);
        erasable_types_tab = (uu___534_15180.erasable_types_tab)
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
      let uu____15211 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15211
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15224 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15224)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15239 =
      let uu____15241 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15241  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15239)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15250  ->
    let uu____15251 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15251
  
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
      | ((formals,t),uu____15351) ->
          let vs = mk_univ_subst formals us  in
          let uu____15375 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15375)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15392  ->
    match uu___1_15392 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15418  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15438 = inst_tscheme t  in
      match uu____15438 with
      | (us,t1) ->
          let uu____15449 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15449)
  
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
          let uu____15474 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15476 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15474 uu____15476
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
        fun uu____15503  ->
          match uu____15503 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15517 =
                    let uu____15519 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15523 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15527 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15529 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15519 uu____15523 uu____15527 uu____15529
                     in
                  failwith uu____15517)
               else ();
               (let uu____15534 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15534))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15552 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15563 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15574 -> false
  
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
             | ([],uu____15622) -> Maybe
             | (uu____15629,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15649 -> No  in
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
          let uu____15743 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15743 with
          | FStar_Pervasives_Native.None  ->
              let uu____15766 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15810  ->
                     match uu___2_15810 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15849 = FStar_Ident.lid_equals lid l  in
                         if uu____15849
                         then
                           let uu____15872 =
                             let uu____15891 =
                               let uu____15906 = inst_tscheme t  in
                               FStar_Util.Inl uu____15906  in
                             let uu____15921 = FStar_Ident.range_of_lid l  in
                             (uu____15891, uu____15921)  in
                           FStar_Pervasives_Native.Some uu____15872
                         else FStar_Pervasives_Native.None
                     | uu____15974 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15766
                (fun uu____16012  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16021  ->
                        match uu___3_16021 with
                        | (uu____16024,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16026);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16027;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16028;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16029;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16030;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16050 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16050
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
                                  uu____16102 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16109 -> cache t  in
                            let uu____16110 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16110 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16116 =
                                   let uu____16117 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16117)
                                    in
                                 maybe_cache uu____16116)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16188 = find_in_sigtab env lid  in
         match uu____16188 with
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
      let uu____16269 = lookup_qname env lid  in
      match uu____16269 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16290,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16404 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16404 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16449 =
          let uu____16452 = lookup_attr env1 attr  in se1 :: uu____16452  in
        FStar_Util.smap_add (attrtab env1) attr uu____16449  in
      FStar_List.iter
        (fun attr  ->
           let uu____16462 =
             let uu____16463 = FStar_Syntax_Subst.compress attr  in
             uu____16463.FStar_Syntax_Syntax.n  in
           match uu____16462 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16467 =
                 let uu____16469 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16469.FStar_Ident.str  in
               add_one1 env se uu____16467
           | uu____16470 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16493) ->
          add_sigelts env ses
      | uu____16502 ->
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
        (fun uu___4_16540  ->
           match uu___4_16540 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16558 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16620,lb::[]),uu____16622) ->
            let uu____16631 =
              let uu____16640 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16649 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16640, uu____16649)  in
            FStar_Pervasives_Native.Some uu____16631
        | FStar_Syntax_Syntax.Sig_let ((uu____16662,lbs),uu____16664) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16696 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16709 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16709
                     then
                       let uu____16722 =
                         let uu____16731 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16740 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16731, uu____16740)  in
                       FStar_Pervasives_Native.Some uu____16722
                     else FStar_Pervasives_Native.None)
        | uu____16763 -> FStar_Pervasives_Native.None
  
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
                    let uu____16855 =
                      let uu____16857 =
                        let uu____16859 =
                          let uu____16861 =
                            let uu____16863 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16869 =
                              let uu____16871 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16871  in
                            Prims.op_Hat uu____16863 uu____16869  in
                          Prims.op_Hat ", expected " uu____16861  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16859
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16857
                       in
                    failwith uu____16855
                  else ());
             (let uu____16878 =
                let uu____16887 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16887, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16878))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16907,uu____16908) ->
            let uu____16913 =
              let uu____16922 =
                let uu____16927 =
                  let uu____16928 =
                    let uu____16931 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16931  in
                  (us, uu____16928)  in
                inst_ts us_opt uu____16927  in
              (uu____16922, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16913
        | uu____16950 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17039 =
          match uu____17039 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17135,uvs,t,uu____17138,uu____17139,uu____17140);
                      FStar_Syntax_Syntax.sigrng = uu____17141;
                      FStar_Syntax_Syntax.sigquals = uu____17142;
                      FStar_Syntax_Syntax.sigmeta = uu____17143;
                      FStar_Syntax_Syntax.sigattrs = uu____17144;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17167 =
                     let uu____17176 = inst_tscheme1 (uvs, t)  in
                     (uu____17176, rng)  in
                   FStar_Pervasives_Native.Some uu____17167
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17200;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17202;
                      FStar_Syntax_Syntax.sigattrs = uu____17203;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17220 =
                     let uu____17222 = in_cur_mod env l  in uu____17222 = Yes
                      in
                   if uu____17220
                   then
                     let uu____17234 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17234
                      then
                        let uu____17250 =
                          let uu____17259 = inst_tscheme1 (uvs, t)  in
                          (uu____17259, rng)  in
                        FStar_Pervasives_Native.Some uu____17250
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17292 =
                        let uu____17301 = inst_tscheme1 (uvs, t)  in
                        (uu____17301, rng)  in
                      FStar_Pervasives_Native.Some uu____17292)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17326,uu____17327);
                      FStar_Syntax_Syntax.sigrng = uu____17328;
                      FStar_Syntax_Syntax.sigquals = uu____17329;
                      FStar_Syntax_Syntax.sigmeta = uu____17330;
                      FStar_Syntax_Syntax.sigattrs = uu____17331;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17372 =
                          let uu____17381 = inst_tscheme1 (uvs, k)  in
                          (uu____17381, rng)  in
                        FStar_Pervasives_Native.Some uu____17372
                    | uu____17402 ->
                        let uu____17403 =
                          let uu____17412 =
                            let uu____17417 =
                              let uu____17418 =
                                let uu____17421 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17421
                                 in
                              (uvs, uu____17418)  in
                            inst_tscheme1 uu____17417  in
                          (uu____17412, rng)  in
                        FStar_Pervasives_Native.Some uu____17403)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17444,uu____17445);
                      FStar_Syntax_Syntax.sigrng = uu____17446;
                      FStar_Syntax_Syntax.sigquals = uu____17447;
                      FStar_Syntax_Syntax.sigmeta = uu____17448;
                      FStar_Syntax_Syntax.sigattrs = uu____17449;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17491 =
                          let uu____17500 = inst_tscheme_with (uvs, k) us  in
                          (uu____17500, rng)  in
                        FStar_Pervasives_Native.Some uu____17491
                    | uu____17521 ->
                        let uu____17522 =
                          let uu____17531 =
                            let uu____17536 =
                              let uu____17537 =
                                let uu____17540 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17540
                                 in
                              (uvs, uu____17537)  in
                            inst_tscheme_with uu____17536 us  in
                          (uu____17531, rng)  in
                        FStar_Pervasives_Native.Some uu____17522)
               | FStar_Util.Inr se ->
                   let uu____17576 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17597;
                          FStar_Syntax_Syntax.sigrng = uu____17598;
                          FStar_Syntax_Syntax.sigquals = uu____17599;
                          FStar_Syntax_Syntax.sigmeta = uu____17600;
                          FStar_Syntax_Syntax.sigattrs = uu____17601;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17616 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17576
                     (FStar_Util.map_option
                        (fun uu____17664  ->
                           match uu____17664 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17695 =
          let uu____17706 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17706 mapper  in
        match uu____17695 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17780 =
              let uu____17791 =
                let uu____17798 =
                  let uu___865_17801 = t  in
                  let uu____17802 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___865_17801.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17802;
                    FStar_Syntax_Syntax.vars =
                      (uu___865_17801.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17798)  in
              (uu____17791, r)  in
            FStar_Pervasives_Native.Some uu____17780
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17851 = lookup_qname env l  in
      match uu____17851 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17872 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17926 = try_lookup_bv env bv  in
      match uu____17926 with
      | FStar_Pervasives_Native.None  ->
          let uu____17941 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17941 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17957 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17958 =
            let uu____17959 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17959  in
          (uu____17957, uu____17958)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17981 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17981 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18047 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18047  in
          let uu____18048 =
            let uu____18057 =
              let uu____18062 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18062)  in
            (uu____18057, r1)  in
          FStar_Pervasives_Native.Some uu____18048
  
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
        let uu____18097 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18097 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18130,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18155 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18155  in
            let uu____18156 =
              let uu____18161 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18161, r1)  in
            FStar_Pervasives_Native.Some uu____18156
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18185 = try_lookup_lid env l  in
      match uu____18185 with
      | FStar_Pervasives_Native.None  ->
          let uu____18212 = name_not_found l  in
          let uu____18218 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18212 uu____18218
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18261  ->
              match uu___5_18261 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18265 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18286 = lookup_qname env lid  in
      match uu____18286 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18295,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18298;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18300;
              FStar_Syntax_Syntax.sigattrs = uu____18301;_},FStar_Pervasives_Native.None
            ),uu____18302)
          ->
          let uu____18351 =
            let uu____18358 =
              let uu____18359 =
                let uu____18362 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18362 t  in
              (uvs, uu____18359)  in
            (uu____18358, q)  in
          FStar_Pervasives_Native.Some uu____18351
      | uu____18375 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18397 = lookup_qname env lid  in
      match uu____18397 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18402,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18405;
              FStar_Syntax_Syntax.sigquals = uu____18406;
              FStar_Syntax_Syntax.sigmeta = uu____18407;
              FStar_Syntax_Syntax.sigattrs = uu____18408;_},FStar_Pervasives_Native.None
            ),uu____18409)
          ->
          let uu____18458 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18458 (uvs, t)
      | uu____18463 ->
          let uu____18464 = name_not_found lid  in
          let uu____18470 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18464 uu____18470
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18490 = lookup_qname env lid  in
      match uu____18490 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18495,uvs,t,uu____18498,uu____18499,uu____18500);
              FStar_Syntax_Syntax.sigrng = uu____18501;
              FStar_Syntax_Syntax.sigquals = uu____18502;
              FStar_Syntax_Syntax.sigmeta = uu____18503;
              FStar_Syntax_Syntax.sigattrs = uu____18504;_},FStar_Pervasives_Native.None
            ),uu____18505)
          ->
          let uu____18560 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18560 (uvs, t)
      | uu____18565 ->
          let uu____18566 = name_not_found lid  in
          let uu____18572 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18566 uu____18572
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18595 = lookup_qname env lid  in
      match uu____18595 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18603,uu____18604,uu____18605,uu____18606,uu____18607,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18609;
              FStar_Syntax_Syntax.sigquals = uu____18610;
              FStar_Syntax_Syntax.sigmeta = uu____18611;
              FStar_Syntax_Syntax.sigattrs = uu____18612;_},uu____18613),uu____18614)
          -> (true, dcs)
      | uu____18677 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18693 = lookup_qname env lid  in
      match uu____18693 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18694,uu____18695,uu____18696,l,uu____18698,uu____18699);
              FStar_Syntax_Syntax.sigrng = uu____18700;
              FStar_Syntax_Syntax.sigquals = uu____18701;
              FStar_Syntax_Syntax.sigmeta = uu____18702;
              FStar_Syntax_Syntax.sigattrs = uu____18703;_},uu____18704),uu____18705)
          -> l
      | uu____18762 ->
          let uu____18763 =
            let uu____18765 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18765  in
          failwith uu____18763
  
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
          let visible quals attrs =
            (FStar_All.pipe_right delta_levels
               (FStar_Util.for_some
                  (fun dl  ->
                     FStar_All.pipe_right quals
                       (FStar_Util.for_some (visible_at dl)))))
              ||
              (FStar_All.pipe_right delta_levels
                 (FStar_Util.for_some
                    (fun uu___6_18837  ->
                       match uu___6_18837 with
                       | Eager_unfolding_only (true ) ->
                           FStar_All.pipe_right attrs
                             (FStar_Util.for_some
                                (fun at  ->
                                   FStar_Syntax_Util.is_fvar
                                     FStar_Parser_Const.unfold_for_smt_attr
                                     at))
                       | uu____18845 -> false)))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18858)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18915) when
                   (visible se.FStar_Syntax_Syntax.sigquals
                      se.FStar_Syntax_Syntax.sigattrs)
                     && ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18939 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18939
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18974 -> FStar_Pervasives_Native.None)
          | uu____18983 -> FStar_Pervasives_Native.None
  
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
        let uu____19045 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19045
  
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
        let uu____19078 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19078
  
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
             (FStar_Util.Inl uu____19130,uu____19131) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19180),uu____19181) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19230 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19248 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19258 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19275 ->
                  let uu____19282 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19282
              | FStar_Syntax_Syntax.Sig_let ((uu____19283,lbs),uu____19285)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19301 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19301
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19308 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19316 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19317 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19324 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19325 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19326 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19327 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19340 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19358 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19358
           (fun d_opt  ->
              let uu____19371 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19371
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19381 =
                   let uu____19384 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19384  in
                 match uu____19381 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19385 =
                       let uu____19387 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19387
                        in
                     failwith uu____19385
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19392 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19392
                       then
                         let uu____19395 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19397 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19399 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19395 uu____19397 uu____19399
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
        (FStar_Util.Inr (se,uu____19424),uu____19425) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19474 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19496),uu____19497) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19546 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19568 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19568
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19601 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19601 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19623 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19632 =
                        let uu____19633 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19633.FStar_Syntax_Syntax.n  in
                      match uu____19632 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19638 -> false))
               in
            (true, uu____19623)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19661 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19661
  
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
          let uu____19733 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19733.FStar_Ident.str  in
        let uu____19734 = FStar_Util.smap_try_find tab s  in
        match uu____19734 with
        | FStar_Pervasives_Native.None  ->
            let uu____19737 = f ()  in
            (match uu____19737 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____19775 =
        let uu____19776 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____19776 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19810 =
        let uu____19811 = FStar_Syntax_Util.unrefine t  in
        uu____19811.FStar_Syntax_Syntax.n  in
      match uu____19810 with
      | FStar_Syntax_Syntax.Tm_type uu____19815 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____19819) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____19845) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____19850,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____19872 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____19905 =
        let attrs =
          let uu____19911 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____19911  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____19951 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____19951)
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
      let uu____19996 = lookup_qname env ftv  in
      match uu____19996 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20000) ->
          let uu____20045 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20045 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20066,t),r) ->
               let uu____20081 =
                 let uu____20082 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20082 t  in
               FStar_Pervasives_Native.Some uu____20081)
      | uu____20083 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20095 = try_lookup_effect_lid env ftv  in
      match uu____20095 with
      | FStar_Pervasives_Native.None  ->
          let uu____20098 = name_not_found ftv  in
          let uu____20104 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20098 uu____20104
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
        let uu____20128 = lookup_qname env lid0  in
        match uu____20128 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20139);
                FStar_Syntax_Syntax.sigrng = uu____20140;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20142;
                FStar_Syntax_Syntax.sigattrs = uu____20143;_},FStar_Pervasives_Native.None
              ),uu____20144)
            ->
            let lid1 =
              let uu____20198 =
                let uu____20199 = FStar_Ident.range_of_lid lid  in
                let uu____20200 =
                  let uu____20201 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20201  in
                FStar_Range.set_use_range uu____20199 uu____20200  in
              FStar_Ident.set_lid_range lid uu____20198  in
            let uu____20202 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___7_20208  ->
                      match uu___7_20208 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20211 -> false))
               in
            if uu____20202
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20230 =
                      let uu____20232 =
                        let uu____20234 = get_range env  in
                        FStar_Range.string_of_range uu____20234  in
                      let uu____20235 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20237 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20232 uu____20235 uu____20237
                       in
                    failwith uu____20230)
                  in
               match (binders, univs1) with
               | ([],uu____20258) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20284,uu____20285::uu____20286::uu____20287) ->
                   let uu____20308 =
                     let uu____20310 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20312 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20310 uu____20312
                      in
                   failwith uu____20308
               | uu____20323 ->
                   let uu____20338 =
                     let uu____20343 =
                       let uu____20344 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20344)  in
                     inst_tscheme_with uu____20343 insts  in
                   (match uu____20338 with
                    | (uu____20357,t) ->
                        let t1 =
                          let uu____20360 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20360 t  in
                        let uu____20361 =
                          let uu____20362 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20362.FStar_Syntax_Syntax.n  in
                        (match uu____20361 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20397 -> failwith "Impossible")))
        | uu____20405 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20429 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20429 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20442,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20449 = find1 l2  in
            (match uu____20449 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20456 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20456 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20460 = find1 l  in
            (match uu____20460 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20465 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20465
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20480 = lookup_qname env l1  in
      match uu____20480 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20483;
              FStar_Syntax_Syntax.sigrng = uu____20484;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20486;
              FStar_Syntax_Syntax.sigattrs = uu____20487;_},uu____20488),uu____20489)
          -> q
      | uu____20540 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20564 =
          let uu____20565 =
            let uu____20567 = FStar_Util.string_of_int i  in
            let uu____20569 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20567 uu____20569
             in
          failwith uu____20565  in
        let uu____20572 = lookup_datacon env lid  in
        match uu____20572 with
        | (uu____20577,t) ->
            let uu____20579 =
              let uu____20580 = FStar_Syntax_Subst.compress t  in
              uu____20580.FStar_Syntax_Syntax.n  in
            (match uu____20579 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20584) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20628 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20628
                      FStar_Pervasives_Native.fst)
             | uu____20639 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20653 = lookup_qname env l  in
      match uu____20653 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20655,uu____20656,uu____20657);
              FStar_Syntax_Syntax.sigrng = uu____20658;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20660;
              FStar_Syntax_Syntax.sigattrs = uu____20661;_},uu____20662),uu____20663)
          ->
          FStar_Util.for_some
            (fun uu___8_20716  ->
               match uu___8_20716 with
               | FStar_Syntax_Syntax.Projector uu____20718 -> true
               | uu____20724 -> false) quals
      | uu____20726 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20740 = lookup_qname env lid  in
      match uu____20740 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20742,uu____20743,uu____20744,uu____20745,uu____20746,uu____20747);
              FStar_Syntax_Syntax.sigrng = uu____20748;
              FStar_Syntax_Syntax.sigquals = uu____20749;
              FStar_Syntax_Syntax.sigmeta = uu____20750;
              FStar_Syntax_Syntax.sigattrs = uu____20751;_},uu____20752),uu____20753)
          -> true
      | uu____20811 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20825 = lookup_qname env lid  in
      match uu____20825 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20827,uu____20828,uu____20829,uu____20830,uu____20831,uu____20832);
              FStar_Syntax_Syntax.sigrng = uu____20833;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20835;
              FStar_Syntax_Syntax.sigattrs = uu____20836;_},uu____20837),uu____20838)
          ->
          FStar_Util.for_some
            (fun uu___9_20899  ->
               match uu___9_20899 with
               | FStar_Syntax_Syntax.RecordType uu____20901 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20911 -> true
               | uu____20921 -> false) quals
      | uu____20923 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20933,uu____20934);
            FStar_Syntax_Syntax.sigrng = uu____20935;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20937;
            FStar_Syntax_Syntax.sigattrs = uu____20938;_},uu____20939),uu____20940)
        ->
        FStar_Util.for_some
          (fun uu___10_20997  ->
             match uu___10_20997 with
             | FStar_Syntax_Syntax.Action uu____20999 -> true
             | uu____21001 -> false) quals
    | uu____21003 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21017 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21017
  
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
      let uu____21034 =
        let uu____21035 = FStar_Syntax_Util.un_uinst head1  in
        uu____21035.FStar_Syntax_Syntax.n  in
      match uu____21034 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21041 ->
               true
           | uu____21044 -> false)
      | uu____21046 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21060 = lookup_qname env l  in
      match uu____21060 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21063),uu____21064) ->
          FStar_Util.for_some
            (fun uu___11_21112  ->
               match uu___11_21112 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21115 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21117 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21193 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21211) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21229 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21237 ->
                 FStar_Pervasives_Native.Some true
             | uu____21256 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21259 =
        let uu____21263 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21263 mapper  in
      match uu____21259 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21323 = lookup_qname env lid  in
      match uu____21323 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21327,uu____21328,tps,uu____21330,uu____21331,uu____21332);
              FStar_Syntax_Syntax.sigrng = uu____21333;
              FStar_Syntax_Syntax.sigquals = uu____21334;
              FStar_Syntax_Syntax.sigmeta = uu____21335;
              FStar_Syntax_Syntax.sigattrs = uu____21336;_},uu____21337),uu____21338)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21404 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21450  ->
              match uu____21450 with
              | (d,uu____21459) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21475 = effect_decl_opt env l  in
      match uu____21475 with
      | FStar_Pervasives_Native.None  ->
          let uu____21490 = name_not_found l  in
          let uu____21496 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21490 uu____21496
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21519  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21538  ->
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
        let uu____21570 = FStar_Ident.lid_equals l1 l2  in
        if uu____21570
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21581 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21581
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21592 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21645  ->
                        match uu____21645 with
                        | (m1,m2,uu____21659,uu____21660,uu____21661) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21592 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21678 =
                    let uu____21684 =
                      let uu____21686 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21688 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21686
                        uu____21688
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21684)
                     in
                  FStar_Errors.raise_error uu____21678 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21698,uu____21699,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21733 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21733
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
  'Auu____21753 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21753) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21782 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21808  ->
                match uu____21808 with
                | (d,uu____21815) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21782 with
      | FStar_Pervasives_Native.None  ->
          let uu____21826 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21826
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21841 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21841 with
           | (uu____21852,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21870)::(wp,uu____21872)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21928 -> failwith "Impossible"))
  
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
        | uu____21993 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22006 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22006 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22023 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22023 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22048 =
                     let uu____22054 =
                       let uu____22056 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22064 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22075 =
                         let uu____22077 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22077  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22056 uu____22064 uu____22075
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22054)
                      in
                   FStar_Errors.raise_error uu____22048
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22085 =
                     let uu____22096 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22096 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22133  ->
                        fun uu____22134  ->
                          match (uu____22133, uu____22134) with
                          | ((x,uu____22164),(t,uu____22166)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22085
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22197 =
                     let uu___1596_22198 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1596_22198.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1596_22198.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1596_22198.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1596_22198.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22197
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22210 .
    'Auu____22210 ->
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
          let uu____22240 = effect_decl_opt env effect_name  in
          match uu____22240 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22283 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22306 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22345 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22345
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22350 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22350
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____22361 =
                     let uu____22364 = get_range env  in
                     let uu____22365 =
                       let uu____22372 =
                         let uu____22373 =
                           let uu____22390 =
                             let uu____22401 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22401; wp]  in
                           (repr, uu____22390)  in
                         FStar_Syntax_Syntax.Tm_app uu____22373  in
                       FStar_Syntax_Syntax.mk uu____22372  in
                     uu____22365 FStar_Pervasives_Native.None uu____22364  in
                   FStar_Pervasives_Native.Some uu____22361)
  
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
      | uu____22545 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22560 =
        let uu____22561 = FStar_Syntax_Subst.compress t  in
        uu____22561.FStar_Syntax_Syntax.n  in
      match uu____22560 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22565,c) ->
          is_reifiable_comp env c
      | uu____22587 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22607 =
           let uu____22609 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22609  in
         if uu____22607
         then
           let uu____22612 =
             let uu____22618 =
               let uu____22620 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22620
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22618)  in
           let uu____22624 = get_range env  in
           FStar_Errors.raise_error uu____22612 uu____22624
         else ());
        (let uu____22627 = effect_repr_aux true env c u_c  in
         match uu____22627 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1661_22663 = env  in
        {
          solver = (uu___1661_22663.solver);
          range = (uu___1661_22663.range);
          curmodule = (uu___1661_22663.curmodule);
          gamma = (uu___1661_22663.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1661_22663.gamma_cache);
          modules = (uu___1661_22663.modules);
          expected_typ = (uu___1661_22663.expected_typ);
          sigtab = (uu___1661_22663.sigtab);
          attrtab = (uu___1661_22663.attrtab);
          is_pattern = (uu___1661_22663.is_pattern);
          instantiate_imp = (uu___1661_22663.instantiate_imp);
          effects = (uu___1661_22663.effects);
          generalize = (uu___1661_22663.generalize);
          letrecs = (uu___1661_22663.letrecs);
          top_level = (uu___1661_22663.top_level);
          check_uvars = (uu___1661_22663.check_uvars);
          use_eq = (uu___1661_22663.use_eq);
          is_iface = (uu___1661_22663.is_iface);
          admit = (uu___1661_22663.admit);
          lax = (uu___1661_22663.lax);
          lax_universes = (uu___1661_22663.lax_universes);
          phase1 = (uu___1661_22663.phase1);
          failhard = (uu___1661_22663.failhard);
          nosynth = (uu___1661_22663.nosynth);
          uvar_subtyping = (uu___1661_22663.uvar_subtyping);
          tc_term = (uu___1661_22663.tc_term);
          type_of = (uu___1661_22663.type_of);
          universe_of = (uu___1661_22663.universe_of);
          check_type_of = (uu___1661_22663.check_type_of);
          use_bv_sorts = (uu___1661_22663.use_bv_sorts);
          qtbl_name_and_index = (uu___1661_22663.qtbl_name_and_index);
          normalized_eff_names = (uu___1661_22663.normalized_eff_names);
          fv_delta_depths = (uu___1661_22663.fv_delta_depths);
          proof_ns = (uu___1661_22663.proof_ns);
          synth_hook = (uu___1661_22663.synth_hook);
          splice = (uu___1661_22663.splice);
          postprocess = (uu___1661_22663.postprocess);
          is_native_tactic = (uu___1661_22663.is_native_tactic);
          identifier_info = (uu___1661_22663.identifier_info);
          tc_hooks = (uu___1661_22663.tc_hooks);
          dsenv = (uu___1661_22663.dsenv);
          nbe = (uu___1661_22663.nbe);
          strict_args_tab = (uu___1661_22663.strict_args_tab);
          erasable_types_tab = (uu___1661_22663.erasable_types_tab)
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
    fun uu____22682  ->
      match uu____22682 with
      | (ed,quals) ->
          let effects =
            let uu___1670_22696 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1670_22696.order);
              joins = (uu___1670_22696.joins)
            }  in
          let uu___1673_22705 = env  in
          {
            solver = (uu___1673_22705.solver);
            range = (uu___1673_22705.range);
            curmodule = (uu___1673_22705.curmodule);
            gamma = (uu___1673_22705.gamma);
            gamma_sig = (uu___1673_22705.gamma_sig);
            gamma_cache = (uu___1673_22705.gamma_cache);
            modules = (uu___1673_22705.modules);
            expected_typ = (uu___1673_22705.expected_typ);
            sigtab = (uu___1673_22705.sigtab);
            attrtab = (uu___1673_22705.attrtab);
            is_pattern = (uu___1673_22705.is_pattern);
            instantiate_imp = (uu___1673_22705.instantiate_imp);
            effects;
            generalize = (uu___1673_22705.generalize);
            letrecs = (uu___1673_22705.letrecs);
            top_level = (uu___1673_22705.top_level);
            check_uvars = (uu___1673_22705.check_uvars);
            use_eq = (uu___1673_22705.use_eq);
            is_iface = (uu___1673_22705.is_iface);
            admit = (uu___1673_22705.admit);
            lax = (uu___1673_22705.lax);
            lax_universes = (uu___1673_22705.lax_universes);
            phase1 = (uu___1673_22705.phase1);
            failhard = (uu___1673_22705.failhard);
            nosynth = (uu___1673_22705.nosynth);
            uvar_subtyping = (uu___1673_22705.uvar_subtyping);
            tc_term = (uu___1673_22705.tc_term);
            type_of = (uu___1673_22705.type_of);
            universe_of = (uu___1673_22705.universe_of);
            check_type_of = (uu___1673_22705.check_type_of);
            use_bv_sorts = (uu___1673_22705.use_bv_sorts);
            qtbl_name_and_index = (uu___1673_22705.qtbl_name_and_index);
            normalized_eff_names = (uu___1673_22705.normalized_eff_names);
            fv_delta_depths = (uu___1673_22705.fv_delta_depths);
            proof_ns = (uu___1673_22705.proof_ns);
            synth_hook = (uu___1673_22705.synth_hook);
            splice = (uu___1673_22705.splice);
            postprocess = (uu___1673_22705.postprocess);
            is_native_tactic = (uu___1673_22705.is_native_tactic);
            identifier_info = (uu___1673_22705.identifier_info);
            tc_hooks = (uu___1673_22705.tc_hooks);
            dsenv = (uu___1673_22705.dsenv);
            nbe = (uu___1673_22705.nbe);
            strict_args_tab = (uu___1673_22705.strict_args_tab);
            erasable_types_tab = (uu___1673_22705.erasable_types_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____22745 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____22745  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____22903 = (e1.mlift).mlift_wp u t wp  in
                            let uu____22904 = l1 u t wp e  in
                            l2 u t uu____22903 uu____22904))
            | uu____22905 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____22977 = inst_tscheme_with lift_t [u]  in
        match uu____22977 with
        | (uu____22984,lift_t1) ->
            let uu____22986 =
              let uu____22993 =
                let uu____22994 =
                  let uu____23011 =
                    let uu____23022 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____23031 =
                      let uu____23042 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____23042]  in
                    uu____23022 :: uu____23031  in
                  (lift_t1, uu____23011)  in
                FStar_Syntax_Syntax.Tm_app uu____22994  in
              FStar_Syntax_Syntax.mk uu____22993  in
            uu____22986 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____23152 = inst_tscheme_with lift_t [u]  in
        match uu____23152 with
        | (uu____23159,lift_t1) ->
            let uu____23161 =
              let uu____23168 =
                let uu____23169 =
                  let uu____23186 =
                    let uu____23197 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____23206 =
                      let uu____23217 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____23226 =
                        let uu____23237 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____23237]  in
                      uu____23217 :: uu____23226  in
                    uu____23197 :: uu____23206  in
                  (lift_t1, uu____23186)  in
                FStar_Syntax_Syntax.Tm_app uu____23169  in
              FStar_Syntax_Syntax.mk uu____23168  in
            uu____23161 FStar_Pervasives_Native.None
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
          let uu____23339 =
            let uu____23340 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____23340
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____23339  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____23349 =
          let uu____23351 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____23351  in
        let uu____23352 =
          let uu____23354 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____23382 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____23382)
             in
          FStar_Util.dflt "none" uu____23354  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____23349 uu____23352
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____23411  ->
                match uu____23411 with
                | (e,uu____23419) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____23442 =
        match uu____23442 with
        | (i,j) ->
            let uu____23453 = FStar_Ident.lid_equals i j  in
            if uu____23453
            then
              FStar_All.pipe_right (id_edge i)
                (fun _23460  -> FStar_Pervasives_Native.Some _23460)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____23489 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____23499 = FStar_Ident.lid_equals i k  in
                    if uu____23499
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____23513 = FStar_Ident.lid_equals j k
                                 in
                              if uu____23513
                              then []
                              else
                                (let uu____23520 =
                                   let uu____23529 = find_edge order1 (i, k)
                                      in
                                   let uu____23532 = find_edge order1 (k, j)
                                      in
                                   (uu____23529, uu____23532)  in
                                 match uu____23520 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____23547 = compose_edges e1 e2
                                        in
                                     [uu____23547]
                                 | uu____23548 -> [])))))
             in
          FStar_List.append order1 uu____23489  in
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
              let uu____23578 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____23581 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____23581
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____23578
              then
                let uu____23588 =
                  let uu____23594 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____23594)
                   in
                let uu____23598 = get_range env  in
                FStar_Errors.raise_error uu____23588 uu____23598
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____23676 = FStar_Ident.lid_equals i j  in
                           if uu____23676
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____23728 =
                                         let uu____23737 =
                                           find_edge order2 (i, k)  in
                                         let uu____23740 =
                                           find_edge order2 (j, k)  in
                                         (uu____23737, uu____23740)  in
                                       match uu____23728 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____23782,uu____23783)
                                                ->
                                                let uu____23790 =
                                                  let uu____23797 =
                                                    let uu____23799 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23799
                                                     in
                                                  let uu____23802 =
                                                    let uu____23804 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23804
                                                     in
                                                  (uu____23797, uu____23802)
                                                   in
                                                (match uu____23790 with
                                                 | (true ,true ) ->
                                                     let uu____23821 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____23821
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
                                       | uu____23864 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1800_23937 = env.effects  in
         { decls = (uu___1800_23937.decls); order = order2; joins }  in
       let uu___1803_23938 = env  in
       {
         solver = (uu___1803_23938.solver);
         range = (uu___1803_23938.range);
         curmodule = (uu___1803_23938.curmodule);
         gamma = (uu___1803_23938.gamma);
         gamma_sig = (uu___1803_23938.gamma_sig);
         gamma_cache = (uu___1803_23938.gamma_cache);
         modules = (uu___1803_23938.modules);
         expected_typ = (uu___1803_23938.expected_typ);
         sigtab = (uu___1803_23938.sigtab);
         attrtab = (uu___1803_23938.attrtab);
         is_pattern = (uu___1803_23938.is_pattern);
         instantiate_imp = (uu___1803_23938.instantiate_imp);
         effects;
         generalize = (uu___1803_23938.generalize);
         letrecs = (uu___1803_23938.letrecs);
         top_level = (uu___1803_23938.top_level);
         check_uvars = (uu___1803_23938.check_uvars);
         use_eq = (uu___1803_23938.use_eq);
         is_iface = (uu___1803_23938.is_iface);
         admit = (uu___1803_23938.admit);
         lax = (uu___1803_23938.lax);
         lax_universes = (uu___1803_23938.lax_universes);
         phase1 = (uu___1803_23938.phase1);
         failhard = (uu___1803_23938.failhard);
         nosynth = (uu___1803_23938.nosynth);
         uvar_subtyping = (uu___1803_23938.uvar_subtyping);
         tc_term = (uu___1803_23938.tc_term);
         type_of = (uu___1803_23938.type_of);
         universe_of = (uu___1803_23938.universe_of);
         check_type_of = (uu___1803_23938.check_type_of);
         use_bv_sorts = (uu___1803_23938.use_bv_sorts);
         qtbl_name_and_index = (uu___1803_23938.qtbl_name_and_index);
         normalized_eff_names = (uu___1803_23938.normalized_eff_names);
         fv_delta_depths = (uu___1803_23938.fv_delta_depths);
         proof_ns = (uu___1803_23938.proof_ns);
         synth_hook = (uu___1803_23938.synth_hook);
         splice = (uu___1803_23938.splice);
         postprocess = (uu___1803_23938.postprocess);
         is_native_tactic = (uu___1803_23938.is_native_tactic);
         identifier_info = (uu___1803_23938.identifier_info);
         tc_hooks = (uu___1803_23938.tc_hooks);
         dsenv = (uu___1803_23938.dsenv);
         nbe = (uu___1803_23938.nbe);
         strict_args_tab = (uu___1803_23938.strict_args_tab);
         erasable_types_tab = (uu___1803_23938.erasable_types_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1807_23950 = env  in
      {
        solver = (uu___1807_23950.solver);
        range = (uu___1807_23950.range);
        curmodule = (uu___1807_23950.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1807_23950.gamma_sig);
        gamma_cache = (uu___1807_23950.gamma_cache);
        modules = (uu___1807_23950.modules);
        expected_typ = (uu___1807_23950.expected_typ);
        sigtab = (uu___1807_23950.sigtab);
        attrtab = (uu___1807_23950.attrtab);
        is_pattern = (uu___1807_23950.is_pattern);
        instantiate_imp = (uu___1807_23950.instantiate_imp);
        effects = (uu___1807_23950.effects);
        generalize = (uu___1807_23950.generalize);
        letrecs = (uu___1807_23950.letrecs);
        top_level = (uu___1807_23950.top_level);
        check_uvars = (uu___1807_23950.check_uvars);
        use_eq = (uu___1807_23950.use_eq);
        is_iface = (uu___1807_23950.is_iface);
        admit = (uu___1807_23950.admit);
        lax = (uu___1807_23950.lax);
        lax_universes = (uu___1807_23950.lax_universes);
        phase1 = (uu___1807_23950.phase1);
        failhard = (uu___1807_23950.failhard);
        nosynth = (uu___1807_23950.nosynth);
        uvar_subtyping = (uu___1807_23950.uvar_subtyping);
        tc_term = (uu___1807_23950.tc_term);
        type_of = (uu___1807_23950.type_of);
        universe_of = (uu___1807_23950.universe_of);
        check_type_of = (uu___1807_23950.check_type_of);
        use_bv_sorts = (uu___1807_23950.use_bv_sorts);
        qtbl_name_and_index = (uu___1807_23950.qtbl_name_and_index);
        normalized_eff_names = (uu___1807_23950.normalized_eff_names);
        fv_delta_depths = (uu___1807_23950.fv_delta_depths);
        proof_ns = (uu___1807_23950.proof_ns);
        synth_hook = (uu___1807_23950.synth_hook);
        splice = (uu___1807_23950.splice);
        postprocess = (uu___1807_23950.postprocess);
        is_native_tactic = (uu___1807_23950.is_native_tactic);
        identifier_info = (uu___1807_23950.identifier_info);
        tc_hooks = (uu___1807_23950.tc_hooks);
        dsenv = (uu___1807_23950.dsenv);
        nbe = (uu___1807_23950.nbe);
        strict_args_tab = (uu___1807_23950.strict_args_tab);
        erasable_types_tab = (uu___1807_23950.erasable_types_tab)
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
            (let uu___1820_24008 = env  in
             {
               solver = (uu___1820_24008.solver);
               range = (uu___1820_24008.range);
               curmodule = (uu___1820_24008.curmodule);
               gamma = rest;
               gamma_sig = (uu___1820_24008.gamma_sig);
               gamma_cache = (uu___1820_24008.gamma_cache);
               modules = (uu___1820_24008.modules);
               expected_typ = (uu___1820_24008.expected_typ);
               sigtab = (uu___1820_24008.sigtab);
               attrtab = (uu___1820_24008.attrtab);
               is_pattern = (uu___1820_24008.is_pattern);
               instantiate_imp = (uu___1820_24008.instantiate_imp);
               effects = (uu___1820_24008.effects);
               generalize = (uu___1820_24008.generalize);
               letrecs = (uu___1820_24008.letrecs);
               top_level = (uu___1820_24008.top_level);
               check_uvars = (uu___1820_24008.check_uvars);
               use_eq = (uu___1820_24008.use_eq);
               is_iface = (uu___1820_24008.is_iface);
               admit = (uu___1820_24008.admit);
               lax = (uu___1820_24008.lax);
               lax_universes = (uu___1820_24008.lax_universes);
               phase1 = (uu___1820_24008.phase1);
               failhard = (uu___1820_24008.failhard);
               nosynth = (uu___1820_24008.nosynth);
               uvar_subtyping = (uu___1820_24008.uvar_subtyping);
               tc_term = (uu___1820_24008.tc_term);
               type_of = (uu___1820_24008.type_of);
               universe_of = (uu___1820_24008.universe_of);
               check_type_of = (uu___1820_24008.check_type_of);
               use_bv_sorts = (uu___1820_24008.use_bv_sorts);
               qtbl_name_and_index = (uu___1820_24008.qtbl_name_and_index);
               normalized_eff_names = (uu___1820_24008.normalized_eff_names);
               fv_delta_depths = (uu___1820_24008.fv_delta_depths);
               proof_ns = (uu___1820_24008.proof_ns);
               synth_hook = (uu___1820_24008.synth_hook);
               splice = (uu___1820_24008.splice);
               postprocess = (uu___1820_24008.postprocess);
               is_native_tactic = (uu___1820_24008.is_native_tactic);
               identifier_info = (uu___1820_24008.identifier_info);
               tc_hooks = (uu___1820_24008.tc_hooks);
               dsenv = (uu___1820_24008.dsenv);
               nbe = (uu___1820_24008.nbe);
               strict_args_tab = (uu___1820_24008.strict_args_tab);
               erasable_types_tab = (uu___1820_24008.erasable_types_tab)
             }))
    | uu____24009 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24038  ->
             match uu____24038 with | (x,uu____24046) -> push_bv env1 x) env
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
            let uu___1834_24081 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1834_24081.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1834_24081.FStar_Syntax_Syntax.index);
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
        let uu____24154 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24154 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24182 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24182)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1855_24198 = env  in
      {
        solver = (uu___1855_24198.solver);
        range = (uu___1855_24198.range);
        curmodule = (uu___1855_24198.curmodule);
        gamma = (uu___1855_24198.gamma);
        gamma_sig = (uu___1855_24198.gamma_sig);
        gamma_cache = (uu___1855_24198.gamma_cache);
        modules = (uu___1855_24198.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1855_24198.sigtab);
        attrtab = (uu___1855_24198.attrtab);
        is_pattern = (uu___1855_24198.is_pattern);
        instantiate_imp = (uu___1855_24198.instantiate_imp);
        effects = (uu___1855_24198.effects);
        generalize = (uu___1855_24198.generalize);
        letrecs = (uu___1855_24198.letrecs);
        top_level = (uu___1855_24198.top_level);
        check_uvars = (uu___1855_24198.check_uvars);
        use_eq = false;
        is_iface = (uu___1855_24198.is_iface);
        admit = (uu___1855_24198.admit);
        lax = (uu___1855_24198.lax);
        lax_universes = (uu___1855_24198.lax_universes);
        phase1 = (uu___1855_24198.phase1);
        failhard = (uu___1855_24198.failhard);
        nosynth = (uu___1855_24198.nosynth);
        uvar_subtyping = (uu___1855_24198.uvar_subtyping);
        tc_term = (uu___1855_24198.tc_term);
        type_of = (uu___1855_24198.type_of);
        universe_of = (uu___1855_24198.universe_of);
        check_type_of = (uu___1855_24198.check_type_of);
        use_bv_sorts = (uu___1855_24198.use_bv_sorts);
        qtbl_name_and_index = (uu___1855_24198.qtbl_name_and_index);
        normalized_eff_names = (uu___1855_24198.normalized_eff_names);
        fv_delta_depths = (uu___1855_24198.fv_delta_depths);
        proof_ns = (uu___1855_24198.proof_ns);
        synth_hook = (uu___1855_24198.synth_hook);
        splice = (uu___1855_24198.splice);
        postprocess = (uu___1855_24198.postprocess);
        is_native_tactic = (uu___1855_24198.is_native_tactic);
        identifier_info = (uu___1855_24198.identifier_info);
        tc_hooks = (uu___1855_24198.tc_hooks);
        dsenv = (uu___1855_24198.dsenv);
        nbe = (uu___1855_24198.nbe);
        strict_args_tab = (uu___1855_24198.strict_args_tab);
        erasable_types_tab = (uu___1855_24198.erasable_types_tab)
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
    let uu____24229 = expected_typ env_  in
    ((let uu___1862_24235 = env_  in
      {
        solver = (uu___1862_24235.solver);
        range = (uu___1862_24235.range);
        curmodule = (uu___1862_24235.curmodule);
        gamma = (uu___1862_24235.gamma);
        gamma_sig = (uu___1862_24235.gamma_sig);
        gamma_cache = (uu___1862_24235.gamma_cache);
        modules = (uu___1862_24235.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1862_24235.sigtab);
        attrtab = (uu___1862_24235.attrtab);
        is_pattern = (uu___1862_24235.is_pattern);
        instantiate_imp = (uu___1862_24235.instantiate_imp);
        effects = (uu___1862_24235.effects);
        generalize = (uu___1862_24235.generalize);
        letrecs = (uu___1862_24235.letrecs);
        top_level = (uu___1862_24235.top_level);
        check_uvars = (uu___1862_24235.check_uvars);
        use_eq = false;
        is_iface = (uu___1862_24235.is_iface);
        admit = (uu___1862_24235.admit);
        lax = (uu___1862_24235.lax);
        lax_universes = (uu___1862_24235.lax_universes);
        phase1 = (uu___1862_24235.phase1);
        failhard = (uu___1862_24235.failhard);
        nosynth = (uu___1862_24235.nosynth);
        uvar_subtyping = (uu___1862_24235.uvar_subtyping);
        tc_term = (uu___1862_24235.tc_term);
        type_of = (uu___1862_24235.type_of);
        universe_of = (uu___1862_24235.universe_of);
        check_type_of = (uu___1862_24235.check_type_of);
        use_bv_sorts = (uu___1862_24235.use_bv_sorts);
        qtbl_name_and_index = (uu___1862_24235.qtbl_name_and_index);
        normalized_eff_names = (uu___1862_24235.normalized_eff_names);
        fv_delta_depths = (uu___1862_24235.fv_delta_depths);
        proof_ns = (uu___1862_24235.proof_ns);
        synth_hook = (uu___1862_24235.synth_hook);
        splice = (uu___1862_24235.splice);
        postprocess = (uu___1862_24235.postprocess);
        is_native_tactic = (uu___1862_24235.is_native_tactic);
        identifier_info = (uu___1862_24235.identifier_info);
        tc_hooks = (uu___1862_24235.tc_hooks);
        dsenv = (uu___1862_24235.dsenv);
        nbe = (uu___1862_24235.nbe);
        strict_args_tab = (uu___1862_24235.strict_args_tab);
        erasable_types_tab = (uu___1862_24235.erasable_types_tab)
      }), uu____24229)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24247 =
      let uu____24250 = FStar_Ident.id_of_text ""  in [uu____24250]  in
    FStar_Ident.lid_of_ids uu____24247  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24257 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24257
        then
          let uu____24262 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24262 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1870_24290 = env  in
       {
         solver = (uu___1870_24290.solver);
         range = (uu___1870_24290.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1870_24290.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1870_24290.expected_typ);
         sigtab = (uu___1870_24290.sigtab);
         attrtab = (uu___1870_24290.attrtab);
         is_pattern = (uu___1870_24290.is_pattern);
         instantiate_imp = (uu___1870_24290.instantiate_imp);
         effects = (uu___1870_24290.effects);
         generalize = (uu___1870_24290.generalize);
         letrecs = (uu___1870_24290.letrecs);
         top_level = (uu___1870_24290.top_level);
         check_uvars = (uu___1870_24290.check_uvars);
         use_eq = (uu___1870_24290.use_eq);
         is_iface = (uu___1870_24290.is_iface);
         admit = (uu___1870_24290.admit);
         lax = (uu___1870_24290.lax);
         lax_universes = (uu___1870_24290.lax_universes);
         phase1 = (uu___1870_24290.phase1);
         failhard = (uu___1870_24290.failhard);
         nosynth = (uu___1870_24290.nosynth);
         uvar_subtyping = (uu___1870_24290.uvar_subtyping);
         tc_term = (uu___1870_24290.tc_term);
         type_of = (uu___1870_24290.type_of);
         universe_of = (uu___1870_24290.universe_of);
         check_type_of = (uu___1870_24290.check_type_of);
         use_bv_sorts = (uu___1870_24290.use_bv_sorts);
         qtbl_name_and_index = (uu___1870_24290.qtbl_name_and_index);
         normalized_eff_names = (uu___1870_24290.normalized_eff_names);
         fv_delta_depths = (uu___1870_24290.fv_delta_depths);
         proof_ns = (uu___1870_24290.proof_ns);
         synth_hook = (uu___1870_24290.synth_hook);
         splice = (uu___1870_24290.splice);
         postprocess = (uu___1870_24290.postprocess);
         is_native_tactic = (uu___1870_24290.is_native_tactic);
         identifier_info = (uu___1870_24290.identifier_info);
         tc_hooks = (uu___1870_24290.tc_hooks);
         dsenv = (uu___1870_24290.dsenv);
         nbe = (uu___1870_24290.nbe);
         strict_args_tab = (uu___1870_24290.strict_args_tab);
         erasable_types_tab = (uu___1870_24290.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24342)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24346,(uu____24347,t)))::tl1
          ->
          let uu____24368 =
            let uu____24371 = FStar_Syntax_Free.uvars t  in
            ext out uu____24371  in
          aux uu____24368 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24374;
            FStar_Syntax_Syntax.index = uu____24375;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24383 =
            let uu____24386 = FStar_Syntax_Free.uvars t  in
            ext out uu____24386  in
          aux uu____24383 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24444)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24448,(uu____24449,t)))::tl1
          ->
          let uu____24470 =
            let uu____24473 = FStar_Syntax_Free.univs t  in
            ext out uu____24473  in
          aux uu____24470 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24476;
            FStar_Syntax_Syntax.index = uu____24477;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24485 =
            let uu____24488 = FStar_Syntax_Free.univs t  in
            ext out uu____24488  in
          aux uu____24485 tl1
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
          let uu____24550 = FStar_Util.set_add uname out  in
          aux uu____24550 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24553,(uu____24554,t)))::tl1
          ->
          let uu____24575 =
            let uu____24578 = FStar_Syntax_Free.univnames t  in
            ext out uu____24578  in
          aux uu____24575 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24581;
            FStar_Syntax_Syntax.index = uu____24582;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24590 =
            let uu____24593 = FStar_Syntax_Free.univnames t  in
            ext out uu____24593  in
          aux uu____24590 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24614  ->
            match uu___12_24614 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24618 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24631 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24642 =
      let uu____24651 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24651
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24642 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24699 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24712  ->
              match uu___13_24712 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24715 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24715
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24721) ->
                  let uu____24738 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24738))
       in
    FStar_All.pipe_right uu____24699 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24752  ->
    match uu___14_24752 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only (true ) -> "Eager_unfolding_only true"
    | Eager_unfolding_only uu____24758 -> "Eager_unfolding_only false"
    | Unfold d ->
        let uu____24762 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24762
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24785  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24840) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24873,uu____24874) -> false  in
      let uu____24888 =
        FStar_List.tryFind
          (fun uu____24910  ->
             match uu____24910 with | (p,uu____24921) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24888 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24940,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24970 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24970
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2016_24992 = e  in
        {
          solver = (uu___2016_24992.solver);
          range = (uu___2016_24992.range);
          curmodule = (uu___2016_24992.curmodule);
          gamma = (uu___2016_24992.gamma);
          gamma_sig = (uu___2016_24992.gamma_sig);
          gamma_cache = (uu___2016_24992.gamma_cache);
          modules = (uu___2016_24992.modules);
          expected_typ = (uu___2016_24992.expected_typ);
          sigtab = (uu___2016_24992.sigtab);
          attrtab = (uu___2016_24992.attrtab);
          is_pattern = (uu___2016_24992.is_pattern);
          instantiate_imp = (uu___2016_24992.instantiate_imp);
          effects = (uu___2016_24992.effects);
          generalize = (uu___2016_24992.generalize);
          letrecs = (uu___2016_24992.letrecs);
          top_level = (uu___2016_24992.top_level);
          check_uvars = (uu___2016_24992.check_uvars);
          use_eq = (uu___2016_24992.use_eq);
          is_iface = (uu___2016_24992.is_iface);
          admit = (uu___2016_24992.admit);
          lax = (uu___2016_24992.lax);
          lax_universes = (uu___2016_24992.lax_universes);
          phase1 = (uu___2016_24992.phase1);
          failhard = (uu___2016_24992.failhard);
          nosynth = (uu___2016_24992.nosynth);
          uvar_subtyping = (uu___2016_24992.uvar_subtyping);
          tc_term = (uu___2016_24992.tc_term);
          type_of = (uu___2016_24992.type_of);
          universe_of = (uu___2016_24992.universe_of);
          check_type_of = (uu___2016_24992.check_type_of);
          use_bv_sorts = (uu___2016_24992.use_bv_sorts);
          qtbl_name_and_index = (uu___2016_24992.qtbl_name_and_index);
          normalized_eff_names = (uu___2016_24992.normalized_eff_names);
          fv_delta_depths = (uu___2016_24992.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2016_24992.synth_hook);
          splice = (uu___2016_24992.splice);
          postprocess = (uu___2016_24992.postprocess);
          is_native_tactic = (uu___2016_24992.is_native_tactic);
          identifier_info = (uu___2016_24992.identifier_info);
          tc_hooks = (uu___2016_24992.tc_hooks);
          dsenv = (uu___2016_24992.dsenv);
          nbe = (uu___2016_24992.nbe);
          strict_args_tab = (uu___2016_24992.strict_args_tab);
          erasable_types_tab = (uu___2016_24992.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2025_25040 = e  in
      {
        solver = (uu___2025_25040.solver);
        range = (uu___2025_25040.range);
        curmodule = (uu___2025_25040.curmodule);
        gamma = (uu___2025_25040.gamma);
        gamma_sig = (uu___2025_25040.gamma_sig);
        gamma_cache = (uu___2025_25040.gamma_cache);
        modules = (uu___2025_25040.modules);
        expected_typ = (uu___2025_25040.expected_typ);
        sigtab = (uu___2025_25040.sigtab);
        attrtab = (uu___2025_25040.attrtab);
        is_pattern = (uu___2025_25040.is_pattern);
        instantiate_imp = (uu___2025_25040.instantiate_imp);
        effects = (uu___2025_25040.effects);
        generalize = (uu___2025_25040.generalize);
        letrecs = (uu___2025_25040.letrecs);
        top_level = (uu___2025_25040.top_level);
        check_uvars = (uu___2025_25040.check_uvars);
        use_eq = (uu___2025_25040.use_eq);
        is_iface = (uu___2025_25040.is_iface);
        admit = (uu___2025_25040.admit);
        lax = (uu___2025_25040.lax);
        lax_universes = (uu___2025_25040.lax_universes);
        phase1 = (uu___2025_25040.phase1);
        failhard = (uu___2025_25040.failhard);
        nosynth = (uu___2025_25040.nosynth);
        uvar_subtyping = (uu___2025_25040.uvar_subtyping);
        tc_term = (uu___2025_25040.tc_term);
        type_of = (uu___2025_25040.type_of);
        universe_of = (uu___2025_25040.universe_of);
        check_type_of = (uu___2025_25040.check_type_of);
        use_bv_sorts = (uu___2025_25040.use_bv_sorts);
        qtbl_name_and_index = (uu___2025_25040.qtbl_name_and_index);
        normalized_eff_names = (uu___2025_25040.normalized_eff_names);
        fv_delta_depths = (uu___2025_25040.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2025_25040.synth_hook);
        splice = (uu___2025_25040.splice);
        postprocess = (uu___2025_25040.postprocess);
        is_native_tactic = (uu___2025_25040.is_native_tactic);
        identifier_info = (uu___2025_25040.identifier_info);
        tc_hooks = (uu___2025_25040.tc_hooks);
        dsenv = (uu___2025_25040.dsenv);
        nbe = (uu___2025_25040.nbe);
        strict_args_tab = (uu___2025_25040.strict_args_tab);
        erasable_types_tab = (uu___2025_25040.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25056 = FStar_Syntax_Free.names t  in
      let uu____25059 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25056 uu____25059
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25082 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25082
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25092 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25092
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25113 =
      match uu____25113 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25133 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25133)
       in
    let uu____25141 =
      let uu____25145 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25145 FStar_List.rev  in
    FStar_All.pipe_right uu____25141 (FStar_String.concat " ")
  
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
                  (let uu____25215 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25215 with
                   | FStar_Pervasives_Native.Some uu____25219 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25222 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____25232;
        univ_ineqs = uu____25233; implicits = uu____25234;_} -> true
    | uu____25246 -> false
  
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
          let uu___2069_25277 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2069_25277.deferred);
            univ_ineqs = (uu___2069_25277.univ_ineqs);
            implicits = (uu___2069_25277.implicits)
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
          let uu____25316 = FStar_Options.defensive ()  in
          if uu____25316
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25322 =
              let uu____25324 =
                let uu____25326 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25326  in
              Prims.op_Negation uu____25324  in
            (if uu____25322
             then
               let uu____25333 =
                 let uu____25339 =
                   let uu____25341 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25343 =
                     let uu____25345 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25345
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25341 uu____25343
                    in
                 (FStar_Errors.Warning_Defensive, uu____25339)  in
               FStar_Errors.log_issue rng uu____25333
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
          let uu____25385 =
            let uu____25387 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25387  in
          if uu____25385
          then ()
          else
            (let uu____25392 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25392 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25418 =
            let uu____25420 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25420  in
          if uu____25418
          then ()
          else
            (let uu____25425 = bound_vars e  in
             def_check_closed_in rng msg uu____25425 t)
  
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
          let uu___2106_25464 = g  in
          let uu____25465 =
            let uu____25466 =
              let uu____25467 =
                let uu____25474 =
                  let uu____25475 =
                    let uu____25492 =
                      let uu____25503 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25503]  in
                    (f, uu____25492)  in
                  FStar_Syntax_Syntax.Tm_app uu____25475  in
                FStar_Syntax_Syntax.mk uu____25474  in
              uu____25467 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25540  -> FStar_TypeChecker_Common.NonTrivial _25540)
              uu____25466
             in
          {
            guard_f = uu____25465;
            deferred = (uu___2106_25464.deferred);
            univ_ineqs = (uu___2106_25464.univ_ineqs);
            implicits = (uu___2106_25464.implicits)
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
          let uu___2113_25558 = g  in
          let uu____25559 =
            let uu____25560 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25560  in
          {
            guard_f = uu____25559;
            deferred = (uu___2113_25558.deferred);
            univ_ineqs = (uu___2113_25558.univ_ineqs);
            implicits = (uu___2113_25558.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2118_25577 = g  in
          let uu____25578 =
            let uu____25579 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25579  in
          {
            guard_f = uu____25578;
            deferred = (uu___2118_25577.deferred);
            univ_ineqs = (uu___2118_25577.univ_ineqs);
            implicits = (uu___2118_25577.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2122_25581 = g  in
          let uu____25582 =
            let uu____25583 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25583  in
          {
            guard_f = uu____25582;
            deferred = (uu___2122_25581.deferred);
            univ_ineqs = (uu___2122_25581.univ_ineqs);
            implicits = (uu___2122_25581.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25590 ->
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
          let uu____25607 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25607
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25614 =
      let uu____25615 = FStar_Syntax_Util.unmeta t  in
      uu____25615.FStar_Syntax_Syntax.n  in
    match uu____25614 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25619 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25662 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25662;
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
                       let uu____25757 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25757
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2177_25764 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2177_25764.deferred);
              univ_ineqs = (uu___2177_25764.univ_ineqs);
              implicits = (uu___2177_25764.implicits)
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
               let uu____25798 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25798
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
            let uu___2192_25825 = g  in
            let uu____25826 =
              let uu____25827 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25827  in
            {
              guard_f = uu____25826;
              deferred = (uu___2192_25825.deferred);
              univ_ineqs = (uu___2192_25825.univ_ineqs);
              implicits = (uu___2192_25825.implicits)
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
              let uu____25885 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25885 with
              | FStar_Pervasives_Native.Some
                  (uu____25910::(tm,uu____25912)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25976 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25994 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25994;
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
                      let uu___2214_26026 = trivial_guard  in
                      {
                        guard_f = (uu___2214_26026.guard_f);
                        deferred = (uu___2214_26026.deferred);
                        univ_ineqs = (uu___2214_26026.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26044  -> ());
    push = (fun uu____26046  -> ());
    pop = (fun uu____26049  -> ());
    snapshot =
      (fun uu____26052  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26071  -> fun uu____26072  -> ());
    encode_sig = (fun uu____26087  -> fun uu____26088  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26094 =
             let uu____26101 = FStar_Options.peek ()  in (e, g, uu____26101)
              in
           [uu____26094]);
    solve = (fun uu____26117  -> fun uu____26118  -> fun uu____26119  -> ());
    finish = (fun uu____26126  -> ());
    refresh = (fun uu____26128  -> ())
  } 