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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
           (fun uu___0_13177  ->
              match uu___0_13177 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13180 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13180  in
                  let uu____13181 =
                    let uu____13182 = FStar_Syntax_Subst.compress y  in
                    uu____13182.FStar_Syntax_Syntax.n  in
                  (match uu____13181 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13186 =
                         let uu___338_13187 = y1  in
                         let uu____13188 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___338_13187.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___338_13187.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13188
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13186
                   | uu____13191 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___344_13205 = env  in
      let uu____13206 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___344_13205.solver);
        range = (uu___344_13205.range);
        curmodule = (uu___344_13205.curmodule);
        gamma = uu____13206;
        gamma_sig = (uu___344_13205.gamma_sig);
        gamma_cache = (uu___344_13205.gamma_cache);
        modules = (uu___344_13205.modules);
        expected_typ = (uu___344_13205.expected_typ);
        sigtab = (uu___344_13205.sigtab);
        attrtab = (uu___344_13205.attrtab);
        instantiate_imp = (uu___344_13205.instantiate_imp);
        effects = (uu___344_13205.effects);
        generalize = (uu___344_13205.generalize);
        letrecs = (uu___344_13205.letrecs);
        top_level = (uu___344_13205.top_level);
        check_uvars = (uu___344_13205.check_uvars);
        use_eq = (uu___344_13205.use_eq);
        is_iface = (uu___344_13205.is_iface);
        admit = (uu___344_13205.admit);
        lax = (uu___344_13205.lax);
        lax_universes = (uu___344_13205.lax_universes);
        phase1 = (uu___344_13205.phase1);
        failhard = (uu___344_13205.failhard);
        nosynth = (uu___344_13205.nosynth);
        uvar_subtyping = (uu___344_13205.uvar_subtyping);
        tc_term = (uu___344_13205.tc_term);
        type_of = (uu___344_13205.type_of);
        universe_of = (uu___344_13205.universe_of);
        check_type_of = (uu___344_13205.check_type_of);
        use_bv_sorts = (uu___344_13205.use_bv_sorts);
        qtbl_name_and_index = (uu___344_13205.qtbl_name_and_index);
        normalized_eff_names = (uu___344_13205.normalized_eff_names);
        fv_delta_depths = (uu___344_13205.fv_delta_depths);
        proof_ns = (uu___344_13205.proof_ns);
        synth_hook = (uu___344_13205.synth_hook);
        splice = (uu___344_13205.splice);
        mpreprocess = (uu___344_13205.mpreprocess);
        postprocess = (uu___344_13205.postprocess);
        is_native_tactic = (uu___344_13205.is_native_tactic);
        identifier_info = (uu___344_13205.identifier_info);
        tc_hooks = (uu___344_13205.tc_hooks);
        dsenv = (uu___344_13205.dsenv);
        nbe = (uu___344_13205.nbe);
        strict_args_tab = (uu___344_13205.strict_args_tab);
        erasable_types_tab = (uu___344_13205.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13214  -> fun uu____13215  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___351_13237 = env  in
      {
        solver = (uu___351_13237.solver);
        range = (uu___351_13237.range);
        curmodule = (uu___351_13237.curmodule);
        gamma = (uu___351_13237.gamma);
        gamma_sig = (uu___351_13237.gamma_sig);
        gamma_cache = (uu___351_13237.gamma_cache);
        modules = (uu___351_13237.modules);
        expected_typ = (uu___351_13237.expected_typ);
        sigtab = (uu___351_13237.sigtab);
        attrtab = (uu___351_13237.attrtab);
        instantiate_imp = (uu___351_13237.instantiate_imp);
        effects = (uu___351_13237.effects);
        generalize = (uu___351_13237.generalize);
        letrecs = (uu___351_13237.letrecs);
        top_level = (uu___351_13237.top_level);
        check_uvars = (uu___351_13237.check_uvars);
        use_eq = (uu___351_13237.use_eq);
        is_iface = (uu___351_13237.is_iface);
        admit = (uu___351_13237.admit);
        lax = (uu___351_13237.lax);
        lax_universes = (uu___351_13237.lax_universes);
        phase1 = (uu___351_13237.phase1);
        failhard = (uu___351_13237.failhard);
        nosynth = (uu___351_13237.nosynth);
        uvar_subtyping = (uu___351_13237.uvar_subtyping);
        tc_term = (uu___351_13237.tc_term);
        type_of = (uu___351_13237.type_of);
        universe_of = (uu___351_13237.universe_of);
        check_type_of = (uu___351_13237.check_type_of);
        use_bv_sorts = (uu___351_13237.use_bv_sorts);
        qtbl_name_and_index = (uu___351_13237.qtbl_name_and_index);
        normalized_eff_names = (uu___351_13237.normalized_eff_names);
        fv_delta_depths = (uu___351_13237.fv_delta_depths);
        proof_ns = (uu___351_13237.proof_ns);
        synth_hook = (uu___351_13237.synth_hook);
        splice = (uu___351_13237.splice);
        mpreprocess = (uu___351_13237.mpreprocess);
        postprocess = (uu___351_13237.postprocess);
        is_native_tactic = (uu___351_13237.is_native_tactic);
        identifier_info = (uu___351_13237.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___351_13237.dsenv);
        nbe = (uu___351_13237.nbe);
        strict_args_tab = (uu___351_13237.strict_args_tab);
        erasable_types_tab = (uu___351_13237.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___355_13249 = e  in
      let uu____13250 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___355_13249.solver);
        range = (uu___355_13249.range);
        curmodule = (uu___355_13249.curmodule);
        gamma = (uu___355_13249.gamma);
        gamma_sig = (uu___355_13249.gamma_sig);
        gamma_cache = (uu___355_13249.gamma_cache);
        modules = (uu___355_13249.modules);
        expected_typ = (uu___355_13249.expected_typ);
        sigtab = (uu___355_13249.sigtab);
        attrtab = (uu___355_13249.attrtab);
        instantiate_imp = (uu___355_13249.instantiate_imp);
        effects = (uu___355_13249.effects);
        generalize = (uu___355_13249.generalize);
        letrecs = (uu___355_13249.letrecs);
        top_level = (uu___355_13249.top_level);
        check_uvars = (uu___355_13249.check_uvars);
        use_eq = (uu___355_13249.use_eq);
        is_iface = (uu___355_13249.is_iface);
        admit = (uu___355_13249.admit);
        lax = (uu___355_13249.lax);
        lax_universes = (uu___355_13249.lax_universes);
        phase1 = (uu___355_13249.phase1);
        failhard = (uu___355_13249.failhard);
        nosynth = (uu___355_13249.nosynth);
        uvar_subtyping = (uu___355_13249.uvar_subtyping);
        tc_term = (uu___355_13249.tc_term);
        type_of = (uu___355_13249.type_of);
        universe_of = (uu___355_13249.universe_of);
        check_type_of = (uu___355_13249.check_type_of);
        use_bv_sorts = (uu___355_13249.use_bv_sorts);
        qtbl_name_and_index = (uu___355_13249.qtbl_name_and_index);
        normalized_eff_names = (uu___355_13249.normalized_eff_names);
        fv_delta_depths = (uu___355_13249.fv_delta_depths);
        proof_ns = (uu___355_13249.proof_ns);
        synth_hook = (uu___355_13249.synth_hook);
        splice = (uu___355_13249.splice);
        mpreprocess = (uu___355_13249.mpreprocess);
        postprocess = (uu___355_13249.postprocess);
        is_native_tactic = (uu___355_13249.is_native_tactic);
        identifier_info = (uu___355_13249.identifier_info);
        tc_hooks = (uu___355_13249.tc_hooks);
        dsenv = uu____13250;
        nbe = (uu___355_13249.nbe);
        strict_args_tab = (uu___355_13249.strict_args_tab);
        erasable_types_tab = (uu___355_13249.erasable_types_tab)
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
      | (NoDelta ,uu____13279) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13282,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13284,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13287 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13301 . unit -> 'Auu____13301 FStar_Util.smap =
  fun uu____13308  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13314 . unit -> 'Auu____13314 FStar_Util.smap =
  fun uu____13321  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13459 = new_gamma_cache ()  in
                  let uu____13462 = new_sigtab ()  in
                  let uu____13465 = new_sigtab ()  in
                  let uu____13472 =
                    let uu____13487 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13487, FStar_Pervasives_Native.None)  in
                  let uu____13508 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13512 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13516 = FStar_Options.using_facts_from ()  in
                  let uu____13517 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13520 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13521 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13535 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13459;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13462;
                    attrtab = uu____13465;
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
                    qtbl_name_and_index = uu____13472;
                    normalized_eff_names = uu____13508;
                    fv_delta_depths = uu____13512;
                    proof_ns = uu____13516;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
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
                    is_native_tactic = (fun uu____13608  -> false);
                    identifier_info = uu____13517;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13520;
                    nbe = nbe1;
                    strict_args_tab = uu____13521;
                    erasable_types_tab = uu____13535
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
  fun uu____13687  ->
    let uu____13688 = FStar_ST.op_Bang query_indices  in
    match uu____13688 with
    | [] -> failwith "Empty query indices!"
    | uu____13743 ->
        let uu____13753 =
          let uu____13763 =
            let uu____13771 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13771  in
          let uu____13825 = FStar_ST.op_Bang query_indices  in uu____13763 ::
            uu____13825
           in
        FStar_ST.op_Colon_Equals query_indices uu____13753
  
let (pop_query_indices : unit -> unit) =
  fun uu____13921  ->
    let uu____13922 = FStar_ST.op_Bang query_indices  in
    match uu____13922 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14049  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14086  ->
    match uu____14086 with
    | (l,n1) ->
        let uu____14096 = FStar_ST.op_Bang query_indices  in
        (match uu____14096 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14218 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14241  ->
    let uu____14242 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14242
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14310 =
       let uu____14313 = FStar_ST.op_Bang stack  in env :: uu____14313  in
     FStar_ST.op_Colon_Equals stack uu____14310);
    (let uu___426_14362 = env  in
     let uu____14363 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14366 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14369 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14376 =
       let uu____14391 =
         let uu____14395 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14395  in
       let uu____14427 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14391, uu____14427)  in
     let uu____14476 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14479 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14482 =
       let uu____14485 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14485  in
     let uu____14505 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14518 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___426_14362.solver);
       range = (uu___426_14362.range);
       curmodule = (uu___426_14362.curmodule);
       gamma = (uu___426_14362.gamma);
       gamma_sig = (uu___426_14362.gamma_sig);
       gamma_cache = uu____14363;
       modules = (uu___426_14362.modules);
       expected_typ = (uu___426_14362.expected_typ);
       sigtab = uu____14366;
       attrtab = uu____14369;
       instantiate_imp = (uu___426_14362.instantiate_imp);
       effects = (uu___426_14362.effects);
       generalize = (uu___426_14362.generalize);
       letrecs = (uu___426_14362.letrecs);
       top_level = (uu___426_14362.top_level);
       check_uvars = (uu___426_14362.check_uvars);
       use_eq = (uu___426_14362.use_eq);
       is_iface = (uu___426_14362.is_iface);
       admit = (uu___426_14362.admit);
       lax = (uu___426_14362.lax);
       lax_universes = (uu___426_14362.lax_universes);
       phase1 = (uu___426_14362.phase1);
       failhard = (uu___426_14362.failhard);
       nosynth = (uu___426_14362.nosynth);
       uvar_subtyping = (uu___426_14362.uvar_subtyping);
       tc_term = (uu___426_14362.tc_term);
       type_of = (uu___426_14362.type_of);
       universe_of = (uu___426_14362.universe_of);
       check_type_of = (uu___426_14362.check_type_of);
       use_bv_sorts = (uu___426_14362.use_bv_sorts);
       qtbl_name_and_index = uu____14376;
       normalized_eff_names = uu____14476;
       fv_delta_depths = uu____14479;
       proof_ns = (uu___426_14362.proof_ns);
       synth_hook = (uu___426_14362.synth_hook);
       splice = (uu___426_14362.splice);
       mpreprocess = (uu___426_14362.mpreprocess);
       postprocess = (uu___426_14362.postprocess);
       is_native_tactic = (uu___426_14362.is_native_tactic);
       identifier_info = uu____14482;
       tc_hooks = (uu___426_14362.tc_hooks);
       dsenv = (uu___426_14362.dsenv);
       nbe = (uu___426_14362.nbe);
       strict_args_tab = uu____14505;
       erasable_types_tab = uu____14518
     })
  
let (pop_stack : unit -> env) =
  fun uu____14528  ->
    let uu____14529 = FStar_ST.op_Bang stack  in
    match uu____14529 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14583 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14673  ->
           let uu____14674 = snapshot_stack env  in
           match uu____14674 with
           | (stack_depth,env1) ->
               let uu____14708 = snapshot_query_indices ()  in
               (match uu____14708 with
                | (query_indices_depth,()) ->
                    let uu____14741 = (env1.solver).snapshot msg  in
                    (match uu____14741 with
                     | (solver_depth,()) ->
                         let uu____14798 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14798 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___451_14865 = env1  in
                                 {
                                   solver = (uu___451_14865.solver);
                                   range = (uu___451_14865.range);
                                   curmodule = (uu___451_14865.curmodule);
                                   gamma = (uu___451_14865.gamma);
                                   gamma_sig = (uu___451_14865.gamma_sig);
                                   gamma_cache = (uu___451_14865.gamma_cache);
                                   modules = (uu___451_14865.modules);
                                   expected_typ =
                                     (uu___451_14865.expected_typ);
                                   sigtab = (uu___451_14865.sigtab);
                                   attrtab = (uu___451_14865.attrtab);
                                   instantiate_imp =
                                     (uu___451_14865.instantiate_imp);
                                   effects = (uu___451_14865.effects);
                                   generalize = (uu___451_14865.generalize);
                                   letrecs = (uu___451_14865.letrecs);
                                   top_level = (uu___451_14865.top_level);
                                   check_uvars = (uu___451_14865.check_uvars);
                                   use_eq = (uu___451_14865.use_eq);
                                   is_iface = (uu___451_14865.is_iface);
                                   admit = (uu___451_14865.admit);
                                   lax = (uu___451_14865.lax);
                                   lax_universes =
                                     (uu___451_14865.lax_universes);
                                   phase1 = (uu___451_14865.phase1);
                                   failhard = (uu___451_14865.failhard);
                                   nosynth = (uu___451_14865.nosynth);
                                   uvar_subtyping =
                                     (uu___451_14865.uvar_subtyping);
                                   tc_term = (uu___451_14865.tc_term);
                                   type_of = (uu___451_14865.type_of);
                                   universe_of = (uu___451_14865.universe_of);
                                   check_type_of =
                                     (uu___451_14865.check_type_of);
                                   use_bv_sorts =
                                     (uu___451_14865.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___451_14865.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___451_14865.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___451_14865.fv_delta_depths);
                                   proof_ns = (uu___451_14865.proof_ns);
                                   synth_hook = (uu___451_14865.synth_hook);
                                   splice = (uu___451_14865.splice);
                                   mpreprocess = (uu___451_14865.mpreprocess);
                                   postprocess = (uu___451_14865.postprocess);
                                   is_native_tactic =
                                     (uu___451_14865.is_native_tactic);
                                   identifier_info =
                                     (uu___451_14865.identifier_info);
                                   tc_hooks = (uu___451_14865.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___451_14865.nbe);
                                   strict_args_tab =
                                     (uu___451_14865.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___451_14865.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14899  ->
             let uu____14900 =
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
             match uu____14900 with
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
                             ((let uu____15080 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15080
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15096 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15096
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15128,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15170 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15200  ->
                  match uu____15200 with
                  | (m,uu____15208) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15170 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___496_15223 = env  in
               {
                 solver = (uu___496_15223.solver);
                 range = (uu___496_15223.range);
                 curmodule = (uu___496_15223.curmodule);
                 gamma = (uu___496_15223.gamma);
                 gamma_sig = (uu___496_15223.gamma_sig);
                 gamma_cache = (uu___496_15223.gamma_cache);
                 modules = (uu___496_15223.modules);
                 expected_typ = (uu___496_15223.expected_typ);
                 sigtab = (uu___496_15223.sigtab);
                 attrtab = (uu___496_15223.attrtab);
                 instantiate_imp = (uu___496_15223.instantiate_imp);
                 effects = (uu___496_15223.effects);
                 generalize = (uu___496_15223.generalize);
                 letrecs = (uu___496_15223.letrecs);
                 top_level = (uu___496_15223.top_level);
                 check_uvars = (uu___496_15223.check_uvars);
                 use_eq = (uu___496_15223.use_eq);
                 is_iface = (uu___496_15223.is_iface);
                 admit = (uu___496_15223.admit);
                 lax = (uu___496_15223.lax);
                 lax_universes = (uu___496_15223.lax_universes);
                 phase1 = (uu___496_15223.phase1);
                 failhard = (uu___496_15223.failhard);
                 nosynth = (uu___496_15223.nosynth);
                 uvar_subtyping = (uu___496_15223.uvar_subtyping);
                 tc_term = (uu___496_15223.tc_term);
                 type_of = (uu___496_15223.type_of);
                 universe_of = (uu___496_15223.universe_of);
                 check_type_of = (uu___496_15223.check_type_of);
                 use_bv_sorts = (uu___496_15223.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___496_15223.normalized_eff_names);
                 fv_delta_depths = (uu___496_15223.fv_delta_depths);
                 proof_ns = (uu___496_15223.proof_ns);
                 synth_hook = (uu___496_15223.synth_hook);
                 splice = (uu___496_15223.splice);
                 mpreprocess = (uu___496_15223.mpreprocess);
                 postprocess = (uu___496_15223.postprocess);
                 is_native_tactic = (uu___496_15223.is_native_tactic);
                 identifier_info = (uu___496_15223.identifier_info);
                 tc_hooks = (uu___496_15223.tc_hooks);
                 dsenv = (uu___496_15223.dsenv);
                 nbe = (uu___496_15223.nbe);
                 strict_args_tab = (uu___496_15223.strict_args_tab);
                 erasable_types_tab = (uu___496_15223.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15240,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___505_15256 = env  in
               {
                 solver = (uu___505_15256.solver);
                 range = (uu___505_15256.range);
                 curmodule = (uu___505_15256.curmodule);
                 gamma = (uu___505_15256.gamma);
                 gamma_sig = (uu___505_15256.gamma_sig);
                 gamma_cache = (uu___505_15256.gamma_cache);
                 modules = (uu___505_15256.modules);
                 expected_typ = (uu___505_15256.expected_typ);
                 sigtab = (uu___505_15256.sigtab);
                 attrtab = (uu___505_15256.attrtab);
                 instantiate_imp = (uu___505_15256.instantiate_imp);
                 effects = (uu___505_15256.effects);
                 generalize = (uu___505_15256.generalize);
                 letrecs = (uu___505_15256.letrecs);
                 top_level = (uu___505_15256.top_level);
                 check_uvars = (uu___505_15256.check_uvars);
                 use_eq = (uu___505_15256.use_eq);
                 is_iface = (uu___505_15256.is_iface);
                 admit = (uu___505_15256.admit);
                 lax = (uu___505_15256.lax);
                 lax_universes = (uu___505_15256.lax_universes);
                 phase1 = (uu___505_15256.phase1);
                 failhard = (uu___505_15256.failhard);
                 nosynth = (uu___505_15256.nosynth);
                 uvar_subtyping = (uu___505_15256.uvar_subtyping);
                 tc_term = (uu___505_15256.tc_term);
                 type_of = (uu___505_15256.type_of);
                 universe_of = (uu___505_15256.universe_of);
                 check_type_of = (uu___505_15256.check_type_of);
                 use_bv_sorts = (uu___505_15256.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___505_15256.normalized_eff_names);
                 fv_delta_depths = (uu___505_15256.fv_delta_depths);
                 proof_ns = (uu___505_15256.proof_ns);
                 synth_hook = (uu___505_15256.synth_hook);
                 splice = (uu___505_15256.splice);
                 mpreprocess = (uu___505_15256.mpreprocess);
                 postprocess = (uu___505_15256.postprocess);
                 is_native_tactic = (uu___505_15256.is_native_tactic);
                 identifier_info = (uu___505_15256.identifier_info);
                 tc_hooks = (uu___505_15256.tc_hooks);
                 dsenv = (uu___505_15256.dsenv);
                 nbe = (uu___505_15256.nbe);
                 strict_args_tab = (uu___505_15256.strict_args_tab);
                 erasable_types_tab = (uu___505_15256.erasable_types_tab)
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
        (let uu___512_15299 = e  in
         {
           solver = (uu___512_15299.solver);
           range = r;
           curmodule = (uu___512_15299.curmodule);
           gamma = (uu___512_15299.gamma);
           gamma_sig = (uu___512_15299.gamma_sig);
           gamma_cache = (uu___512_15299.gamma_cache);
           modules = (uu___512_15299.modules);
           expected_typ = (uu___512_15299.expected_typ);
           sigtab = (uu___512_15299.sigtab);
           attrtab = (uu___512_15299.attrtab);
           instantiate_imp = (uu___512_15299.instantiate_imp);
           effects = (uu___512_15299.effects);
           generalize = (uu___512_15299.generalize);
           letrecs = (uu___512_15299.letrecs);
           top_level = (uu___512_15299.top_level);
           check_uvars = (uu___512_15299.check_uvars);
           use_eq = (uu___512_15299.use_eq);
           is_iface = (uu___512_15299.is_iface);
           admit = (uu___512_15299.admit);
           lax = (uu___512_15299.lax);
           lax_universes = (uu___512_15299.lax_universes);
           phase1 = (uu___512_15299.phase1);
           failhard = (uu___512_15299.failhard);
           nosynth = (uu___512_15299.nosynth);
           uvar_subtyping = (uu___512_15299.uvar_subtyping);
           tc_term = (uu___512_15299.tc_term);
           type_of = (uu___512_15299.type_of);
           universe_of = (uu___512_15299.universe_of);
           check_type_of = (uu___512_15299.check_type_of);
           use_bv_sorts = (uu___512_15299.use_bv_sorts);
           qtbl_name_and_index = (uu___512_15299.qtbl_name_and_index);
           normalized_eff_names = (uu___512_15299.normalized_eff_names);
           fv_delta_depths = (uu___512_15299.fv_delta_depths);
           proof_ns = (uu___512_15299.proof_ns);
           synth_hook = (uu___512_15299.synth_hook);
           splice = (uu___512_15299.splice);
           mpreprocess = (uu___512_15299.mpreprocess);
           postprocess = (uu___512_15299.postprocess);
           is_native_tactic = (uu___512_15299.is_native_tactic);
           identifier_info = (uu___512_15299.identifier_info);
           tc_hooks = (uu___512_15299.tc_hooks);
           dsenv = (uu___512_15299.dsenv);
           nbe = (uu___512_15299.nbe);
           strict_args_tab = (uu___512_15299.strict_args_tab);
           erasable_types_tab = (uu___512_15299.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15319 =
        let uu____15320 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15320 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15319
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15375 =
          let uu____15376 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15376 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15375
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15431 =
          let uu____15432 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15432 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15431
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15487 =
        let uu____15488 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15488 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15487
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___529_15552 = env  in
      {
        solver = (uu___529_15552.solver);
        range = (uu___529_15552.range);
        curmodule = lid;
        gamma = (uu___529_15552.gamma);
        gamma_sig = (uu___529_15552.gamma_sig);
        gamma_cache = (uu___529_15552.gamma_cache);
        modules = (uu___529_15552.modules);
        expected_typ = (uu___529_15552.expected_typ);
        sigtab = (uu___529_15552.sigtab);
        attrtab = (uu___529_15552.attrtab);
        instantiate_imp = (uu___529_15552.instantiate_imp);
        effects = (uu___529_15552.effects);
        generalize = (uu___529_15552.generalize);
        letrecs = (uu___529_15552.letrecs);
        top_level = (uu___529_15552.top_level);
        check_uvars = (uu___529_15552.check_uvars);
        use_eq = (uu___529_15552.use_eq);
        is_iface = (uu___529_15552.is_iface);
        admit = (uu___529_15552.admit);
        lax = (uu___529_15552.lax);
        lax_universes = (uu___529_15552.lax_universes);
        phase1 = (uu___529_15552.phase1);
        failhard = (uu___529_15552.failhard);
        nosynth = (uu___529_15552.nosynth);
        uvar_subtyping = (uu___529_15552.uvar_subtyping);
        tc_term = (uu___529_15552.tc_term);
        type_of = (uu___529_15552.type_of);
        universe_of = (uu___529_15552.universe_of);
        check_type_of = (uu___529_15552.check_type_of);
        use_bv_sorts = (uu___529_15552.use_bv_sorts);
        qtbl_name_and_index = (uu___529_15552.qtbl_name_and_index);
        normalized_eff_names = (uu___529_15552.normalized_eff_names);
        fv_delta_depths = (uu___529_15552.fv_delta_depths);
        proof_ns = (uu___529_15552.proof_ns);
        synth_hook = (uu___529_15552.synth_hook);
        splice = (uu___529_15552.splice);
        mpreprocess = (uu___529_15552.mpreprocess);
        postprocess = (uu___529_15552.postprocess);
        is_native_tactic = (uu___529_15552.is_native_tactic);
        identifier_info = (uu___529_15552.identifier_info);
        tc_hooks = (uu___529_15552.tc_hooks);
        dsenv = (uu___529_15552.dsenv);
        nbe = (uu___529_15552.nbe);
        strict_args_tab = (uu___529_15552.strict_args_tab);
        erasable_types_tab = (uu___529_15552.erasable_types_tab)
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
      let uu____15583 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15583
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15596 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15596)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15611 =
      let uu____15613 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15613  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15611)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15622  ->
    let uu____15623 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15623
  
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
      | ((formals,t),uu____15723) ->
          let vs = mk_univ_subst formals us  in
          let uu____15747 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15747)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15764  ->
    match uu___1_15764 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15790  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15810 = inst_tscheme t  in
      match uu____15810 with
      | (us,t1) ->
          let uu____15821 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15821)
  
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
          let uu____15846 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15848 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15846 uu____15848
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
        fun uu____15875  ->
          match uu____15875 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15889 =
                    let uu____15891 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15895 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15899 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15901 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15891 uu____15895 uu____15899 uu____15901
                     in
                  failwith uu____15889)
               else ();
               (let uu____15906 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15906))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15924 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15935 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15946 -> false
  
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
             | ([],uu____15994) -> Maybe
             | (uu____16001,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16021 -> No  in
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
          let uu____16115 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16115 with
          | FStar_Pervasives_Native.None  ->
              let uu____16138 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16182  ->
                     match uu___2_16182 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16221 = FStar_Ident.lid_equals lid l  in
                         if uu____16221
                         then
                           let uu____16244 =
                             let uu____16263 =
                               let uu____16278 = inst_tscheme t  in
                               FStar_Util.Inl uu____16278  in
                             let uu____16293 = FStar_Ident.range_of_lid l  in
                             (uu____16263, uu____16293)  in
                           FStar_Pervasives_Native.Some uu____16244
                         else FStar_Pervasives_Native.None
                     | uu____16346 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16138
                (fun uu____16384  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16394  ->
                        match uu___3_16394 with
                        | (uu____16397,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16399);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16400;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16401;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16402;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16403;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16404;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16426 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16426
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
                                  uu____16478 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16485 -> cache t  in
                            let uu____16486 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16486 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16492 =
                                   let uu____16493 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16493)
                                    in
                                 maybe_cache uu____16492)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16564 = find_in_sigtab env lid  in
         match uu____16564 with
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
      let uu____16645 = lookup_qname env lid  in
      match uu____16645 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16666,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16780 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16780 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16825 =
          let uu____16828 = lookup_attr env1 attr  in se1 :: uu____16828  in
        FStar_Util.smap_add (attrtab env1) attr uu____16825  in
      FStar_List.iter
        (fun attr  ->
           let uu____16838 =
             let uu____16839 = FStar_Syntax_Subst.compress attr  in
             uu____16839.FStar_Syntax_Syntax.n  in
           match uu____16838 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16843 =
                 let uu____16845 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16845.FStar_Ident.str  in
               add_one1 env se uu____16843
           | uu____16846 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16869) ->
          add_sigelts env ses
      | uu____16878 ->
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
        (fun uu___4_16916  ->
           match uu___4_16916 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16934 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16996,lb::[]),uu____16998) ->
            let uu____17007 =
              let uu____17016 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17025 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17016, uu____17025)  in
            FStar_Pervasives_Native.Some uu____17007
        | FStar_Syntax_Syntax.Sig_let ((uu____17038,lbs),uu____17040) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17072 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17085 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17085
                     then
                       let uu____17098 =
                         let uu____17107 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17116 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17107, uu____17116)  in
                       FStar_Pervasives_Native.Some uu____17098
                     else FStar_Pervasives_Native.None)
        | uu____17139 -> FStar_Pervasives_Native.None
  
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
                    let uu____17231 =
                      let uu____17233 =
                        let uu____17235 =
                          let uu____17237 =
                            let uu____17239 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17245 =
                              let uu____17247 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17247  in
                            Prims.op_Hat uu____17239 uu____17245  in
                          Prims.op_Hat ", expected " uu____17237  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17235
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17233
                       in
                    failwith uu____17231
                  else ());
             (let uu____17254 =
                let uu____17263 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17263, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17254))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17283,uu____17284) ->
            let uu____17289 =
              let uu____17298 =
                let uu____17303 =
                  let uu____17304 =
                    let uu____17307 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17307  in
                  (us, uu____17304)  in
                inst_ts us_opt uu____17303  in
              (uu____17298, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17289
        | uu____17326 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17415 =
          match uu____17415 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17511,uvs,t,uu____17514,uu____17515,uu____17516);
                      FStar_Syntax_Syntax.sigrng = uu____17517;
                      FStar_Syntax_Syntax.sigquals = uu____17518;
                      FStar_Syntax_Syntax.sigmeta = uu____17519;
                      FStar_Syntax_Syntax.sigattrs = uu____17520;
                      FStar_Syntax_Syntax.sigopts = uu____17521;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17546 =
                     let uu____17555 = inst_tscheme1 (uvs, t)  in
                     (uu____17555, rng)  in
                   FStar_Pervasives_Native.Some uu____17546
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17579;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17581;
                      FStar_Syntax_Syntax.sigattrs = uu____17582;
                      FStar_Syntax_Syntax.sigopts = uu____17583;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17602 =
                     let uu____17604 = in_cur_mod env l  in uu____17604 = Yes
                      in
                   if uu____17602
                   then
                     let uu____17616 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17616
                      then
                        let uu____17632 =
                          let uu____17641 = inst_tscheme1 (uvs, t)  in
                          (uu____17641, rng)  in
                        FStar_Pervasives_Native.Some uu____17632
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17674 =
                        let uu____17683 = inst_tscheme1 (uvs, t)  in
                        (uu____17683, rng)  in
                      FStar_Pervasives_Native.Some uu____17674)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17708,uu____17709);
                      FStar_Syntax_Syntax.sigrng = uu____17710;
                      FStar_Syntax_Syntax.sigquals = uu____17711;
                      FStar_Syntax_Syntax.sigmeta = uu____17712;
                      FStar_Syntax_Syntax.sigattrs = uu____17713;
                      FStar_Syntax_Syntax.sigopts = uu____17714;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17757 =
                          let uu____17766 = inst_tscheme1 (uvs, k)  in
                          (uu____17766, rng)  in
                        FStar_Pervasives_Native.Some uu____17757
                    | uu____17787 ->
                        let uu____17788 =
                          let uu____17797 =
                            let uu____17802 =
                              let uu____17803 =
                                let uu____17806 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17806
                                 in
                              (uvs, uu____17803)  in
                            inst_tscheme1 uu____17802  in
                          (uu____17797, rng)  in
                        FStar_Pervasives_Native.Some uu____17788)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17829,uu____17830);
                      FStar_Syntax_Syntax.sigrng = uu____17831;
                      FStar_Syntax_Syntax.sigquals = uu____17832;
                      FStar_Syntax_Syntax.sigmeta = uu____17833;
                      FStar_Syntax_Syntax.sigattrs = uu____17834;
                      FStar_Syntax_Syntax.sigopts = uu____17835;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17879 =
                          let uu____17888 = inst_tscheme_with (uvs, k) us  in
                          (uu____17888, rng)  in
                        FStar_Pervasives_Native.Some uu____17879
                    | uu____17909 ->
                        let uu____17910 =
                          let uu____17919 =
                            let uu____17924 =
                              let uu____17925 =
                                let uu____17928 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17928
                                 in
                              (uvs, uu____17925)  in
                            inst_tscheme_with uu____17924 us  in
                          (uu____17919, rng)  in
                        FStar_Pervasives_Native.Some uu____17910)
               | FStar_Util.Inr se ->
                   let uu____17964 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17985;
                          FStar_Syntax_Syntax.sigrng = uu____17986;
                          FStar_Syntax_Syntax.sigquals = uu____17987;
                          FStar_Syntax_Syntax.sigmeta = uu____17988;
                          FStar_Syntax_Syntax.sigattrs = uu____17989;
                          FStar_Syntax_Syntax.sigopts = uu____17990;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18007 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17964
                     (FStar_Util.map_option
                        (fun uu____18055  ->
                           match uu____18055 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18086 =
          let uu____18097 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18097 mapper  in
        match uu____18086 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18171 =
              let uu____18182 =
                let uu____18189 =
                  let uu___866_18192 = t  in
                  let uu____18193 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___866_18192.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18193;
                    FStar_Syntax_Syntax.vars =
                      (uu___866_18192.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18189)  in
              (uu____18182, r)  in
            FStar_Pervasives_Native.Some uu____18171
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18242 = lookup_qname env l  in
      match uu____18242 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18263 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18317 = try_lookup_bv env bv  in
      match uu____18317 with
      | FStar_Pervasives_Native.None  ->
          let uu____18332 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18332 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18348 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18349 =
            let uu____18350 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18350  in
          (uu____18348, uu____18349)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18372 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18372 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18438 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18438  in
          let uu____18439 =
            let uu____18448 =
              let uu____18453 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18453)  in
            (uu____18448, r1)  in
          FStar_Pervasives_Native.Some uu____18439
  
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
        let uu____18488 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18488 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18521,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18546 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18546  in
            let uu____18547 =
              let uu____18552 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18552, r1)  in
            FStar_Pervasives_Native.Some uu____18547
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18576 = try_lookup_lid env l  in
      match uu____18576 with
      | FStar_Pervasives_Native.None  ->
          let uu____18603 = name_not_found l  in
          let uu____18609 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18603 uu____18609
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18652  ->
              match uu___5_18652 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18656 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18677 = lookup_qname env lid  in
      match uu____18677 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18686,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18689;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18691;
              FStar_Syntax_Syntax.sigattrs = uu____18692;
              FStar_Syntax_Syntax.sigopts = uu____18693;_},FStar_Pervasives_Native.None
            ),uu____18694)
          ->
          let uu____18745 =
            let uu____18752 =
              let uu____18753 =
                let uu____18756 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18756 t  in
              (uvs, uu____18753)  in
            (uu____18752, q)  in
          FStar_Pervasives_Native.Some uu____18745
      | uu____18769 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18791 = lookup_qname env lid  in
      match uu____18791 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18796,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18799;
              FStar_Syntax_Syntax.sigquals = uu____18800;
              FStar_Syntax_Syntax.sigmeta = uu____18801;
              FStar_Syntax_Syntax.sigattrs = uu____18802;
              FStar_Syntax_Syntax.sigopts = uu____18803;_},FStar_Pervasives_Native.None
            ),uu____18804)
          ->
          let uu____18855 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18855 (uvs, t)
      | uu____18860 ->
          let uu____18861 = name_not_found lid  in
          let uu____18867 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18861 uu____18867
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18887 = lookup_qname env lid  in
      match uu____18887 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18892,uvs,t,uu____18895,uu____18896,uu____18897);
              FStar_Syntax_Syntax.sigrng = uu____18898;
              FStar_Syntax_Syntax.sigquals = uu____18899;
              FStar_Syntax_Syntax.sigmeta = uu____18900;
              FStar_Syntax_Syntax.sigattrs = uu____18901;
              FStar_Syntax_Syntax.sigopts = uu____18902;_},FStar_Pervasives_Native.None
            ),uu____18903)
          ->
          let uu____18960 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18960 (uvs, t)
      | uu____18965 ->
          let uu____18966 = name_not_found lid  in
          let uu____18972 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18966 uu____18972
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18995 = lookup_qname env lid  in
      match uu____18995 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19003,uu____19004,uu____19005,uu____19006,uu____19007,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19009;
              FStar_Syntax_Syntax.sigquals = uu____19010;
              FStar_Syntax_Syntax.sigmeta = uu____19011;
              FStar_Syntax_Syntax.sigattrs = uu____19012;
              FStar_Syntax_Syntax.sigopts = uu____19013;_},uu____19014),uu____19015)
          -> (true, dcs)
      | uu____19080 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19096 = lookup_qname env lid  in
      match uu____19096 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19097,uu____19098,uu____19099,l,uu____19101,uu____19102);
              FStar_Syntax_Syntax.sigrng = uu____19103;
              FStar_Syntax_Syntax.sigquals = uu____19104;
              FStar_Syntax_Syntax.sigmeta = uu____19105;
              FStar_Syntax_Syntax.sigattrs = uu____19106;
              FStar_Syntax_Syntax.sigopts = uu____19107;_},uu____19108),uu____19109)
          -> l
      | uu____19168 ->
          let uu____19169 =
            let uu____19171 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19171  in
          failwith uu____19169
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19241)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19298) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19322 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19322
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19357 -> FStar_Pervasives_Native.None)
          | uu____19366 -> FStar_Pervasives_Native.None
  
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
        let uu____19428 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19428
  
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
        let uu____19461 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19461
  
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
             (FStar_Util.Inl uu____19513,uu____19514) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19563),uu____19564) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19613 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19631 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19641 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19658 ->
                  let uu____19665 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19665
              | FStar_Syntax_Syntax.Sig_let ((uu____19666,lbs),uu____19668)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19684 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19684
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19691 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19699 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19700 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19707 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19708 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19709 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19710 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19723 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19741 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19741
           (fun d_opt  ->
              let uu____19754 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19754
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19764 =
                   let uu____19767 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19767  in
                 match uu____19764 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19768 =
                       let uu____19770 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19770
                        in
                     failwith uu____19768
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19775 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19775
                       then
                         let uu____19778 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19780 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19782 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19778 uu____19780 uu____19782
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
        (FStar_Util.Inr (se,uu____19807),uu____19808) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19857 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19879),uu____19880) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19929 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19951 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19951
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19984 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19984 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20006 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20015 =
                        let uu____20016 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20016.FStar_Syntax_Syntax.n  in
                      match uu____20015 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20021 -> false))
               in
            (true, uu____20006)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20044 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20044
  
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
          let uu____20116 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20116.FStar_Ident.str  in
        let uu____20117 = FStar_Util.smap_try_find tab s  in
        match uu____20117 with
        | FStar_Pervasives_Native.None  ->
            let uu____20120 = f ()  in
            (match uu____20120 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20158 =
        let uu____20159 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20159 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20193 =
        let uu____20194 = FStar_Syntax_Util.unrefine t  in
        uu____20194.FStar_Syntax_Syntax.n  in
      match uu____20193 with
      | FStar_Syntax_Syntax.Tm_type uu____20198 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20202) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20228) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20233,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20255 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20288 =
        let attrs =
          let uu____20294 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20294  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20334 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20334)
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
      let uu____20379 = lookup_qname env ftv  in
      match uu____20379 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20383) ->
          let uu____20428 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20428 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20449,t),r) ->
               let uu____20464 =
                 let uu____20465 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20465 t  in
               FStar_Pervasives_Native.Some uu____20464)
      | uu____20466 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20478 = try_lookup_effect_lid env ftv  in
      match uu____20478 with
      | FStar_Pervasives_Native.None  ->
          let uu____20481 = name_not_found ftv  in
          let uu____20487 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20481 uu____20487
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
        let uu____20511 = lookup_qname env lid0  in
        match uu____20511 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20522);
                FStar_Syntax_Syntax.sigrng = uu____20523;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20525;
                FStar_Syntax_Syntax.sigattrs = uu____20526;
                FStar_Syntax_Syntax.sigopts = uu____20527;_},FStar_Pervasives_Native.None
              ),uu____20528)
            ->
            let lid1 =
              let uu____20584 =
                let uu____20585 = FStar_Ident.range_of_lid lid  in
                let uu____20586 =
                  let uu____20587 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20587  in
                FStar_Range.set_use_range uu____20585 uu____20586  in
              FStar_Ident.set_lid_range lid uu____20584  in
            let uu____20588 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20594  ->
                      match uu___6_20594 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20597 -> false))
               in
            if uu____20588
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20616 =
                      let uu____20618 =
                        let uu____20620 = get_range env  in
                        FStar_Range.string_of_range uu____20620  in
                      let uu____20621 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20623 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20618 uu____20621 uu____20623
                       in
                    failwith uu____20616)
                  in
               match (binders, univs1) with
               | ([],uu____20644) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20670,uu____20671::uu____20672::uu____20673) ->
                   let uu____20694 =
                     let uu____20696 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20698 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20696 uu____20698
                      in
                   failwith uu____20694
               | uu____20709 ->
                   let uu____20724 =
                     let uu____20729 =
                       let uu____20730 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20730)  in
                     inst_tscheme_with uu____20729 insts  in
                   (match uu____20724 with
                    | (uu____20743,t) ->
                        let t1 =
                          let uu____20746 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20746 t  in
                        let uu____20747 =
                          let uu____20748 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20748.FStar_Syntax_Syntax.n  in
                        (match uu____20747 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20783 -> failwith "Impossible")))
        | uu____20791 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20815 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20815 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20828,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20835 = find1 l2  in
            (match uu____20835 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20842 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20842 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20846 = find1 l  in
            (match uu____20846 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20851 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20851
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20866 = lookup_qname env l1  in
      match uu____20866 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20869;
              FStar_Syntax_Syntax.sigrng = uu____20870;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20872;
              FStar_Syntax_Syntax.sigattrs = uu____20873;
              FStar_Syntax_Syntax.sigopts = uu____20874;_},uu____20875),uu____20876)
          -> q
      | uu____20929 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20953 =
          let uu____20954 =
            let uu____20956 = FStar_Util.string_of_int i  in
            let uu____20958 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20956 uu____20958
             in
          failwith uu____20954  in
        let uu____20961 = lookup_datacon env lid  in
        match uu____20961 with
        | (uu____20966,t) ->
            let uu____20968 =
              let uu____20969 = FStar_Syntax_Subst.compress t  in
              uu____20969.FStar_Syntax_Syntax.n  in
            (match uu____20968 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20973) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21017 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21017
                      FStar_Pervasives_Native.fst)
             | uu____21028 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21042 = lookup_qname env l  in
      match uu____21042 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21044,uu____21045,uu____21046);
              FStar_Syntax_Syntax.sigrng = uu____21047;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21049;
              FStar_Syntax_Syntax.sigattrs = uu____21050;
              FStar_Syntax_Syntax.sigopts = uu____21051;_},uu____21052),uu____21053)
          ->
          FStar_Util.for_some
            (fun uu___7_21108  ->
               match uu___7_21108 with
               | FStar_Syntax_Syntax.Projector uu____21110 -> true
               | uu____21116 -> false) quals
      | uu____21118 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21132 = lookup_qname env lid  in
      match uu____21132 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21134,uu____21135,uu____21136,uu____21137,uu____21138,uu____21139);
              FStar_Syntax_Syntax.sigrng = uu____21140;
              FStar_Syntax_Syntax.sigquals = uu____21141;
              FStar_Syntax_Syntax.sigmeta = uu____21142;
              FStar_Syntax_Syntax.sigattrs = uu____21143;
              FStar_Syntax_Syntax.sigopts = uu____21144;_},uu____21145),uu____21146)
          -> true
      | uu____21206 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21220 = lookup_qname env lid  in
      match uu____21220 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21222,uu____21223,uu____21224,uu____21225,uu____21226,uu____21227);
              FStar_Syntax_Syntax.sigrng = uu____21228;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21230;
              FStar_Syntax_Syntax.sigattrs = uu____21231;
              FStar_Syntax_Syntax.sigopts = uu____21232;_},uu____21233),uu____21234)
          ->
          FStar_Util.for_some
            (fun uu___8_21297  ->
               match uu___8_21297 with
               | FStar_Syntax_Syntax.RecordType uu____21299 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21309 -> true
               | uu____21319 -> false) quals
      | uu____21321 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21331,uu____21332);
            FStar_Syntax_Syntax.sigrng = uu____21333;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21335;
            FStar_Syntax_Syntax.sigattrs = uu____21336;
            FStar_Syntax_Syntax.sigopts = uu____21337;_},uu____21338),uu____21339)
        ->
        FStar_Util.for_some
          (fun uu___9_21398  ->
             match uu___9_21398 with
             | FStar_Syntax_Syntax.Action uu____21400 -> true
             | uu____21402 -> false) quals
    | uu____21404 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21418 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21418
  
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
      let uu____21435 =
        let uu____21436 = FStar_Syntax_Util.un_uinst head1  in
        uu____21436.FStar_Syntax_Syntax.n  in
      match uu____21435 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21442 ->
               true
           | uu____21445 -> false)
      | uu____21447 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21461 = lookup_qname env l  in
      match uu____21461 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21464),uu____21465) ->
          FStar_Util.for_some
            (fun uu___10_21513  ->
               match uu___10_21513 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21516 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21518 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21594 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21612) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21630 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21638 ->
                 FStar_Pervasives_Native.Some true
             | uu____21657 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21660 =
        let uu____21664 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21664 mapper  in
      match uu____21660 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21724 = lookup_qname env lid  in
      match uu____21724 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21728,uu____21729,tps,uu____21731,uu____21732,uu____21733);
              FStar_Syntax_Syntax.sigrng = uu____21734;
              FStar_Syntax_Syntax.sigquals = uu____21735;
              FStar_Syntax_Syntax.sigmeta = uu____21736;
              FStar_Syntax_Syntax.sigattrs = uu____21737;
              FStar_Syntax_Syntax.sigopts = uu____21738;_},uu____21739),uu____21740)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21808 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21854  ->
              match uu____21854 with
              | (d,uu____21863) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21879 = effect_decl_opt env l  in
      match uu____21879 with
      | FStar_Pervasives_Native.None  ->
          let uu____21894 = name_not_found l  in
          let uu____21900 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21894 uu____21900
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21923  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21942  ->
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
        let uu____21974 = FStar_Ident.lid_equals l1 l2  in
        if uu____21974
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21985 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21985
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21996 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22049  ->
                        match uu____22049 with
                        | (m1,m2,uu____22063,uu____22064,uu____22065) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21996 with
              | FStar_Pervasives_Native.None  ->
                  let uu____22082 =
                    let uu____22088 =
                      let uu____22090 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____22092 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____22090
                        uu____22092
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22088)
                     in
                  FStar_Errors.raise_error uu____22082 env.range
              | FStar_Pervasives_Native.Some
                  (uu____22102,uu____22103,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22137 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22137
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
  'Auu____22157 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22157) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22186 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22212  ->
                match uu____22212 with
                | (d,uu____22219) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22186 with
      | FStar_Pervasives_Native.None  ->
          let uu____22230 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22230
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22245 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22245 with
           | (uu____22256,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22274)::(wp,uu____22276)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22332 -> failwith "Impossible"))
  
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
        | uu____22397 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22410 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22410 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22427 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22427 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22452 =
                     let uu____22458 =
                       let uu____22460 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22468 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22479 =
                         let uu____22481 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22481  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22460 uu____22468 uu____22479
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22458)
                      in
                   FStar_Errors.raise_error uu____22452
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22489 =
                     let uu____22500 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22500 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22537  ->
                        fun uu____22538  ->
                          match (uu____22537, uu____22538) with
                          | ((x,uu____22568),(t,uu____22570)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22489
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22601 =
                     let uu___1603_22602 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1603_22602.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1603_22602.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1603_22602.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1603_22602.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22601
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22614 .
    'Auu____22614 ->
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
          let uu____22644 = effect_decl_opt env effect_name  in
          match uu____22644 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22687 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22710 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22749 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22749
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22754 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22754
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____22765 =
                     let uu____22768 = get_range env  in
                     let uu____22769 =
                       let uu____22776 =
                         let uu____22777 =
                           let uu____22794 =
                             let uu____22805 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22805; wp]  in
                           (repr, uu____22794)  in
                         FStar_Syntax_Syntax.Tm_app uu____22777  in
                       FStar_Syntax_Syntax.mk uu____22776  in
                     uu____22769 FStar_Pervasives_Native.None uu____22768  in
                   FStar_Pervasives_Native.Some uu____22765)
  
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
      | uu____22949 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22964 =
        let uu____22965 = FStar_Syntax_Subst.compress t  in
        uu____22965.FStar_Syntax_Syntax.n  in
      match uu____22964 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22969,c) ->
          is_reifiable_comp env c
      | uu____22991 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23011 =
           let uu____23013 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23013  in
         if uu____23011
         then
           let uu____23016 =
             let uu____23022 =
               let uu____23024 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23024
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23022)  in
           let uu____23028 = get_range env  in
           FStar_Errors.raise_error uu____23016 uu____23028
         else ());
        (let uu____23031 = effect_repr_aux true env c u_c  in
         match uu____23031 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1668_23067 = env  in
        {
          solver = (uu___1668_23067.solver);
          range = (uu___1668_23067.range);
          curmodule = (uu___1668_23067.curmodule);
          gamma = (uu___1668_23067.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1668_23067.gamma_cache);
          modules = (uu___1668_23067.modules);
          expected_typ = (uu___1668_23067.expected_typ);
          sigtab = (uu___1668_23067.sigtab);
          attrtab = (uu___1668_23067.attrtab);
          instantiate_imp = (uu___1668_23067.instantiate_imp);
          effects = (uu___1668_23067.effects);
          generalize = (uu___1668_23067.generalize);
          letrecs = (uu___1668_23067.letrecs);
          top_level = (uu___1668_23067.top_level);
          check_uvars = (uu___1668_23067.check_uvars);
          use_eq = (uu___1668_23067.use_eq);
          is_iface = (uu___1668_23067.is_iface);
          admit = (uu___1668_23067.admit);
          lax = (uu___1668_23067.lax);
          lax_universes = (uu___1668_23067.lax_universes);
          phase1 = (uu___1668_23067.phase1);
          failhard = (uu___1668_23067.failhard);
          nosynth = (uu___1668_23067.nosynth);
          uvar_subtyping = (uu___1668_23067.uvar_subtyping);
          tc_term = (uu___1668_23067.tc_term);
          type_of = (uu___1668_23067.type_of);
          universe_of = (uu___1668_23067.universe_of);
          check_type_of = (uu___1668_23067.check_type_of);
          use_bv_sorts = (uu___1668_23067.use_bv_sorts);
          qtbl_name_and_index = (uu___1668_23067.qtbl_name_and_index);
          normalized_eff_names = (uu___1668_23067.normalized_eff_names);
          fv_delta_depths = (uu___1668_23067.fv_delta_depths);
          proof_ns = (uu___1668_23067.proof_ns);
          synth_hook = (uu___1668_23067.synth_hook);
          splice = (uu___1668_23067.splice);
          mpreprocess = (uu___1668_23067.mpreprocess);
          postprocess = (uu___1668_23067.postprocess);
          is_native_tactic = (uu___1668_23067.is_native_tactic);
          identifier_info = (uu___1668_23067.identifier_info);
          tc_hooks = (uu___1668_23067.tc_hooks);
          dsenv = (uu___1668_23067.dsenv);
          nbe = (uu___1668_23067.nbe);
          strict_args_tab = (uu___1668_23067.strict_args_tab);
          erasable_types_tab = (uu___1668_23067.erasable_types_tab)
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
    fun uu____23086  ->
      match uu____23086 with
      | (ed,quals) ->
          let effects =
            let uu___1677_23100 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1677_23100.order);
              joins = (uu___1677_23100.joins)
            }  in
          let uu___1680_23109 = env  in
          {
            solver = (uu___1680_23109.solver);
            range = (uu___1680_23109.range);
            curmodule = (uu___1680_23109.curmodule);
            gamma = (uu___1680_23109.gamma);
            gamma_sig = (uu___1680_23109.gamma_sig);
            gamma_cache = (uu___1680_23109.gamma_cache);
            modules = (uu___1680_23109.modules);
            expected_typ = (uu___1680_23109.expected_typ);
            sigtab = (uu___1680_23109.sigtab);
            attrtab = (uu___1680_23109.attrtab);
            instantiate_imp = (uu___1680_23109.instantiate_imp);
            effects;
            generalize = (uu___1680_23109.generalize);
            letrecs = (uu___1680_23109.letrecs);
            top_level = (uu___1680_23109.top_level);
            check_uvars = (uu___1680_23109.check_uvars);
            use_eq = (uu___1680_23109.use_eq);
            is_iface = (uu___1680_23109.is_iface);
            admit = (uu___1680_23109.admit);
            lax = (uu___1680_23109.lax);
            lax_universes = (uu___1680_23109.lax_universes);
            phase1 = (uu___1680_23109.phase1);
            failhard = (uu___1680_23109.failhard);
            nosynth = (uu___1680_23109.nosynth);
            uvar_subtyping = (uu___1680_23109.uvar_subtyping);
            tc_term = (uu___1680_23109.tc_term);
            type_of = (uu___1680_23109.type_of);
            universe_of = (uu___1680_23109.universe_of);
            check_type_of = (uu___1680_23109.check_type_of);
            use_bv_sorts = (uu___1680_23109.use_bv_sorts);
            qtbl_name_and_index = (uu___1680_23109.qtbl_name_and_index);
            normalized_eff_names = (uu___1680_23109.normalized_eff_names);
            fv_delta_depths = (uu___1680_23109.fv_delta_depths);
            proof_ns = (uu___1680_23109.proof_ns);
            synth_hook = (uu___1680_23109.synth_hook);
            splice = (uu___1680_23109.splice);
            mpreprocess = (uu___1680_23109.mpreprocess);
            postprocess = (uu___1680_23109.postprocess);
            is_native_tactic = (uu___1680_23109.is_native_tactic);
            identifier_info = (uu___1680_23109.identifier_info);
            tc_hooks = (uu___1680_23109.tc_hooks);
            dsenv = (uu___1680_23109.dsenv);
            nbe = (uu___1680_23109.nbe);
            strict_args_tab = (uu___1680_23109.strict_args_tab);
            erasable_types_tab = (uu___1680_23109.erasable_types_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____23149 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____23149  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____23307 = (e1.mlift).mlift_wp u t wp  in
                            let uu____23308 = l1 u t wp e  in
                            l2 u t uu____23307 uu____23308))
            | uu____23309 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____23381 = inst_tscheme_with lift_t [u]  in
        match uu____23381 with
        | (uu____23388,lift_t1) ->
            let uu____23390 =
              let uu____23397 =
                let uu____23398 =
                  let uu____23415 =
                    let uu____23426 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____23435 =
                      let uu____23446 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____23446]  in
                    uu____23426 :: uu____23435  in
                  (lift_t1, uu____23415)  in
                FStar_Syntax_Syntax.Tm_app uu____23398  in
              FStar_Syntax_Syntax.mk uu____23397  in
            uu____23390 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____23556 = inst_tscheme_with lift_t [u]  in
        match uu____23556 with
        | (uu____23563,lift_t1) ->
            let uu____23565 =
              let uu____23572 =
                let uu____23573 =
                  let uu____23590 =
                    let uu____23601 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____23610 =
                      let uu____23621 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____23630 =
                        let uu____23641 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____23641]  in
                      uu____23621 :: uu____23630  in
                    uu____23601 :: uu____23610  in
                  (lift_t1, uu____23590)  in
                FStar_Syntax_Syntax.Tm_app uu____23573  in
              FStar_Syntax_Syntax.mk uu____23572  in
            uu____23565 FStar_Pervasives_Native.None
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
          let uu____23743 =
            let uu____23744 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____23744
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____23743  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____23753 =
          let uu____23755 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____23755  in
        let uu____23756 =
          let uu____23758 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____23786 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____23786)
             in
          FStar_Util.dflt "none" uu____23758  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____23753 uu____23756
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____23815  ->
                match uu____23815 with
                | (e,uu____23823) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____23846 =
        match uu____23846 with
        | (i,j) ->
            let uu____23857 = FStar_Ident.lid_equals i j  in
            if uu____23857
            then
              FStar_All.pipe_right (id_edge i)
                (fun _23864  -> FStar_Pervasives_Native.Some _23864)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____23893 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____23903 = FStar_Ident.lid_equals i k  in
                    if uu____23903
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____23917 = FStar_Ident.lid_equals j k
                                 in
                              if uu____23917
                              then []
                              else
                                (let uu____23924 =
                                   let uu____23933 = find_edge order1 (i, k)
                                      in
                                   let uu____23936 = find_edge order1 (k, j)
                                      in
                                   (uu____23933, uu____23936)  in
                                 match uu____23924 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____23951 = compose_edges e1 e2
                                        in
                                     [uu____23951]
                                 | uu____23952 -> [])))))
             in
          FStar_List.append order1 uu____23893  in
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
              let uu____23982 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____23985 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____23985
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____23982
              then
                let uu____23992 =
                  let uu____23998 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____23998)
                   in
                let uu____24002 = get_range env  in
                FStar_Errors.raise_error uu____23992 uu____24002
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____24080 = FStar_Ident.lid_equals i j  in
                           if uu____24080
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____24132 =
                                         let uu____24141 =
                                           find_edge order2 (i, k)  in
                                         let uu____24144 =
                                           find_edge order2 (j, k)  in
                                         (uu____24141, uu____24144)  in
                                       match uu____24132 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____24186,uu____24187)
                                                ->
                                                let uu____24194 =
                                                  let uu____24201 =
                                                    let uu____24203 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____24203
                                                     in
                                                  let uu____24206 =
                                                    let uu____24208 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____24208
                                                     in
                                                  (uu____24201, uu____24206)
                                                   in
                                                (match uu____24194 with
                                                 | (true ,true ) ->
                                                     let uu____24225 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____24225
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
                                       | uu____24268 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1807_24341 = env.effects  in
         { decls = (uu___1807_24341.decls); order = order2; joins }  in
       let uu___1810_24342 = env  in
       {
         solver = (uu___1810_24342.solver);
         range = (uu___1810_24342.range);
         curmodule = (uu___1810_24342.curmodule);
         gamma = (uu___1810_24342.gamma);
         gamma_sig = (uu___1810_24342.gamma_sig);
         gamma_cache = (uu___1810_24342.gamma_cache);
         modules = (uu___1810_24342.modules);
         expected_typ = (uu___1810_24342.expected_typ);
         sigtab = (uu___1810_24342.sigtab);
         attrtab = (uu___1810_24342.attrtab);
         instantiate_imp = (uu___1810_24342.instantiate_imp);
         effects;
         generalize = (uu___1810_24342.generalize);
         letrecs = (uu___1810_24342.letrecs);
         top_level = (uu___1810_24342.top_level);
         check_uvars = (uu___1810_24342.check_uvars);
         use_eq = (uu___1810_24342.use_eq);
         is_iface = (uu___1810_24342.is_iface);
         admit = (uu___1810_24342.admit);
         lax = (uu___1810_24342.lax);
         lax_universes = (uu___1810_24342.lax_universes);
         phase1 = (uu___1810_24342.phase1);
         failhard = (uu___1810_24342.failhard);
         nosynth = (uu___1810_24342.nosynth);
         uvar_subtyping = (uu___1810_24342.uvar_subtyping);
         tc_term = (uu___1810_24342.tc_term);
         type_of = (uu___1810_24342.type_of);
         universe_of = (uu___1810_24342.universe_of);
         check_type_of = (uu___1810_24342.check_type_of);
         use_bv_sorts = (uu___1810_24342.use_bv_sorts);
         qtbl_name_and_index = (uu___1810_24342.qtbl_name_and_index);
         normalized_eff_names = (uu___1810_24342.normalized_eff_names);
         fv_delta_depths = (uu___1810_24342.fv_delta_depths);
         proof_ns = (uu___1810_24342.proof_ns);
         synth_hook = (uu___1810_24342.synth_hook);
         splice = (uu___1810_24342.splice);
         mpreprocess = (uu___1810_24342.mpreprocess);
         postprocess = (uu___1810_24342.postprocess);
         is_native_tactic = (uu___1810_24342.is_native_tactic);
         identifier_info = (uu___1810_24342.identifier_info);
         tc_hooks = (uu___1810_24342.tc_hooks);
         dsenv = (uu___1810_24342.dsenv);
         nbe = (uu___1810_24342.nbe);
         strict_args_tab = (uu___1810_24342.strict_args_tab);
         erasable_types_tab = (uu___1810_24342.erasable_types_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1814_24354 = env  in
      {
        solver = (uu___1814_24354.solver);
        range = (uu___1814_24354.range);
        curmodule = (uu___1814_24354.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1814_24354.gamma_sig);
        gamma_cache = (uu___1814_24354.gamma_cache);
        modules = (uu___1814_24354.modules);
        expected_typ = (uu___1814_24354.expected_typ);
        sigtab = (uu___1814_24354.sigtab);
        attrtab = (uu___1814_24354.attrtab);
        instantiate_imp = (uu___1814_24354.instantiate_imp);
        effects = (uu___1814_24354.effects);
        generalize = (uu___1814_24354.generalize);
        letrecs = (uu___1814_24354.letrecs);
        top_level = (uu___1814_24354.top_level);
        check_uvars = (uu___1814_24354.check_uvars);
        use_eq = (uu___1814_24354.use_eq);
        is_iface = (uu___1814_24354.is_iface);
        admit = (uu___1814_24354.admit);
        lax = (uu___1814_24354.lax);
        lax_universes = (uu___1814_24354.lax_universes);
        phase1 = (uu___1814_24354.phase1);
        failhard = (uu___1814_24354.failhard);
        nosynth = (uu___1814_24354.nosynth);
        uvar_subtyping = (uu___1814_24354.uvar_subtyping);
        tc_term = (uu___1814_24354.tc_term);
        type_of = (uu___1814_24354.type_of);
        universe_of = (uu___1814_24354.universe_of);
        check_type_of = (uu___1814_24354.check_type_of);
        use_bv_sorts = (uu___1814_24354.use_bv_sorts);
        qtbl_name_and_index = (uu___1814_24354.qtbl_name_and_index);
        normalized_eff_names = (uu___1814_24354.normalized_eff_names);
        fv_delta_depths = (uu___1814_24354.fv_delta_depths);
        proof_ns = (uu___1814_24354.proof_ns);
        synth_hook = (uu___1814_24354.synth_hook);
        splice = (uu___1814_24354.splice);
        mpreprocess = (uu___1814_24354.mpreprocess);
        postprocess = (uu___1814_24354.postprocess);
        is_native_tactic = (uu___1814_24354.is_native_tactic);
        identifier_info = (uu___1814_24354.identifier_info);
        tc_hooks = (uu___1814_24354.tc_hooks);
        dsenv = (uu___1814_24354.dsenv);
        nbe = (uu___1814_24354.nbe);
        strict_args_tab = (uu___1814_24354.strict_args_tab);
        erasable_types_tab = (uu___1814_24354.erasable_types_tab)
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
            (let uu___1827_24412 = env  in
             {
               solver = (uu___1827_24412.solver);
               range = (uu___1827_24412.range);
               curmodule = (uu___1827_24412.curmodule);
               gamma = rest;
               gamma_sig = (uu___1827_24412.gamma_sig);
               gamma_cache = (uu___1827_24412.gamma_cache);
               modules = (uu___1827_24412.modules);
               expected_typ = (uu___1827_24412.expected_typ);
               sigtab = (uu___1827_24412.sigtab);
               attrtab = (uu___1827_24412.attrtab);
               instantiate_imp = (uu___1827_24412.instantiate_imp);
               effects = (uu___1827_24412.effects);
               generalize = (uu___1827_24412.generalize);
               letrecs = (uu___1827_24412.letrecs);
               top_level = (uu___1827_24412.top_level);
               check_uvars = (uu___1827_24412.check_uvars);
               use_eq = (uu___1827_24412.use_eq);
               is_iface = (uu___1827_24412.is_iface);
               admit = (uu___1827_24412.admit);
               lax = (uu___1827_24412.lax);
               lax_universes = (uu___1827_24412.lax_universes);
               phase1 = (uu___1827_24412.phase1);
               failhard = (uu___1827_24412.failhard);
               nosynth = (uu___1827_24412.nosynth);
               uvar_subtyping = (uu___1827_24412.uvar_subtyping);
               tc_term = (uu___1827_24412.tc_term);
               type_of = (uu___1827_24412.type_of);
               universe_of = (uu___1827_24412.universe_of);
               check_type_of = (uu___1827_24412.check_type_of);
               use_bv_sorts = (uu___1827_24412.use_bv_sorts);
               qtbl_name_and_index = (uu___1827_24412.qtbl_name_and_index);
               normalized_eff_names = (uu___1827_24412.normalized_eff_names);
               fv_delta_depths = (uu___1827_24412.fv_delta_depths);
               proof_ns = (uu___1827_24412.proof_ns);
               synth_hook = (uu___1827_24412.synth_hook);
               splice = (uu___1827_24412.splice);
               mpreprocess = (uu___1827_24412.mpreprocess);
               postprocess = (uu___1827_24412.postprocess);
               is_native_tactic = (uu___1827_24412.is_native_tactic);
               identifier_info = (uu___1827_24412.identifier_info);
               tc_hooks = (uu___1827_24412.tc_hooks);
               dsenv = (uu___1827_24412.dsenv);
               nbe = (uu___1827_24412.nbe);
               strict_args_tab = (uu___1827_24412.strict_args_tab);
               erasable_types_tab = (uu___1827_24412.erasable_types_tab)
             }))
    | uu____24413 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24442  ->
             match uu____24442 with | (x,uu____24450) -> push_bv env1 x) env
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
            let uu___1841_24485 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1841_24485.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1841_24485.FStar_Syntax_Syntax.index);
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
        let uu____24558 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24558 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24586 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24586)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1862_24602 = env  in
      {
        solver = (uu___1862_24602.solver);
        range = (uu___1862_24602.range);
        curmodule = (uu___1862_24602.curmodule);
        gamma = (uu___1862_24602.gamma);
        gamma_sig = (uu___1862_24602.gamma_sig);
        gamma_cache = (uu___1862_24602.gamma_cache);
        modules = (uu___1862_24602.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1862_24602.sigtab);
        attrtab = (uu___1862_24602.attrtab);
        instantiate_imp = (uu___1862_24602.instantiate_imp);
        effects = (uu___1862_24602.effects);
        generalize = (uu___1862_24602.generalize);
        letrecs = (uu___1862_24602.letrecs);
        top_level = (uu___1862_24602.top_level);
        check_uvars = (uu___1862_24602.check_uvars);
        use_eq = false;
        is_iface = (uu___1862_24602.is_iface);
        admit = (uu___1862_24602.admit);
        lax = (uu___1862_24602.lax);
        lax_universes = (uu___1862_24602.lax_universes);
        phase1 = (uu___1862_24602.phase1);
        failhard = (uu___1862_24602.failhard);
        nosynth = (uu___1862_24602.nosynth);
        uvar_subtyping = (uu___1862_24602.uvar_subtyping);
        tc_term = (uu___1862_24602.tc_term);
        type_of = (uu___1862_24602.type_of);
        universe_of = (uu___1862_24602.universe_of);
        check_type_of = (uu___1862_24602.check_type_of);
        use_bv_sorts = (uu___1862_24602.use_bv_sorts);
        qtbl_name_and_index = (uu___1862_24602.qtbl_name_and_index);
        normalized_eff_names = (uu___1862_24602.normalized_eff_names);
        fv_delta_depths = (uu___1862_24602.fv_delta_depths);
        proof_ns = (uu___1862_24602.proof_ns);
        synth_hook = (uu___1862_24602.synth_hook);
        splice = (uu___1862_24602.splice);
        mpreprocess = (uu___1862_24602.mpreprocess);
        postprocess = (uu___1862_24602.postprocess);
        is_native_tactic = (uu___1862_24602.is_native_tactic);
        identifier_info = (uu___1862_24602.identifier_info);
        tc_hooks = (uu___1862_24602.tc_hooks);
        dsenv = (uu___1862_24602.dsenv);
        nbe = (uu___1862_24602.nbe);
        strict_args_tab = (uu___1862_24602.strict_args_tab);
        erasable_types_tab = (uu___1862_24602.erasable_types_tab)
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
    let uu____24633 = expected_typ env_  in
    ((let uu___1869_24639 = env_  in
      {
        solver = (uu___1869_24639.solver);
        range = (uu___1869_24639.range);
        curmodule = (uu___1869_24639.curmodule);
        gamma = (uu___1869_24639.gamma);
        gamma_sig = (uu___1869_24639.gamma_sig);
        gamma_cache = (uu___1869_24639.gamma_cache);
        modules = (uu___1869_24639.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1869_24639.sigtab);
        attrtab = (uu___1869_24639.attrtab);
        instantiate_imp = (uu___1869_24639.instantiate_imp);
        effects = (uu___1869_24639.effects);
        generalize = (uu___1869_24639.generalize);
        letrecs = (uu___1869_24639.letrecs);
        top_level = (uu___1869_24639.top_level);
        check_uvars = (uu___1869_24639.check_uvars);
        use_eq = false;
        is_iface = (uu___1869_24639.is_iface);
        admit = (uu___1869_24639.admit);
        lax = (uu___1869_24639.lax);
        lax_universes = (uu___1869_24639.lax_universes);
        phase1 = (uu___1869_24639.phase1);
        failhard = (uu___1869_24639.failhard);
        nosynth = (uu___1869_24639.nosynth);
        uvar_subtyping = (uu___1869_24639.uvar_subtyping);
        tc_term = (uu___1869_24639.tc_term);
        type_of = (uu___1869_24639.type_of);
        universe_of = (uu___1869_24639.universe_of);
        check_type_of = (uu___1869_24639.check_type_of);
        use_bv_sorts = (uu___1869_24639.use_bv_sorts);
        qtbl_name_and_index = (uu___1869_24639.qtbl_name_and_index);
        normalized_eff_names = (uu___1869_24639.normalized_eff_names);
        fv_delta_depths = (uu___1869_24639.fv_delta_depths);
        proof_ns = (uu___1869_24639.proof_ns);
        synth_hook = (uu___1869_24639.synth_hook);
        splice = (uu___1869_24639.splice);
        mpreprocess = (uu___1869_24639.mpreprocess);
        postprocess = (uu___1869_24639.postprocess);
        is_native_tactic = (uu___1869_24639.is_native_tactic);
        identifier_info = (uu___1869_24639.identifier_info);
        tc_hooks = (uu___1869_24639.tc_hooks);
        dsenv = (uu___1869_24639.dsenv);
        nbe = (uu___1869_24639.nbe);
        strict_args_tab = (uu___1869_24639.strict_args_tab);
        erasable_types_tab = (uu___1869_24639.erasable_types_tab)
      }), uu____24633)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24651 =
      let uu____24654 = FStar_Ident.id_of_text ""  in [uu____24654]  in
    FStar_Ident.lid_of_ids uu____24651  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24661 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24661
        then
          let uu____24666 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24666 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1877_24694 = env  in
       {
         solver = (uu___1877_24694.solver);
         range = (uu___1877_24694.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1877_24694.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1877_24694.expected_typ);
         sigtab = (uu___1877_24694.sigtab);
         attrtab = (uu___1877_24694.attrtab);
         instantiate_imp = (uu___1877_24694.instantiate_imp);
         effects = (uu___1877_24694.effects);
         generalize = (uu___1877_24694.generalize);
         letrecs = (uu___1877_24694.letrecs);
         top_level = (uu___1877_24694.top_level);
         check_uvars = (uu___1877_24694.check_uvars);
         use_eq = (uu___1877_24694.use_eq);
         is_iface = (uu___1877_24694.is_iface);
         admit = (uu___1877_24694.admit);
         lax = (uu___1877_24694.lax);
         lax_universes = (uu___1877_24694.lax_universes);
         phase1 = (uu___1877_24694.phase1);
         failhard = (uu___1877_24694.failhard);
         nosynth = (uu___1877_24694.nosynth);
         uvar_subtyping = (uu___1877_24694.uvar_subtyping);
         tc_term = (uu___1877_24694.tc_term);
         type_of = (uu___1877_24694.type_of);
         universe_of = (uu___1877_24694.universe_of);
         check_type_of = (uu___1877_24694.check_type_of);
         use_bv_sorts = (uu___1877_24694.use_bv_sorts);
         qtbl_name_and_index = (uu___1877_24694.qtbl_name_and_index);
         normalized_eff_names = (uu___1877_24694.normalized_eff_names);
         fv_delta_depths = (uu___1877_24694.fv_delta_depths);
         proof_ns = (uu___1877_24694.proof_ns);
         synth_hook = (uu___1877_24694.synth_hook);
         splice = (uu___1877_24694.splice);
         mpreprocess = (uu___1877_24694.mpreprocess);
         postprocess = (uu___1877_24694.postprocess);
         is_native_tactic = (uu___1877_24694.is_native_tactic);
         identifier_info = (uu___1877_24694.identifier_info);
         tc_hooks = (uu___1877_24694.tc_hooks);
         dsenv = (uu___1877_24694.dsenv);
         nbe = (uu___1877_24694.nbe);
         strict_args_tab = (uu___1877_24694.strict_args_tab);
         erasable_types_tab = (uu___1877_24694.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24746)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24750,(uu____24751,t)))::tl1
          ->
          let uu____24772 =
            let uu____24775 = FStar_Syntax_Free.uvars t  in
            ext out uu____24775  in
          aux uu____24772 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24778;
            FStar_Syntax_Syntax.index = uu____24779;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24787 =
            let uu____24790 = FStar_Syntax_Free.uvars t  in
            ext out uu____24790  in
          aux uu____24787 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24848)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24852,(uu____24853,t)))::tl1
          ->
          let uu____24874 =
            let uu____24877 = FStar_Syntax_Free.univs t  in
            ext out uu____24877  in
          aux uu____24874 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24880;
            FStar_Syntax_Syntax.index = uu____24881;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24889 =
            let uu____24892 = FStar_Syntax_Free.univs t  in
            ext out uu____24892  in
          aux uu____24889 tl1
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
          let uu____24954 = FStar_Util.set_add uname out  in
          aux uu____24954 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24957,(uu____24958,t)))::tl1
          ->
          let uu____24979 =
            let uu____24982 = FStar_Syntax_Free.univnames t  in
            ext out uu____24982  in
          aux uu____24979 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24985;
            FStar_Syntax_Syntax.index = uu____24986;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24994 =
            let uu____24997 = FStar_Syntax_Free.univnames t  in
            ext out uu____24997  in
          aux uu____24994 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_25018  ->
            match uu___11_25018 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____25022 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____25035 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____25046 =
      let uu____25055 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____25055
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____25046 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____25103 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_25116  ->
              match uu___12_25116 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____25119 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____25119
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____25125) ->
                  let uu____25142 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____25142))
       in
    FStar_All.pipe_right uu____25103 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_25156  ->
    match uu___13_25156 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____25162 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____25162
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____25185  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____25240) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25273,uu____25274) -> false  in
      let uu____25288 =
        FStar_List.tryFind
          (fun uu____25310  ->
             match uu____25310 with | (p,uu____25321) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25288 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25340,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25370 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25370
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2020_25392 = e  in
        {
          solver = (uu___2020_25392.solver);
          range = (uu___2020_25392.range);
          curmodule = (uu___2020_25392.curmodule);
          gamma = (uu___2020_25392.gamma);
          gamma_sig = (uu___2020_25392.gamma_sig);
          gamma_cache = (uu___2020_25392.gamma_cache);
          modules = (uu___2020_25392.modules);
          expected_typ = (uu___2020_25392.expected_typ);
          sigtab = (uu___2020_25392.sigtab);
          attrtab = (uu___2020_25392.attrtab);
          instantiate_imp = (uu___2020_25392.instantiate_imp);
          effects = (uu___2020_25392.effects);
          generalize = (uu___2020_25392.generalize);
          letrecs = (uu___2020_25392.letrecs);
          top_level = (uu___2020_25392.top_level);
          check_uvars = (uu___2020_25392.check_uvars);
          use_eq = (uu___2020_25392.use_eq);
          is_iface = (uu___2020_25392.is_iface);
          admit = (uu___2020_25392.admit);
          lax = (uu___2020_25392.lax);
          lax_universes = (uu___2020_25392.lax_universes);
          phase1 = (uu___2020_25392.phase1);
          failhard = (uu___2020_25392.failhard);
          nosynth = (uu___2020_25392.nosynth);
          uvar_subtyping = (uu___2020_25392.uvar_subtyping);
          tc_term = (uu___2020_25392.tc_term);
          type_of = (uu___2020_25392.type_of);
          universe_of = (uu___2020_25392.universe_of);
          check_type_of = (uu___2020_25392.check_type_of);
          use_bv_sorts = (uu___2020_25392.use_bv_sorts);
          qtbl_name_and_index = (uu___2020_25392.qtbl_name_and_index);
          normalized_eff_names = (uu___2020_25392.normalized_eff_names);
          fv_delta_depths = (uu___2020_25392.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2020_25392.synth_hook);
          splice = (uu___2020_25392.splice);
          mpreprocess = (uu___2020_25392.mpreprocess);
          postprocess = (uu___2020_25392.postprocess);
          is_native_tactic = (uu___2020_25392.is_native_tactic);
          identifier_info = (uu___2020_25392.identifier_info);
          tc_hooks = (uu___2020_25392.tc_hooks);
          dsenv = (uu___2020_25392.dsenv);
          nbe = (uu___2020_25392.nbe);
          strict_args_tab = (uu___2020_25392.strict_args_tab);
          erasable_types_tab = (uu___2020_25392.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2029_25440 = e  in
      {
        solver = (uu___2029_25440.solver);
        range = (uu___2029_25440.range);
        curmodule = (uu___2029_25440.curmodule);
        gamma = (uu___2029_25440.gamma);
        gamma_sig = (uu___2029_25440.gamma_sig);
        gamma_cache = (uu___2029_25440.gamma_cache);
        modules = (uu___2029_25440.modules);
        expected_typ = (uu___2029_25440.expected_typ);
        sigtab = (uu___2029_25440.sigtab);
        attrtab = (uu___2029_25440.attrtab);
        instantiate_imp = (uu___2029_25440.instantiate_imp);
        effects = (uu___2029_25440.effects);
        generalize = (uu___2029_25440.generalize);
        letrecs = (uu___2029_25440.letrecs);
        top_level = (uu___2029_25440.top_level);
        check_uvars = (uu___2029_25440.check_uvars);
        use_eq = (uu___2029_25440.use_eq);
        is_iface = (uu___2029_25440.is_iface);
        admit = (uu___2029_25440.admit);
        lax = (uu___2029_25440.lax);
        lax_universes = (uu___2029_25440.lax_universes);
        phase1 = (uu___2029_25440.phase1);
        failhard = (uu___2029_25440.failhard);
        nosynth = (uu___2029_25440.nosynth);
        uvar_subtyping = (uu___2029_25440.uvar_subtyping);
        tc_term = (uu___2029_25440.tc_term);
        type_of = (uu___2029_25440.type_of);
        universe_of = (uu___2029_25440.universe_of);
        check_type_of = (uu___2029_25440.check_type_of);
        use_bv_sorts = (uu___2029_25440.use_bv_sorts);
        qtbl_name_and_index = (uu___2029_25440.qtbl_name_and_index);
        normalized_eff_names = (uu___2029_25440.normalized_eff_names);
        fv_delta_depths = (uu___2029_25440.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2029_25440.synth_hook);
        splice = (uu___2029_25440.splice);
        mpreprocess = (uu___2029_25440.mpreprocess);
        postprocess = (uu___2029_25440.postprocess);
        is_native_tactic = (uu___2029_25440.is_native_tactic);
        identifier_info = (uu___2029_25440.identifier_info);
        tc_hooks = (uu___2029_25440.tc_hooks);
        dsenv = (uu___2029_25440.dsenv);
        nbe = (uu___2029_25440.nbe);
        strict_args_tab = (uu___2029_25440.strict_args_tab);
        erasable_types_tab = (uu___2029_25440.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25456 = FStar_Syntax_Free.names t  in
      let uu____25459 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25456 uu____25459
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25482 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25482
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25492 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25492
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25513 =
      match uu____25513 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25533 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25533)
       in
    let uu____25541 =
      let uu____25545 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25545 FStar_List.rev  in
    FStar_All.pipe_right uu____25541 (FStar_String.concat " ")
  
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
                  (let uu____25615 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25615 with
                   | FStar_Pervasives_Native.Some uu____25619 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25622 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____25632;
        univ_ineqs = uu____25633; implicits = uu____25634;_} -> true
    | uu____25646 -> false
  
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
          let uu___2073_25677 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2073_25677.deferred);
            univ_ineqs = (uu___2073_25677.univ_ineqs);
            implicits = (uu___2073_25677.implicits)
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
          let uu____25716 = FStar_Options.defensive ()  in
          if uu____25716
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25722 =
              let uu____25724 =
                let uu____25726 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25726  in
              Prims.op_Negation uu____25724  in
            (if uu____25722
             then
               let uu____25733 =
                 let uu____25739 =
                   let uu____25741 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25743 =
                     let uu____25745 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25745
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25741 uu____25743
                    in
                 (FStar_Errors.Warning_Defensive, uu____25739)  in
               FStar_Errors.log_issue rng uu____25733
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
          let uu____25785 =
            let uu____25787 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25787  in
          if uu____25785
          then ()
          else
            (let uu____25792 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25792 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25818 =
            let uu____25820 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25820  in
          if uu____25818
          then ()
          else
            (let uu____25825 = bound_vars e  in
             def_check_closed_in rng msg uu____25825 t)
  
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
          let uu___2110_25864 = g  in
          let uu____25865 =
            let uu____25866 =
              let uu____25867 =
                let uu____25874 =
                  let uu____25875 =
                    let uu____25892 =
                      let uu____25903 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25903]  in
                    (f, uu____25892)  in
                  FStar_Syntax_Syntax.Tm_app uu____25875  in
                FStar_Syntax_Syntax.mk uu____25874  in
              uu____25867 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25940  -> FStar_TypeChecker_Common.NonTrivial _25940)
              uu____25866
             in
          {
            guard_f = uu____25865;
            deferred = (uu___2110_25864.deferred);
            univ_ineqs = (uu___2110_25864.univ_ineqs);
            implicits = (uu___2110_25864.implicits)
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
          let uu___2117_25958 = g  in
          let uu____25959 =
            let uu____25960 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25960  in
          {
            guard_f = uu____25959;
            deferred = (uu___2117_25958.deferred);
            univ_ineqs = (uu___2117_25958.univ_ineqs);
            implicits = (uu___2117_25958.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2122_25977 = g  in
          let uu____25978 =
            let uu____25979 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25979  in
          {
            guard_f = uu____25978;
            deferred = (uu___2122_25977.deferred);
            univ_ineqs = (uu___2122_25977.univ_ineqs);
            implicits = (uu___2122_25977.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2126_25981 = g  in
          let uu____25982 =
            let uu____25983 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25983  in
          {
            guard_f = uu____25982;
            deferred = (uu___2126_25981.deferred);
            univ_ineqs = (uu___2126_25981.univ_ineqs);
            implicits = (uu___2126_25981.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25990 ->
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
          let uu____26007 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____26007
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____26014 =
      let uu____26015 = FStar_Syntax_Util.unmeta t  in
      uu____26015.FStar_Syntax_Syntax.n  in
    match uu____26014 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____26019 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____26062 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____26062;
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
                       let uu____26157 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____26157
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2181_26164 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2181_26164.deferred);
              univ_ineqs = (uu___2181_26164.univ_ineqs);
              implicits = (uu___2181_26164.implicits)
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
               let uu____26198 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____26198
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
            let uu___2196_26225 = g  in
            let uu____26226 =
              let uu____26227 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____26227  in
            {
              guard_f = uu____26226;
              deferred = (uu___2196_26225.deferred);
              univ_ineqs = (uu___2196_26225.univ_ineqs);
              implicits = (uu___2196_26225.implicits)
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
              let uu____26285 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26285 with
              | FStar_Pervasives_Native.Some
                  (uu____26310::(tm,uu____26312)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26376 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26394 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26394;
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
                      let uu___2218_26426 = trivial_guard  in
                      {
                        guard_f = (uu___2218_26426.guard_f);
                        deferred = (uu___2218_26426.deferred);
                        univ_ineqs = (uu___2218_26426.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26444  -> ());
    push = (fun uu____26446  -> ());
    pop = (fun uu____26449  -> ());
    snapshot =
      (fun uu____26452  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26471  -> fun uu____26472  -> ());
    encode_sig = (fun uu____26487  -> fun uu____26488  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26494 =
             let uu____26501 = FStar_Options.peek ()  in (e, g, uu____26501)
              in
           [uu____26494]);
    solve = (fun uu____26517  -> fun uu____26518  -> fun uu____26519  -> ());
    finish = (fun uu____26526  -> ());
    refresh = (fun uu____26528  -> ())
  } 