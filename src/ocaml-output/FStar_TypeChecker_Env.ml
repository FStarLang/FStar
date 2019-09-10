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
  fun projectee  -> match projectee with | Beta  -> true | uu____109 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____120 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____131 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____143 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____161 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____172 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____183 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____194 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____205 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____216 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____228 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____249 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____276 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____303 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____327 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____338 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____349 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____360 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____371 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____382 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____393 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____404 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____415 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____426 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____437 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____448 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____459 -> false
  
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
      | uu____519 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____545 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____556 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____567 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____579 -> false
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        curmodule
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        gamma_cache
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        modules
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        expected_typ
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        sigtab
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        uvar_subtyping
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        tc_term
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        type_of
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        universe_of
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        qtbl_name_and_index
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        normalized_eff_names
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        synth_hook
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        splice1
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        postprocess
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        is_native_tactic
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        dsenv
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        nbe1
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        strict_args_tab
  
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
           (fun uu___0_12072  ->
              match uu___0_12072 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12075 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12075  in
                  let uu____12076 =
                    let uu____12077 = FStar_Syntax_Subst.compress y  in
                    uu____12077.FStar_Syntax_Syntax.n  in
                  (match uu____12076 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12081 =
                         let uu___329_12082 = y1  in
                         let uu____12083 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___329_12082.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___329_12082.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12083
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12081
                   | uu____12086 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___335_12100 = env  in
      let uu____12101 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___335_12100.solver);
        range = (uu___335_12100.range);
        curmodule = (uu___335_12100.curmodule);
        gamma = uu____12101;
        gamma_sig = (uu___335_12100.gamma_sig);
        gamma_cache = (uu___335_12100.gamma_cache);
        modules = (uu___335_12100.modules);
        expected_typ = (uu___335_12100.expected_typ);
        sigtab = (uu___335_12100.sigtab);
        attrtab = (uu___335_12100.attrtab);
        instantiate_imp = (uu___335_12100.instantiate_imp);
        effects = (uu___335_12100.effects);
        generalize = (uu___335_12100.generalize);
        letrecs = (uu___335_12100.letrecs);
        top_level = (uu___335_12100.top_level);
        check_uvars = (uu___335_12100.check_uvars);
        use_eq = (uu___335_12100.use_eq);
        is_iface = (uu___335_12100.is_iface);
        admit = (uu___335_12100.admit);
        lax = (uu___335_12100.lax);
        lax_universes = (uu___335_12100.lax_universes);
        phase1 = (uu___335_12100.phase1);
        failhard = (uu___335_12100.failhard);
        nosynth = (uu___335_12100.nosynth);
        uvar_subtyping = (uu___335_12100.uvar_subtyping);
        tc_term = (uu___335_12100.tc_term);
        type_of = (uu___335_12100.type_of);
        universe_of = (uu___335_12100.universe_of);
        check_type_of = (uu___335_12100.check_type_of);
        use_bv_sorts = (uu___335_12100.use_bv_sorts);
        qtbl_name_and_index = (uu___335_12100.qtbl_name_and_index);
        normalized_eff_names = (uu___335_12100.normalized_eff_names);
        fv_delta_depths = (uu___335_12100.fv_delta_depths);
        proof_ns = (uu___335_12100.proof_ns);
        synth_hook = (uu___335_12100.synth_hook);
        splice = (uu___335_12100.splice);
        postprocess = (uu___335_12100.postprocess);
        is_native_tactic = (uu___335_12100.is_native_tactic);
        identifier_info = (uu___335_12100.identifier_info);
        tc_hooks = (uu___335_12100.tc_hooks);
        dsenv = (uu___335_12100.dsenv);
        nbe = (uu___335_12100.nbe);
        strict_args_tab = (uu___335_12100.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12109  -> fun uu____12110  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___342_12132 = env  in
      {
        solver = (uu___342_12132.solver);
        range = (uu___342_12132.range);
        curmodule = (uu___342_12132.curmodule);
        gamma = (uu___342_12132.gamma);
        gamma_sig = (uu___342_12132.gamma_sig);
        gamma_cache = (uu___342_12132.gamma_cache);
        modules = (uu___342_12132.modules);
        expected_typ = (uu___342_12132.expected_typ);
        sigtab = (uu___342_12132.sigtab);
        attrtab = (uu___342_12132.attrtab);
        instantiate_imp = (uu___342_12132.instantiate_imp);
        effects = (uu___342_12132.effects);
        generalize = (uu___342_12132.generalize);
        letrecs = (uu___342_12132.letrecs);
        top_level = (uu___342_12132.top_level);
        check_uvars = (uu___342_12132.check_uvars);
        use_eq = (uu___342_12132.use_eq);
        is_iface = (uu___342_12132.is_iface);
        admit = (uu___342_12132.admit);
        lax = (uu___342_12132.lax);
        lax_universes = (uu___342_12132.lax_universes);
        phase1 = (uu___342_12132.phase1);
        failhard = (uu___342_12132.failhard);
        nosynth = (uu___342_12132.nosynth);
        uvar_subtyping = (uu___342_12132.uvar_subtyping);
        tc_term = (uu___342_12132.tc_term);
        type_of = (uu___342_12132.type_of);
        universe_of = (uu___342_12132.universe_of);
        check_type_of = (uu___342_12132.check_type_of);
        use_bv_sorts = (uu___342_12132.use_bv_sorts);
        qtbl_name_and_index = (uu___342_12132.qtbl_name_and_index);
        normalized_eff_names = (uu___342_12132.normalized_eff_names);
        fv_delta_depths = (uu___342_12132.fv_delta_depths);
        proof_ns = (uu___342_12132.proof_ns);
        synth_hook = (uu___342_12132.synth_hook);
        splice = (uu___342_12132.splice);
        postprocess = (uu___342_12132.postprocess);
        is_native_tactic = (uu___342_12132.is_native_tactic);
        identifier_info = (uu___342_12132.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___342_12132.dsenv);
        nbe = (uu___342_12132.nbe);
        strict_args_tab = (uu___342_12132.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___346_12144 = e  in
      let uu____12145 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___346_12144.solver);
        range = (uu___346_12144.range);
        curmodule = (uu___346_12144.curmodule);
        gamma = (uu___346_12144.gamma);
        gamma_sig = (uu___346_12144.gamma_sig);
        gamma_cache = (uu___346_12144.gamma_cache);
        modules = (uu___346_12144.modules);
        expected_typ = (uu___346_12144.expected_typ);
        sigtab = (uu___346_12144.sigtab);
        attrtab = (uu___346_12144.attrtab);
        instantiate_imp = (uu___346_12144.instantiate_imp);
        effects = (uu___346_12144.effects);
        generalize = (uu___346_12144.generalize);
        letrecs = (uu___346_12144.letrecs);
        top_level = (uu___346_12144.top_level);
        check_uvars = (uu___346_12144.check_uvars);
        use_eq = (uu___346_12144.use_eq);
        is_iface = (uu___346_12144.is_iface);
        admit = (uu___346_12144.admit);
        lax = (uu___346_12144.lax);
        lax_universes = (uu___346_12144.lax_universes);
        phase1 = (uu___346_12144.phase1);
        failhard = (uu___346_12144.failhard);
        nosynth = (uu___346_12144.nosynth);
        uvar_subtyping = (uu___346_12144.uvar_subtyping);
        tc_term = (uu___346_12144.tc_term);
        type_of = (uu___346_12144.type_of);
        universe_of = (uu___346_12144.universe_of);
        check_type_of = (uu___346_12144.check_type_of);
        use_bv_sorts = (uu___346_12144.use_bv_sorts);
        qtbl_name_and_index = (uu___346_12144.qtbl_name_and_index);
        normalized_eff_names = (uu___346_12144.normalized_eff_names);
        fv_delta_depths = (uu___346_12144.fv_delta_depths);
        proof_ns = (uu___346_12144.proof_ns);
        synth_hook = (uu___346_12144.synth_hook);
        splice = (uu___346_12144.splice);
        postprocess = (uu___346_12144.postprocess);
        is_native_tactic = (uu___346_12144.is_native_tactic);
        identifier_info = (uu___346_12144.identifier_info);
        tc_hooks = (uu___346_12144.tc_hooks);
        dsenv = uu____12145;
        nbe = (uu___346_12144.nbe);
        strict_args_tab = (uu___346_12144.strict_args_tab)
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
      | (NoDelta ,uu____12174) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12177,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12179,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12182 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12196 . unit -> 'Auu____12196 FStar_Util.smap =
  fun uu____12203  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12209 . unit -> 'Auu____12209 FStar_Util.smap =
  fun uu____12216  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____12354 = new_gamma_cache ()  in
                  let uu____12357 = new_sigtab ()  in
                  let uu____12360 = new_sigtab ()  in
                  let uu____12367 =
                    let uu____12382 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____12382, FStar_Pervasives_Native.None)  in
                  let uu____12403 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12407 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____12411 = FStar_Options.using_facts_from ()  in
                  let uu____12412 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12415 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____12416 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12354;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12357;
                    attrtab = uu____12360;
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
                    qtbl_name_and_index = uu____12367;
                    normalized_eff_names = uu____12403;
                    fv_delta_depths = uu____12407;
                    proof_ns = uu____12411;
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
                    is_native_tactic = (fun uu____12490  -> false);
                    identifier_info = uu____12412;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12415;
                    nbe = nbe1;
                    strict_args_tab = uu____12416
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
  fun uu____12569  ->
    let uu____12570 = FStar_ST.op_Bang query_indices  in
    match uu____12570 with
    | [] -> failwith "Empty query indices!"
    | uu____12625 ->
        let uu____12635 =
          let uu____12645 =
            let uu____12653 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12653  in
          let uu____12707 = FStar_ST.op_Bang query_indices  in uu____12645 ::
            uu____12707
           in
        FStar_ST.op_Colon_Equals query_indices uu____12635
  
let (pop_query_indices : unit -> unit) =
  fun uu____12803  ->
    let uu____12804 = FStar_ST.op_Bang query_indices  in
    match uu____12804 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____12931  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____12968  ->
    match uu____12968 with
    | (l,n1) ->
        let uu____12978 = FStar_ST.op_Bang query_indices  in
        (match uu____12978 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13100 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13123  ->
    let uu____13124 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13124
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13192 =
       let uu____13195 = FStar_ST.op_Bang stack  in env :: uu____13195  in
     FStar_ST.op_Colon_Equals stack uu____13192);
    (let uu___414_13244 = env  in
     let uu____13245 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13248 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13251 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13258 =
       let uu____13273 =
         let uu____13277 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13277  in
       let uu____13309 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13273, uu____13309)  in
     let uu____13358 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13361 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13364 =
       let uu____13367 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13367  in
     let uu____13387 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___414_13244.solver);
       range = (uu___414_13244.range);
       curmodule = (uu___414_13244.curmodule);
       gamma = (uu___414_13244.gamma);
       gamma_sig = (uu___414_13244.gamma_sig);
       gamma_cache = uu____13245;
       modules = (uu___414_13244.modules);
       expected_typ = (uu___414_13244.expected_typ);
       sigtab = uu____13248;
       attrtab = uu____13251;
       instantiate_imp = (uu___414_13244.instantiate_imp);
       effects = (uu___414_13244.effects);
       generalize = (uu___414_13244.generalize);
       letrecs = (uu___414_13244.letrecs);
       top_level = (uu___414_13244.top_level);
       check_uvars = (uu___414_13244.check_uvars);
       use_eq = (uu___414_13244.use_eq);
       is_iface = (uu___414_13244.is_iface);
       admit = (uu___414_13244.admit);
       lax = (uu___414_13244.lax);
       lax_universes = (uu___414_13244.lax_universes);
       phase1 = (uu___414_13244.phase1);
       failhard = (uu___414_13244.failhard);
       nosynth = (uu___414_13244.nosynth);
       uvar_subtyping = (uu___414_13244.uvar_subtyping);
       tc_term = (uu___414_13244.tc_term);
       type_of = (uu___414_13244.type_of);
       universe_of = (uu___414_13244.universe_of);
       check_type_of = (uu___414_13244.check_type_of);
       use_bv_sorts = (uu___414_13244.use_bv_sorts);
       qtbl_name_and_index = uu____13258;
       normalized_eff_names = uu____13358;
       fv_delta_depths = uu____13361;
       proof_ns = (uu___414_13244.proof_ns);
       synth_hook = (uu___414_13244.synth_hook);
       splice = (uu___414_13244.splice);
       postprocess = (uu___414_13244.postprocess);
       is_native_tactic = (uu___414_13244.is_native_tactic);
       identifier_info = uu____13364;
       tc_hooks = (uu___414_13244.tc_hooks);
       dsenv = (uu___414_13244.dsenv);
       nbe = (uu___414_13244.nbe);
       strict_args_tab = uu____13387
     })
  
let (pop_stack : unit -> env) =
  fun uu____13405  ->
    let uu____13406 = FStar_ST.op_Bang stack  in
    match uu____13406 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13460 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13550  ->
           let uu____13551 = snapshot_stack env  in
           match uu____13551 with
           | (stack_depth,env1) ->
               let uu____13585 = snapshot_query_indices ()  in
               (match uu____13585 with
                | (query_indices_depth,()) ->
                    let uu____13618 = (env1.solver).snapshot msg  in
                    (match uu____13618 with
                     | (solver_depth,()) ->
                         let uu____13675 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13675 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___439_13742 = env1  in
                                 {
                                   solver = (uu___439_13742.solver);
                                   range = (uu___439_13742.range);
                                   curmodule = (uu___439_13742.curmodule);
                                   gamma = (uu___439_13742.gamma);
                                   gamma_sig = (uu___439_13742.gamma_sig);
                                   gamma_cache = (uu___439_13742.gamma_cache);
                                   modules = (uu___439_13742.modules);
                                   expected_typ =
                                     (uu___439_13742.expected_typ);
                                   sigtab = (uu___439_13742.sigtab);
                                   attrtab = (uu___439_13742.attrtab);
                                   instantiate_imp =
                                     (uu___439_13742.instantiate_imp);
                                   effects = (uu___439_13742.effects);
                                   generalize = (uu___439_13742.generalize);
                                   letrecs = (uu___439_13742.letrecs);
                                   top_level = (uu___439_13742.top_level);
                                   check_uvars = (uu___439_13742.check_uvars);
                                   use_eq = (uu___439_13742.use_eq);
                                   is_iface = (uu___439_13742.is_iface);
                                   admit = (uu___439_13742.admit);
                                   lax = (uu___439_13742.lax);
                                   lax_universes =
                                     (uu___439_13742.lax_universes);
                                   phase1 = (uu___439_13742.phase1);
                                   failhard = (uu___439_13742.failhard);
                                   nosynth = (uu___439_13742.nosynth);
                                   uvar_subtyping =
                                     (uu___439_13742.uvar_subtyping);
                                   tc_term = (uu___439_13742.tc_term);
                                   type_of = (uu___439_13742.type_of);
                                   universe_of = (uu___439_13742.universe_of);
                                   check_type_of =
                                     (uu___439_13742.check_type_of);
                                   use_bv_sorts =
                                     (uu___439_13742.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___439_13742.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___439_13742.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___439_13742.fv_delta_depths);
                                   proof_ns = (uu___439_13742.proof_ns);
                                   synth_hook = (uu___439_13742.synth_hook);
                                   splice = (uu___439_13742.splice);
                                   postprocess = (uu___439_13742.postprocess);
                                   is_native_tactic =
                                     (uu___439_13742.is_native_tactic);
                                   identifier_info =
                                     (uu___439_13742.identifier_info);
                                   tc_hooks = (uu___439_13742.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___439_13742.nbe);
                                   strict_args_tab =
                                     (uu___439_13742.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13776  ->
             let uu____13777 =
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
             match uu____13777 with
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
                             ((let uu____13957 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13957
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13973 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13973
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14005,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14047 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14077  ->
                  match uu____14077 with
                  | (m,uu____14085) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14047 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___484_14100 = env  in
               {
                 solver = (uu___484_14100.solver);
                 range = (uu___484_14100.range);
                 curmodule = (uu___484_14100.curmodule);
                 gamma = (uu___484_14100.gamma);
                 gamma_sig = (uu___484_14100.gamma_sig);
                 gamma_cache = (uu___484_14100.gamma_cache);
                 modules = (uu___484_14100.modules);
                 expected_typ = (uu___484_14100.expected_typ);
                 sigtab = (uu___484_14100.sigtab);
                 attrtab = (uu___484_14100.attrtab);
                 instantiate_imp = (uu___484_14100.instantiate_imp);
                 effects = (uu___484_14100.effects);
                 generalize = (uu___484_14100.generalize);
                 letrecs = (uu___484_14100.letrecs);
                 top_level = (uu___484_14100.top_level);
                 check_uvars = (uu___484_14100.check_uvars);
                 use_eq = (uu___484_14100.use_eq);
                 is_iface = (uu___484_14100.is_iface);
                 admit = (uu___484_14100.admit);
                 lax = (uu___484_14100.lax);
                 lax_universes = (uu___484_14100.lax_universes);
                 phase1 = (uu___484_14100.phase1);
                 failhard = (uu___484_14100.failhard);
                 nosynth = (uu___484_14100.nosynth);
                 uvar_subtyping = (uu___484_14100.uvar_subtyping);
                 tc_term = (uu___484_14100.tc_term);
                 type_of = (uu___484_14100.type_of);
                 universe_of = (uu___484_14100.universe_of);
                 check_type_of = (uu___484_14100.check_type_of);
                 use_bv_sorts = (uu___484_14100.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___484_14100.normalized_eff_names);
                 fv_delta_depths = (uu___484_14100.fv_delta_depths);
                 proof_ns = (uu___484_14100.proof_ns);
                 synth_hook = (uu___484_14100.synth_hook);
                 splice = (uu___484_14100.splice);
                 postprocess = (uu___484_14100.postprocess);
                 is_native_tactic = (uu___484_14100.is_native_tactic);
                 identifier_info = (uu___484_14100.identifier_info);
                 tc_hooks = (uu___484_14100.tc_hooks);
                 dsenv = (uu___484_14100.dsenv);
                 nbe = (uu___484_14100.nbe);
                 strict_args_tab = (uu___484_14100.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14117,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___493_14133 = env  in
               {
                 solver = (uu___493_14133.solver);
                 range = (uu___493_14133.range);
                 curmodule = (uu___493_14133.curmodule);
                 gamma = (uu___493_14133.gamma);
                 gamma_sig = (uu___493_14133.gamma_sig);
                 gamma_cache = (uu___493_14133.gamma_cache);
                 modules = (uu___493_14133.modules);
                 expected_typ = (uu___493_14133.expected_typ);
                 sigtab = (uu___493_14133.sigtab);
                 attrtab = (uu___493_14133.attrtab);
                 instantiate_imp = (uu___493_14133.instantiate_imp);
                 effects = (uu___493_14133.effects);
                 generalize = (uu___493_14133.generalize);
                 letrecs = (uu___493_14133.letrecs);
                 top_level = (uu___493_14133.top_level);
                 check_uvars = (uu___493_14133.check_uvars);
                 use_eq = (uu___493_14133.use_eq);
                 is_iface = (uu___493_14133.is_iface);
                 admit = (uu___493_14133.admit);
                 lax = (uu___493_14133.lax);
                 lax_universes = (uu___493_14133.lax_universes);
                 phase1 = (uu___493_14133.phase1);
                 failhard = (uu___493_14133.failhard);
                 nosynth = (uu___493_14133.nosynth);
                 uvar_subtyping = (uu___493_14133.uvar_subtyping);
                 tc_term = (uu___493_14133.tc_term);
                 type_of = (uu___493_14133.type_of);
                 universe_of = (uu___493_14133.universe_of);
                 check_type_of = (uu___493_14133.check_type_of);
                 use_bv_sorts = (uu___493_14133.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___493_14133.normalized_eff_names);
                 fv_delta_depths = (uu___493_14133.fv_delta_depths);
                 proof_ns = (uu___493_14133.proof_ns);
                 synth_hook = (uu___493_14133.synth_hook);
                 splice = (uu___493_14133.splice);
                 postprocess = (uu___493_14133.postprocess);
                 is_native_tactic = (uu___493_14133.is_native_tactic);
                 identifier_info = (uu___493_14133.identifier_info);
                 tc_hooks = (uu___493_14133.tc_hooks);
                 dsenv = (uu___493_14133.dsenv);
                 nbe = (uu___493_14133.nbe);
                 strict_args_tab = (uu___493_14133.strict_args_tab)
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
        (let uu___500_14176 = e  in
         {
           solver = (uu___500_14176.solver);
           range = r;
           curmodule = (uu___500_14176.curmodule);
           gamma = (uu___500_14176.gamma);
           gamma_sig = (uu___500_14176.gamma_sig);
           gamma_cache = (uu___500_14176.gamma_cache);
           modules = (uu___500_14176.modules);
           expected_typ = (uu___500_14176.expected_typ);
           sigtab = (uu___500_14176.sigtab);
           attrtab = (uu___500_14176.attrtab);
           instantiate_imp = (uu___500_14176.instantiate_imp);
           effects = (uu___500_14176.effects);
           generalize = (uu___500_14176.generalize);
           letrecs = (uu___500_14176.letrecs);
           top_level = (uu___500_14176.top_level);
           check_uvars = (uu___500_14176.check_uvars);
           use_eq = (uu___500_14176.use_eq);
           is_iface = (uu___500_14176.is_iface);
           admit = (uu___500_14176.admit);
           lax = (uu___500_14176.lax);
           lax_universes = (uu___500_14176.lax_universes);
           phase1 = (uu___500_14176.phase1);
           failhard = (uu___500_14176.failhard);
           nosynth = (uu___500_14176.nosynth);
           uvar_subtyping = (uu___500_14176.uvar_subtyping);
           tc_term = (uu___500_14176.tc_term);
           type_of = (uu___500_14176.type_of);
           universe_of = (uu___500_14176.universe_of);
           check_type_of = (uu___500_14176.check_type_of);
           use_bv_sorts = (uu___500_14176.use_bv_sorts);
           qtbl_name_and_index = (uu___500_14176.qtbl_name_and_index);
           normalized_eff_names = (uu___500_14176.normalized_eff_names);
           fv_delta_depths = (uu___500_14176.fv_delta_depths);
           proof_ns = (uu___500_14176.proof_ns);
           synth_hook = (uu___500_14176.synth_hook);
           splice = (uu___500_14176.splice);
           postprocess = (uu___500_14176.postprocess);
           is_native_tactic = (uu___500_14176.is_native_tactic);
           identifier_info = (uu___500_14176.identifier_info);
           tc_hooks = (uu___500_14176.tc_hooks);
           dsenv = (uu___500_14176.dsenv);
           nbe = (uu___500_14176.nbe);
           strict_args_tab = (uu___500_14176.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14196 =
        let uu____14197 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14197 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14196
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14252 =
          let uu____14253 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14253 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14252
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14308 =
          let uu____14309 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14309 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14308
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14364 =
        let uu____14365 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14365 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14364
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___517_14429 = env  in
      {
        solver = (uu___517_14429.solver);
        range = (uu___517_14429.range);
        curmodule = lid;
        gamma = (uu___517_14429.gamma);
        gamma_sig = (uu___517_14429.gamma_sig);
        gamma_cache = (uu___517_14429.gamma_cache);
        modules = (uu___517_14429.modules);
        expected_typ = (uu___517_14429.expected_typ);
        sigtab = (uu___517_14429.sigtab);
        attrtab = (uu___517_14429.attrtab);
        instantiate_imp = (uu___517_14429.instantiate_imp);
        effects = (uu___517_14429.effects);
        generalize = (uu___517_14429.generalize);
        letrecs = (uu___517_14429.letrecs);
        top_level = (uu___517_14429.top_level);
        check_uvars = (uu___517_14429.check_uvars);
        use_eq = (uu___517_14429.use_eq);
        is_iface = (uu___517_14429.is_iface);
        admit = (uu___517_14429.admit);
        lax = (uu___517_14429.lax);
        lax_universes = (uu___517_14429.lax_universes);
        phase1 = (uu___517_14429.phase1);
        failhard = (uu___517_14429.failhard);
        nosynth = (uu___517_14429.nosynth);
        uvar_subtyping = (uu___517_14429.uvar_subtyping);
        tc_term = (uu___517_14429.tc_term);
        type_of = (uu___517_14429.type_of);
        universe_of = (uu___517_14429.universe_of);
        check_type_of = (uu___517_14429.check_type_of);
        use_bv_sorts = (uu___517_14429.use_bv_sorts);
        qtbl_name_and_index = (uu___517_14429.qtbl_name_and_index);
        normalized_eff_names = (uu___517_14429.normalized_eff_names);
        fv_delta_depths = (uu___517_14429.fv_delta_depths);
        proof_ns = (uu___517_14429.proof_ns);
        synth_hook = (uu___517_14429.synth_hook);
        splice = (uu___517_14429.splice);
        postprocess = (uu___517_14429.postprocess);
        is_native_tactic = (uu___517_14429.is_native_tactic);
        identifier_info = (uu___517_14429.identifier_info);
        tc_hooks = (uu___517_14429.tc_hooks);
        dsenv = (uu___517_14429.dsenv);
        nbe = (uu___517_14429.nbe);
        strict_args_tab = (uu___517_14429.strict_args_tab)
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
      let uu____14460 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14460
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14473 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14473)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14488 =
      let uu____14490 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14490  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14488)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14499  ->
    let uu____14500 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14500
  
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
      | ((formals,t),uu____14600) ->
          let vs = mk_univ_subst formals us  in
          let uu____14624 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14624)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14641  ->
    match uu___1_14641 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14667  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14687 = inst_tscheme t  in
      match uu____14687 with
      | (us,t1) ->
          let uu____14698 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14698)
  
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
          let uu____14723 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____14725 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____14723 uu____14725
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
        fun uu____14752  ->
          match uu____14752 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____14766 =
                    let uu____14768 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____14772 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____14776 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____14778 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____14768 uu____14772 uu____14776 uu____14778
                     in
                  failwith uu____14766)
               else ();
               (let uu____14783 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____14783))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14801 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14812 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14823 -> false
  
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
             | ([],uu____14871) -> Maybe
             | (uu____14878,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14898 -> No  in
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
          let uu____14992 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14992 with
          | FStar_Pervasives_Native.None  ->
              let uu____15015 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15059  ->
                     match uu___2_15059 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15098 = FStar_Ident.lid_equals lid l  in
                         if uu____15098
                         then
                           let uu____15121 =
                             let uu____15140 =
                               let uu____15155 = inst_tscheme t  in
                               FStar_Util.Inl uu____15155  in
                             let uu____15170 = FStar_Ident.range_of_lid l  in
                             (uu____15140, uu____15170)  in
                           FStar_Pervasives_Native.Some uu____15121
                         else FStar_Pervasives_Native.None
                     | uu____15223 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15015
                (fun uu____15261  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15270  ->
                        match uu___3_15270 with
                        | (uu____15273,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15275);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15276;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15277;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15278;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15279;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15299 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15299
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
                                  uu____15351 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15358 -> cache t  in
                            let uu____15359 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15359 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15365 =
                                   let uu____15366 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15366)
                                    in
                                 maybe_cache uu____15365)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15437 = find_in_sigtab env lid  in
         match uu____15437 with
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
      let uu____15518 = lookup_qname env lid  in
      match uu____15518 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15539,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15653 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15653 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15698 =
          let uu____15701 = lookup_attr env1 attr  in se1 :: uu____15701  in
        FStar_Util.smap_add (attrtab env1) attr uu____15698  in
      FStar_List.iter
        (fun attr  ->
           let uu____15711 =
             let uu____15712 = FStar_Syntax_Subst.compress attr  in
             uu____15712.FStar_Syntax_Syntax.n  in
           match uu____15711 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15716 =
                 let uu____15718 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15718.FStar_Ident.str  in
               add_one1 env se uu____15716
           | uu____15719 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15742) ->
          add_sigelts env ses
      | uu____15751 ->
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
        (fun uu___4_15789  ->
           match uu___4_15789 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15807 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____15869,lb::[]),uu____15871) ->
            let uu____15880 =
              let uu____15889 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15898 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15889, uu____15898)  in
            FStar_Pervasives_Native.Some uu____15880
        | FStar_Syntax_Syntax.Sig_let ((uu____15911,lbs),uu____15913) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15945 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15958 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15958
                     then
                       let uu____15971 =
                         let uu____15980 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____15989 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15980, uu____15989)  in
                       FStar_Pervasives_Native.Some uu____15971
                     else FStar_Pervasives_Native.None)
        | uu____16012 -> FStar_Pervasives_Native.None
  
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
                    let uu____16104 =
                      let uu____16106 =
                        let uu____16108 =
                          let uu____16110 =
                            let uu____16112 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16118 =
                              let uu____16120 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16120  in
                            Prims.op_Hat uu____16112 uu____16118  in
                          Prims.op_Hat ", expected " uu____16110  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16108
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16106
                       in
                    failwith uu____16104
                  else ());
             (let uu____16127 =
                let uu____16136 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16136, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16127))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16156,uu____16157) ->
            let uu____16162 =
              let uu____16171 =
                let uu____16176 =
                  let uu____16177 =
                    let uu____16180 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16180  in
                  (us, uu____16177)  in
                inst_ts us_opt uu____16176  in
              (uu____16171, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16162
        | uu____16199 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16288 =
          match uu____16288 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16384,uvs,t,uu____16387,uu____16388,uu____16389);
                      FStar_Syntax_Syntax.sigrng = uu____16390;
                      FStar_Syntax_Syntax.sigquals = uu____16391;
                      FStar_Syntax_Syntax.sigmeta = uu____16392;
                      FStar_Syntax_Syntax.sigattrs = uu____16393;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16416 =
                     let uu____16425 = inst_tscheme1 (uvs, t)  in
                     (uu____16425, rng)  in
                   FStar_Pervasives_Native.Some uu____16416
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16449;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16451;
                      FStar_Syntax_Syntax.sigattrs = uu____16452;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16469 =
                     let uu____16471 = in_cur_mod env l  in uu____16471 = Yes
                      in
                   if uu____16469
                   then
                     let uu____16483 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16483
                      then
                        let uu____16499 =
                          let uu____16508 = inst_tscheme1 (uvs, t)  in
                          (uu____16508, rng)  in
                        FStar_Pervasives_Native.Some uu____16499
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16541 =
                        let uu____16550 = inst_tscheme1 (uvs, t)  in
                        (uu____16550, rng)  in
                      FStar_Pervasives_Native.Some uu____16541)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16575,uu____16576);
                      FStar_Syntax_Syntax.sigrng = uu____16577;
                      FStar_Syntax_Syntax.sigquals = uu____16578;
                      FStar_Syntax_Syntax.sigmeta = uu____16579;
                      FStar_Syntax_Syntax.sigattrs = uu____16580;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16621 =
                          let uu____16630 = inst_tscheme1 (uvs, k)  in
                          (uu____16630, rng)  in
                        FStar_Pervasives_Native.Some uu____16621
                    | uu____16651 ->
                        let uu____16652 =
                          let uu____16661 =
                            let uu____16666 =
                              let uu____16667 =
                                let uu____16670 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16670
                                 in
                              (uvs, uu____16667)  in
                            inst_tscheme1 uu____16666  in
                          (uu____16661, rng)  in
                        FStar_Pervasives_Native.Some uu____16652)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16693,uu____16694);
                      FStar_Syntax_Syntax.sigrng = uu____16695;
                      FStar_Syntax_Syntax.sigquals = uu____16696;
                      FStar_Syntax_Syntax.sigmeta = uu____16697;
                      FStar_Syntax_Syntax.sigattrs = uu____16698;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16740 =
                          let uu____16749 = inst_tscheme_with (uvs, k) us  in
                          (uu____16749, rng)  in
                        FStar_Pervasives_Native.Some uu____16740
                    | uu____16770 ->
                        let uu____16771 =
                          let uu____16780 =
                            let uu____16785 =
                              let uu____16786 =
                                let uu____16789 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16789
                                 in
                              (uvs, uu____16786)  in
                            inst_tscheme_with uu____16785 us  in
                          (uu____16780, rng)  in
                        FStar_Pervasives_Native.Some uu____16771)
               | FStar_Util.Inr se ->
                   let uu____16825 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16846;
                          FStar_Syntax_Syntax.sigrng = uu____16847;
                          FStar_Syntax_Syntax.sigquals = uu____16848;
                          FStar_Syntax_Syntax.sigmeta = uu____16849;
                          FStar_Syntax_Syntax.sigattrs = uu____16850;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16865 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____16825
                     (FStar_Util.map_option
                        (fun uu____16913  ->
                           match uu____16913 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16944 =
          let uu____16955 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16955 mapper  in
        match uu____16944 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17029 =
              let uu____17040 =
                let uu____17047 =
                  let uu___848_17050 = t  in
                  let uu____17051 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___848_17050.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17051;
                    FStar_Syntax_Syntax.vars =
                      (uu___848_17050.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17047)  in
              (uu____17040, r)  in
            FStar_Pervasives_Native.Some uu____17029
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17100 = lookup_qname env l  in
      match uu____17100 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17121 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17175 = try_lookup_bv env bv  in
      match uu____17175 with
      | FStar_Pervasives_Native.None  ->
          let uu____17190 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17190 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17206 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17207 =
            let uu____17208 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17208  in
          (uu____17206, uu____17207)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17230 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17230 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17296 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17296  in
          let uu____17297 =
            let uu____17306 =
              let uu____17311 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17311)  in
            (uu____17306, r1)  in
          FStar_Pervasives_Native.Some uu____17297
  
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
        let uu____17346 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17346 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17379,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17404 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17404  in
            let uu____17405 =
              let uu____17410 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17410, r1)  in
            FStar_Pervasives_Native.Some uu____17405
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17434 = try_lookup_lid env l  in
      match uu____17434 with
      | FStar_Pervasives_Native.None  ->
          let uu____17461 = name_not_found l  in
          let uu____17467 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17461 uu____17467
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17510  ->
              match uu___5_17510 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17514 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17535 = lookup_qname env lid  in
      match uu____17535 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17544,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17547;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17549;
              FStar_Syntax_Syntax.sigattrs = uu____17550;_},FStar_Pervasives_Native.None
            ),uu____17551)
          ->
          let uu____17600 =
            let uu____17607 =
              let uu____17608 =
                let uu____17611 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17611 t  in
              (uvs, uu____17608)  in
            (uu____17607, q)  in
          FStar_Pervasives_Native.Some uu____17600
      | uu____17624 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17646 = lookup_qname env lid  in
      match uu____17646 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17651,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17654;
              FStar_Syntax_Syntax.sigquals = uu____17655;
              FStar_Syntax_Syntax.sigmeta = uu____17656;
              FStar_Syntax_Syntax.sigattrs = uu____17657;_},FStar_Pervasives_Native.None
            ),uu____17658)
          ->
          let uu____17707 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17707 (uvs, t)
      | uu____17712 ->
          let uu____17713 = name_not_found lid  in
          let uu____17719 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17713 uu____17719
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17739 = lookup_qname env lid  in
      match uu____17739 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17744,uvs,t,uu____17747,uu____17748,uu____17749);
              FStar_Syntax_Syntax.sigrng = uu____17750;
              FStar_Syntax_Syntax.sigquals = uu____17751;
              FStar_Syntax_Syntax.sigmeta = uu____17752;
              FStar_Syntax_Syntax.sigattrs = uu____17753;_},FStar_Pervasives_Native.None
            ),uu____17754)
          ->
          let uu____17809 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17809 (uvs, t)
      | uu____17814 ->
          let uu____17815 = name_not_found lid  in
          let uu____17821 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17815 uu____17821
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17844 = lookup_qname env lid  in
      match uu____17844 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17852,uu____17853,uu____17854,uu____17855,uu____17856,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17858;
              FStar_Syntax_Syntax.sigquals = uu____17859;
              FStar_Syntax_Syntax.sigmeta = uu____17860;
              FStar_Syntax_Syntax.sigattrs = uu____17861;_},uu____17862),uu____17863)
          -> (true, dcs)
      | uu____17926 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17942 = lookup_qname env lid  in
      match uu____17942 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17943,uu____17944,uu____17945,l,uu____17947,uu____17948);
              FStar_Syntax_Syntax.sigrng = uu____17949;
              FStar_Syntax_Syntax.sigquals = uu____17950;
              FStar_Syntax_Syntax.sigmeta = uu____17951;
              FStar_Syntax_Syntax.sigattrs = uu____17952;_},uu____17953),uu____17954)
          -> l
      | uu____18011 ->
          let uu____18012 =
            let uu____18014 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18014  in
          failwith uu____18012
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18084)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18141) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18165 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18165
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18200 -> FStar_Pervasives_Native.None)
          | uu____18209 -> FStar_Pervasives_Native.None
  
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
        let uu____18271 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18271
  
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
        let uu____18304 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18304
  
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
             (FStar_Util.Inl uu____18356,uu____18357) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18406),uu____18407) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18456 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18474 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18484 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18501 ->
                  let uu____18508 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18508
              | FStar_Syntax_Syntax.Sig_let ((uu____18509,lbs),uu____18511)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18527 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18527
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18534 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18542 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18543 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18550 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18551 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18552 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18553 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18566 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18584 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18584
           (fun d_opt  ->
              let uu____18597 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18597
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18607 =
                   let uu____18610 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18610  in
                 match uu____18607 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18611 =
                       let uu____18613 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18613
                        in
                     failwith uu____18611
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18618 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18618
                       then
                         let uu____18621 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18623 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18625 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18621 uu____18623 uu____18625
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
        (FStar_Util.Inr (se,uu____18650),uu____18651) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18700 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18722),uu____18723) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18772 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18794 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18794
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____18817 = lookup_attrs_of_lid env fv_lid1  in
        match uu____18817 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18841 =
                      let uu____18842 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18842.FStar_Syntax_Syntax.n  in
                    match uu____18841 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____18847 -> false))
  
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
        let uu____18884 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____18884.FStar_Ident.str  in
      let uu____18885 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____18885 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____18913 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____18913  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____18941 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____18941)
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
      let uu____18991 = lookup_qname env ftv  in
      match uu____18991 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18995) ->
          let uu____19040 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19040 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19061,t),r) ->
               let uu____19076 =
                 let uu____19077 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19077 t  in
               FStar_Pervasives_Native.Some uu____19076)
      | uu____19078 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19090 = try_lookup_effect_lid env ftv  in
      match uu____19090 with
      | FStar_Pervasives_Native.None  ->
          let uu____19093 = name_not_found ftv  in
          let uu____19099 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19093 uu____19099
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
        let uu____19123 = lookup_qname env lid0  in
        match uu____19123 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19134);
                FStar_Syntax_Syntax.sigrng = uu____19135;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19137;
                FStar_Syntax_Syntax.sigattrs = uu____19138;_},FStar_Pervasives_Native.None
              ),uu____19139)
            ->
            let lid1 =
              let uu____19193 =
                let uu____19194 = FStar_Ident.range_of_lid lid  in
                let uu____19195 =
                  let uu____19196 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19196  in
                FStar_Range.set_use_range uu____19194 uu____19195  in
              FStar_Ident.set_lid_range lid uu____19193  in
            let uu____19197 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19203  ->
                      match uu___6_19203 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19206 -> false))
               in
            if uu____19197
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19225 =
                      let uu____19227 =
                        let uu____19229 = get_range env  in
                        FStar_Range.string_of_range uu____19229  in
                      let uu____19230 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19232 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19227 uu____19230 uu____19232
                       in
                    failwith uu____19225)
                  in
               match (binders, univs1) with
               | ([],uu____19253) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19279,uu____19280::uu____19281::uu____19282) ->
                   let uu____19303 =
                     let uu____19305 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19307 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19305 uu____19307
                      in
                   failwith uu____19303
               | uu____19318 ->
                   let uu____19333 =
                     let uu____19338 =
                       let uu____19339 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19339)  in
                     inst_tscheme_with uu____19338 insts  in
                   (match uu____19333 with
                    | (uu____19352,t) ->
                        let t1 =
                          let uu____19355 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19355 t  in
                        let uu____19356 =
                          let uu____19357 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19357.FStar_Syntax_Syntax.n  in
                        (match uu____19356 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19392 -> failwith "Impossible")))
        | uu____19400 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19424 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19424 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19437,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19444 = find1 l2  in
            (match uu____19444 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19451 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19451 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19455 = find1 l  in
            (match uu____19455 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19460 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19460
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19475 = lookup_qname env l1  in
      match uu____19475 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19478;
              FStar_Syntax_Syntax.sigrng = uu____19479;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19481;
              FStar_Syntax_Syntax.sigattrs = uu____19482;_},uu____19483),uu____19484)
          -> q
      | uu____19535 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19559 =
          let uu____19560 =
            let uu____19562 = FStar_Util.string_of_int i  in
            let uu____19564 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19562 uu____19564
             in
          failwith uu____19560  in
        let uu____19567 = lookup_datacon env lid  in
        match uu____19567 with
        | (uu____19572,t) ->
            let uu____19574 =
              let uu____19575 = FStar_Syntax_Subst.compress t  in
              uu____19575.FStar_Syntax_Syntax.n  in
            (match uu____19574 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19579) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19623 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19623
                      FStar_Pervasives_Native.fst)
             | uu____19634 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19648 = lookup_qname env l  in
      match uu____19648 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19650,uu____19651,uu____19652);
              FStar_Syntax_Syntax.sigrng = uu____19653;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19655;
              FStar_Syntax_Syntax.sigattrs = uu____19656;_},uu____19657),uu____19658)
          ->
          FStar_Util.for_some
            (fun uu___7_19711  ->
               match uu___7_19711 with
               | FStar_Syntax_Syntax.Projector uu____19713 -> true
               | uu____19719 -> false) quals
      | uu____19721 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19735 = lookup_qname env lid  in
      match uu____19735 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19737,uu____19738,uu____19739,uu____19740,uu____19741,uu____19742);
              FStar_Syntax_Syntax.sigrng = uu____19743;
              FStar_Syntax_Syntax.sigquals = uu____19744;
              FStar_Syntax_Syntax.sigmeta = uu____19745;
              FStar_Syntax_Syntax.sigattrs = uu____19746;_},uu____19747),uu____19748)
          -> true
      | uu____19806 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19820 = lookup_qname env lid  in
      match uu____19820 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19822,uu____19823,uu____19824,uu____19825,uu____19826,uu____19827);
              FStar_Syntax_Syntax.sigrng = uu____19828;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19830;
              FStar_Syntax_Syntax.sigattrs = uu____19831;_},uu____19832),uu____19833)
          ->
          FStar_Util.for_some
            (fun uu___8_19894  ->
               match uu___8_19894 with
               | FStar_Syntax_Syntax.RecordType uu____19896 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19906 -> true
               | uu____19916 -> false) quals
      | uu____19918 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19928,uu____19929);
            FStar_Syntax_Syntax.sigrng = uu____19930;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19932;
            FStar_Syntax_Syntax.sigattrs = uu____19933;_},uu____19934),uu____19935)
        ->
        FStar_Util.for_some
          (fun uu___9_19992  ->
             match uu___9_19992 with
             | FStar_Syntax_Syntax.Action uu____19994 -> true
             | uu____19996 -> false) quals
    | uu____19998 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20012 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20012
  
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
      let uu____20029 =
        let uu____20030 = FStar_Syntax_Util.un_uinst head1  in
        uu____20030.FStar_Syntax_Syntax.n  in
      match uu____20029 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20036 ->
               true
           | uu____20039 -> false)
      | uu____20041 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20055 = lookup_qname env l  in
      match uu____20055 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20058),uu____20059) ->
          FStar_Util.for_some
            (fun uu___10_20107  ->
               match uu___10_20107 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20110 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20112 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20188 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20206) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20224 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20232 ->
                 FStar_Pervasives_Native.Some true
             | uu____20251 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20254 =
        let uu____20258 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20258 mapper  in
      match uu____20254 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20318 = lookup_qname env lid  in
      match uu____20318 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20322,uu____20323,tps,uu____20325,uu____20326,uu____20327);
              FStar_Syntax_Syntax.sigrng = uu____20328;
              FStar_Syntax_Syntax.sigquals = uu____20329;
              FStar_Syntax_Syntax.sigmeta = uu____20330;
              FStar_Syntax_Syntax.sigattrs = uu____20331;_},uu____20332),uu____20333)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20399 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20445  ->
              match uu____20445 with
              | (d,uu____20454) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20470 = effect_decl_opt env l  in
      match uu____20470 with
      | FStar_Pervasives_Native.None  ->
          let uu____20485 = name_not_found l  in
          let uu____20491 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20485 uu____20491
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20514  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20533  ->
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
        let uu____20565 = FStar_Ident.lid_equals l1 l2  in
        if uu____20565
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20576 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20576
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20587 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20640  ->
                        match uu____20640 with
                        | (m1,m2,uu____20654,uu____20655,uu____20656) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20587 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20673 =
                    let uu____20679 =
                      let uu____20681 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20683 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20681
                        uu____20683
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20679)
                     in
                  FStar_Errors.raise_error uu____20673 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20693,uu____20694,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20728 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20728
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
  'Auu____20748 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20748) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20777 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20803  ->
                match uu____20803 with
                | (d,uu____20810) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20777 with
      | FStar_Pervasives_Native.None  ->
          let uu____20821 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20821
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20836 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____20836 with
           | (uu____20847,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20865)::(wp,uu____20867)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20923 -> failwith "Impossible"))
  
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
        | uu____20988 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21001 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21001 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21018 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21018 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21043 =
                     let uu____21049 =
                       let uu____21051 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____21059 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____21070 =
                         let uu____21072 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____21072  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21051 uu____21059 uu____21070
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21049)
                      in
                   FStar_Errors.raise_error uu____21043
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____21080 =
                     let uu____21091 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____21091 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____21128  ->
                        fun uu____21129  ->
                          match (uu____21128, uu____21129) with
                          | ((x,uu____21159),(t,uu____21161)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21080
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____21192 =
                     let uu___1536_21193 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1536_21193.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1536_21193.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1536_21193.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1536_21193.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____21192
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____21205 .
    'Auu____21205 ->
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
          let uu____21235 = effect_decl_opt env effect_name  in
          match uu____21235 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____21278 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____21301 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____21340 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____21340
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____21345 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____21345
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____21356 =
                     let uu____21359 = get_range env  in
                     let uu____21360 =
                       let uu____21367 =
                         let uu____21368 =
                           let uu____21385 =
                             let uu____21396 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____21396; wp]  in
                           (repr, uu____21385)  in
                         FStar_Syntax_Syntax.Tm_app uu____21368  in
                       FStar_Syntax_Syntax.mk uu____21367  in
                     uu____21360 FStar_Pervasives_Native.None uu____21359  in
                   FStar_Pervasives_Native.Some uu____21356)
  
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
      | uu____21540 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21555 =
        let uu____21556 = FStar_Syntax_Subst.compress t  in
        uu____21556.FStar_Syntax_Syntax.n  in
      match uu____21555 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____21560,c) ->
          is_reifiable_comp env c
      | uu____21582 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____21602 =
           let uu____21604 = is_reifiable_effect env l  in
           Prims.op_Negation uu____21604  in
         if uu____21602
         then
           let uu____21607 =
             let uu____21613 =
               let uu____21615 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____21615
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____21613)  in
           let uu____21619 = get_range env  in
           FStar_Errors.raise_error uu____21607 uu____21619
         else ());
        (let uu____21622 = effect_repr_aux true env c u_c  in
         match uu____21622 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1601_21658 = env  in
        {
          solver = (uu___1601_21658.solver);
          range = (uu___1601_21658.range);
          curmodule = (uu___1601_21658.curmodule);
          gamma = (uu___1601_21658.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1601_21658.gamma_cache);
          modules = (uu___1601_21658.modules);
          expected_typ = (uu___1601_21658.expected_typ);
          sigtab = (uu___1601_21658.sigtab);
          attrtab = (uu___1601_21658.attrtab);
          instantiate_imp = (uu___1601_21658.instantiate_imp);
          effects = (uu___1601_21658.effects);
          generalize = (uu___1601_21658.generalize);
          letrecs = (uu___1601_21658.letrecs);
          top_level = (uu___1601_21658.top_level);
          check_uvars = (uu___1601_21658.check_uvars);
          use_eq = (uu___1601_21658.use_eq);
          is_iface = (uu___1601_21658.is_iface);
          admit = (uu___1601_21658.admit);
          lax = (uu___1601_21658.lax);
          lax_universes = (uu___1601_21658.lax_universes);
          phase1 = (uu___1601_21658.phase1);
          failhard = (uu___1601_21658.failhard);
          nosynth = (uu___1601_21658.nosynth);
          uvar_subtyping = (uu___1601_21658.uvar_subtyping);
          tc_term = (uu___1601_21658.tc_term);
          type_of = (uu___1601_21658.type_of);
          universe_of = (uu___1601_21658.universe_of);
          check_type_of = (uu___1601_21658.check_type_of);
          use_bv_sorts = (uu___1601_21658.use_bv_sorts);
          qtbl_name_and_index = (uu___1601_21658.qtbl_name_and_index);
          normalized_eff_names = (uu___1601_21658.normalized_eff_names);
          fv_delta_depths = (uu___1601_21658.fv_delta_depths);
          proof_ns = (uu___1601_21658.proof_ns);
          synth_hook = (uu___1601_21658.synth_hook);
          splice = (uu___1601_21658.splice);
          postprocess = (uu___1601_21658.postprocess);
          is_native_tactic = (uu___1601_21658.is_native_tactic);
          identifier_info = (uu___1601_21658.identifier_info);
          tc_hooks = (uu___1601_21658.tc_hooks);
          dsenv = (uu___1601_21658.dsenv);
          nbe = (uu___1601_21658.nbe);
          strict_args_tab = (uu___1601_21658.strict_args_tab)
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
    fun uu____21677  ->
      match uu____21677 with
      | (ed,quals) ->
          let effects =
            let uu___1610_21691 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1610_21691.order);
              joins = (uu___1610_21691.joins)
            }  in
          let uu___1613_21700 = env  in
          {
            solver = (uu___1613_21700.solver);
            range = (uu___1613_21700.range);
            curmodule = (uu___1613_21700.curmodule);
            gamma = (uu___1613_21700.gamma);
            gamma_sig = (uu___1613_21700.gamma_sig);
            gamma_cache = (uu___1613_21700.gamma_cache);
            modules = (uu___1613_21700.modules);
            expected_typ = (uu___1613_21700.expected_typ);
            sigtab = (uu___1613_21700.sigtab);
            attrtab = (uu___1613_21700.attrtab);
            instantiate_imp = (uu___1613_21700.instantiate_imp);
            effects;
            generalize = (uu___1613_21700.generalize);
            letrecs = (uu___1613_21700.letrecs);
            top_level = (uu___1613_21700.top_level);
            check_uvars = (uu___1613_21700.check_uvars);
            use_eq = (uu___1613_21700.use_eq);
            is_iface = (uu___1613_21700.is_iface);
            admit = (uu___1613_21700.admit);
            lax = (uu___1613_21700.lax);
            lax_universes = (uu___1613_21700.lax_universes);
            phase1 = (uu___1613_21700.phase1);
            failhard = (uu___1613_21700.failhard);
            nosynth = (uu___1613_21700.nosynth);
            uvar_subtyping = (uu___1613_21700.uvar_subtyping);
            tc_term = (uu___1613_21700.tc_term);
            type_of = (uu___1613_21700.type_of);
            universe_of = (uu___1613_21700.universe_of);
            check_type_of = (uu___1613_21700.check_type_of);
            use_bv_sorts = (uu___1613_21700.use_bv_sorts);
            qtbl_name_and_index = (uu___1613_21700.qtbl_name_and_index);
            normalized_eff_names = (uu___1613_21700.normalized_eff_names);
            fv_delta_depths = (uu___1613_21700.fv_delta_depths);
            proof_ns = (uu___1613_21700.proof_ns);
            synth_hook = (uu___1613_21700.synth_hook);
            splice = (uu___1613_21700.splice);
            postprocess = (uu___1613_21700.postprocess);
            is_native_tactic = (uu___1613_21700.is_native_tactic);
            identifier_info = (uu___1613_21700.identifier_info);
            tc_hooks = (uu___1613_21700.tc_hooks);
            dsenv = (uu___1613_21700.dsenv);
            nbe = (uu___1613_21700.nbe);
            strict_args_tab = (uu___1613_21700.strict_args_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____21740 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____21740  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____21898 = (e1.mlift).mlift_wp u t wp  in
                            let uu____21899 = l1 u t wp e  in
                            l2 u t uu____21898 uu____21899))
            | uu____21900 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____21972 = inst_tscheme_with lift_t [u]  in
        match uu____21972 with
        | (uu____21979,lift_t1) ->
            let uu____21981 =
              let uu____21988 =
                let uu____21989 =
                  let uu____22006 =
                    let uu____22017 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22026 =
                      let uu____22037 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____22037]  in
                    uu____22017 :: uu____22026  in
                  (lift_t1, uu____22006)  in
                FStar_Syntax_Syntax.Tm_app uu____21989  in
              FStar_Syntax_Syntax.mk uu____21988  in
            uu____21981 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____22147 = inst_tscheme_with lift_t [u]  in
        match uu____22147 with
        | (uu____22154,lift_t1) ->
            let uu____22156 =
              let uu____22163 =
                let uu____22164 =
                  let uu____22181 =
                    let uu____22192 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22201 =
                      let uu____22212 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____22221 =
                        let uu____22232 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____22232]  in
                      uu____22212 :: uu____22221  in
                    uu____22192 :: uu____22201  in
                  (lift_t1, uu____22181)  in
                FStar_Syntax_Syntax.Tm_app uu____22164  in
              FStar_Syntax_Syntax.mk uu____22163  in
            uu____22156 FStar_Pervasives_Native.None
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
          let uu____22334 =
            let uu____22335 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____22335
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____22334  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____22344 =
          let uu____22346 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____22346  in
        let uu____22347 =
          let uu____22349 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____22377 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____22377)
             in
          FStar_Util.dflt "none" uu____22349  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22344 uu____22347
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____22406  ->
                match uu____22406 with
                | (e,uu____22414) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____22437 =
        match uu____22437 with
        | (i,j) ->
            let uu____22448 = FStar_Ident.lid_equals i j  in
            if uu____22448
            then
              FStar_All.pipe_right (id_edge i)
                (fun _22455  -> FStar_Pervasives_Native.Some _22455)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____22484 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____22494 = FStar_Ident.lid_equals i k  in
                    if uu____22494
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____22508 = FStar_Ident.lid_equals j k
                                 in
                              if uu____22508
                              then []
                              else
                                (let uu____22515 =
                                   let uu____22524 = find_edge order1 (i, k)
                                      in
                                   let uu____22527 = find_edge order1 (k, j)
                                      in
                                   (uu____22524, uu____22527)  in
                                 match uu____22515 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____22542 = compose_edges e1 e2
                                        in
                                     [uu____22542]
                                 | uu____22543 -> [])))))
             in
          FStar_List.append order1 uu____22484  in
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
              let uu____22573 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____22576 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____22576
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____22573
              then
                let uu____22583 =
                  let uu____22589 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____22589)
                   in
                let uu____22593 = get_range env  in
                FStar_Errors.raise_error uu____22583 uu____22593
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____22671 = FStar_Ident.lid_equals i j  in
                           if uu____22671
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____22723 =
                                         let uu____22732 =
                                           find_edge order2 (i, k)  in
                                         let uu____22735 =
                                           find_edge order2 (j, k)  in
                                         (uu____22732, uu____22735)  in
                                       match uu____22723 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____22777,uu____22778)
                                                ->
                                                let uu____22785 =
                                                  let uu____22792 =
                                                    let uu____22794 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____22794
                                                     in
                                                  let uu____22797 =
                                                    let uu____22799 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____22799
                                                     in
                                                  (uu____22792, uu____22797)
                                                   in
                                                (match uu____22785 with
                                                 | (true ,true ) ->
                                                     let uu____22816 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____22816
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
                                       | uu____22859 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1740_22932 = env.effects  in
         { decls = (uu___1740_22932.decls); order = order2; joins }  in
       let uu___1743_22933 = env  in
       {
         solver = (uu___1743_22933.solver);
         range = (uu___1743_22933.range);
         curmodule = (uu___1743_22933.curmodule);
         gamma = (uu___1743_22933.gamma);
         gamma_sig = (uu___1743_22933.gamma_sig);
         gamma_cache = (uu___1743_22933.gamma_cache);
         modules = (uu___1743_22933.modules);
         expected_typ = (uu___1743_22933.expected_typ);
         sigtab = (uu___1743_22933.sigtab);
         attrtab = (uu___1743_22933.attrtab);
         instantiate_imp = (uu___1743_22933.instantiate_imp);
         effects;
         generalize = (uu___1743_22933.generalize);
         letrecs = (uu___1743_22933.letrecs);
         top_level = (uu___1743_22933.top_level);
         check_uvars = (uu___1743_22933.check_uvars);
         use_eq = (uu___1743_22933.use_eq);
         is_iface = (uu___1743_22933.is_iface);
         admit = (uu___1743_22933.admit);
         lax = (uu___1743_22933.lax);
         lax_universes = (uu___1743_22933.lax_universes);
         phase1 = (uu___1743_22933.phase1);
         failhard = (uu___1743_22933.failhard);
         nosynth = (uu___1743_22933.nosynth);
         uvar_subtyping = (uu___1743_22933.uvar_subtyping);
         tc_term = (uu___1743_22933.tc_term);
         type_of = (uu___1743_22933.type_of);
         universe_of = (uu___1743_22933.universe_of);
         check_type_of = (uu___1743_22933.check_type_of);
         use_bv_sorts = (uu___1743_22933.use_bv_sorts);
         qtbl_name_and_index = (uu___1743_22933.qtbl_name_and_index);
         normalized_eff_names = (uu___1743_22933.normalized_eff_names);
         fv_delta_depths = (uu___1743_22933.fv_delta_depths);
         proof_ns = (uu___1743_22933.proof_ns);
         synth_hook = (uu___1743_22933.synth_hook);
         splice = (uu___1743_22933.splice);
         postprocess = (uu___1743_22933.postprocess);
         is_native_tactic = (uu___1743_22933.is_native_tactic);
         identifier_info = (uu___1743_22933.identifier_info);
         tc_hooks = (uu___1743_22933.tc_hooks);
         dsenv = (uu___1743_22933.dsenv);
         nbe = (uu___1743_22933.nbe);
         strict_args_tab = (uu___1743_22933.strict_args_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1747_22945 = env  in
      {
        solver = (uu___1747_22945.solver);
        range = (uu___1747_22945.range);
        curmodule = (uu___1747_22945.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1747_22945.gamma_sig);
        gamma_cache = (uu___1747_22945.gamma_cache);
        modules = (uu___1747_22945.modules);
        expected_typ = (uu___1747_22945.expected_typ);
        sigtab = (uu___1747_22945.sigtab);
        attrtab = (uu___1747_22945.attrtab);
        instantiate_imp = (uu___1747_22945.instantiate_imp);
        effects = (uu___1747_22945.effects);
        generalize = (uu___1747_22945.generalize);
        letrecs = (uu___1747_22945.letrecs);
        top_level = (uu___1747_22945.top_level);
        check_uvars = (uu___1747_22945.check_uvars);
        use_eq = (uu___1747_22945.use_eq);
        is_iface = (uu___1747_22945.is_iface);
        admit = (uu___1747_22945.admit);
        lax = (uu___1747_22945.lax);
        lax_universes = (uu___1747_22945.lax_universes);
        phase1 = (uu___1747_22945.phase1);
        failhard = (uu___1747_22945.failhard);
        nosynth = (uu___1747_22945.nosynth);
        uvar_subtyping = (uu___1747_22945.uvar_subtyping);
        tc_term = (uu___1747_22945.tc_term);
        type_of = (uu___1747_22945.type_of);
        universe_of = (uu___1747_22945.universe_of);
        check_type_of = (uu___1747_22945.check_type_of);
        use_bv_sorts = (uu___1747_22945.use_bv_sorts);
        qtbl_name_and_index = (uu___1747_22945.qtbl_name_and_index);
        normalized_eff_names = (uu___1747_22945.normalized_eff_names);
        fv_delta_depths = (uu___1747_22945.fv_delta_depths);
        proof_ns = (uu___1747_22945.proof_ns);
        synth_hook = (uu___1747_22945.synth_hook);
        splice = (uu___1747_22945.splice);
        postprocess = (uu___1747_22945.postprocess);
        is_native_tactic = (uu___1747_22945.is_native_tactic);
        identifier_info = (uu___1747_22945.identifier_info);
        tc_hooks = (uu___1747_22945.tc_hooks);
        dsenv = (uu___1747_22945.dsenv);
        nbe = (uu___1747_22945.nbe);
        strict_args_tab = (uu___1747_22945.strict_args_tab)
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
            (let uu___1760_23003 = env  in
             {
               solver = (uu___1760_23003.solver);
               range = (uu___1760_23003.range);
               curmodule = (uu___1760_23003.curmodule);
               gamma = rest;
               gamma_sig = (uu___1760_23003.gamma_sig);
               gamma_cache = (uu___1760_23003.gamma_cache);
               modules = (uu___1760_23003.modules);
               expected_typ = (uu___1760_23003.expected_typ);
               sigtab = (uu___1760_23003.sigtab);
               attrtab = (uu___1760_23003.attrtab);
               instantiate_imp = (uu___1760_23003.instantiate_imp);
               effects = (uu___1760_23003.effects);
               generalize = (uu___1760_23003.generalize);
               letrecs = (uu___1760_23003.letrecs);
               top_level = (uu___1760_23003.top_level);
               check_uvars = (uu___1760_23003.check_uvars);
               use_eq = (uu___1760_23003.use_eq);
               is_iface = (uu___1760_23003.is_iface);
               admit = (uu___1760_23003.admit);
               lax = (uu___1760_23003.lax);
               lax_universes = (uu___1760_23003.lax_universes);
               phase1 = (uu___1760_23003.phase1);
               failhard = (uu___1760_23003.failhard);
               nosynth = (uu___1760_23003.nosynth);
               uvar_subtyping = (uu___1760_23003.uvar_subtyping);
               tc_term = (uu___1760_23003.tc_term);
               type_of = (uu___1760_23003.type_of);
               universe_of = (uu___1760_23003.universe_of);
               check_type_of = (uu___1760_23003.check_type_of);
               use_bv_sorts = (uu___1760_23003.use_bv_sorts);
               qtbl_name_and_index = (uu___1760_23003.qtbl_name_and_index);
               normalized_eff_names = (uu___1760_23003.normalized_eff_names);
               fv_delta_depths = (uu___1760_23003.fv_delta_depths);
               proof_ns = (uu___1760_23003.proof_ns);
               synth_hook = (uu___1760_23003.synth_hook);
               splice = (uu___1760_23003.splice);
               postprocess = (uu___1760_23003.postprocess);
               is_native_tactic = (uu___1760_23003.is_native_tactic);
               identifier_info = (uu___1760_23003.identifier_info);
               tc_hooks = (uu___1760_23003.tc_hooks);
               dsenv = (uu___1760_23003.dsenv);
               nbe = (uu___1760_23003.nbe);
               strict_args_tab = (uu___1760_23003.strict_args_tab)
             }))
    | uu____23004 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23033  ->
             match uu____23033 with | (x,uu____23041) -> push_bv env1 x) env
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
            let uu___1774_23076 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1774_23076.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1774_23076.FStar_Syntax_Syntax.index);
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
        let uu____23149 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23149 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23177 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23177)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1795_23193 = env  in
      {
        solver = (uu___1795_23193.solver);
        range = (uu___1795_23193.range);
        curmodule = (uu___1795_23193.curmodule);
        gamma = (uu___1795_23193.gamma);
        gamma_sig = (uu___1795_23193.gamma_sig);
        gamma_cache = (uu___1795_23193.gamma_cache);
        modules = (uu___1795_23193.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1795_23193.sigtab);
        attrtab = (uu___1795_23193.attrtab);
        instantiate_imp = (uu___1795_23193.instantiate_imp);
        effects = (uu___1795_23193.effects);
        generalize = (uu___1795_23193.generalize);
        letrecs = (uu___1795_23193.letrecs);
        top_level = (uu___1795_23193.top_level);
        check_uvars = (uu___1795_23193.check_uvars);
        use_eq = false;
        is_iface = (uu___1795_23193.is_iface);
        admit = (uu___1795_23193.admit);
        lax = (uu___1795_23193.lax);
        lax_universes = (uu___1795_23193.lax_universes);
        phase1 = (uu___1795_23193.phase1);
        failhard = (uu___1795_23193.failhard);
        nosynth = (uu___1795_23193.nosynth);
        uvar_subtyping = (uu___1795_23193.uvar_subtyping);
        tc_term = (uu___1795_23193.tc_term);
        type_of = (uu___1795_23193.type_of);
        universe_of = (uu___1795_23193.universe_of);
        check_type_of = (uu___1795_23193.check_type_of);
        use_bv_sorts = (uu___1795_23193.use_bv_sorts);
        qtbl_name_and_index = (uu___1795_23193.qtbl_name_and_index);
        normalized_eff_names = (uu___1795_23193.normalized_eff_names);
        fv_delta_depths = (uu___1795_23193.fv_delta_depths);
        proof_ns = (uu___1795_23193.proof_ns);
        synth_hook = (uu___1795_23193.synth_hook);
        splice = (uu___1795_23193.splice);
        postprocess = (uu___1795_23193.postprocess);
        is_native_tactic = (uu___1795_23193.is_native_tactic);
        identifier_info = (uu___1795_23193.identifier_info);
        tc_hooks = (uu___1795_23193.tc_hooks);
        dsenv = (uu___1795_23193.dsenv);
        nbe = (uu___1795_23193.nbe);
        strict_args_tab = (uu___1795_23193.strict_args_tab)
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
    let uu____23224 = expected_typ env_  in
    ((let uu___1802_23230 = env_  in
      {
        solver = (uu___1802_23230.solver);
        range = (uu___1802_23230.range);
        curmodule = (uu___1802_23230.curmodule);
        gamma = (uu___1802_23230.gamma);
        gamma_sig = (uu___1802_23230.gamma_sig);
        gamma_cache = (uu___1802_23230.gamma_cache);
        modules = (uu___1802_23230.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1802_23230.sigtab);
        attrtab = (uu___1802_23230.attrtab);
        instantiate_imp = (uu___1802_23230.instantiate_imp);
        effects = (uu___1802_23230.effects);
        generalize = (uu___1802_23230.generalize);
        letrecs = (uu___1802_23230.letrecs);
        top_level = (uu___1802_23230.top_level);
        check_uvars = (uu___1802_23230.check_uvars);
        use_eq = false;
        is_iface = (uu___1802_23230.is_iface);
        admit = (uu___1802_23230.admit);
        lax = (uu___1802_23230.lax);
        lax_universes = (uu___1802_23230.lax_universes);
        phase1 = (uu___1802_23230.phase1);
        failhard = (uu___1802_23230.failhard);
        nosynth = (uu___1802_23230.nosynth);
        uvar_subtyping = (uu___1802_23230.uvar_subtyping);
        tc_term = (uu___1802_23230.tc_term);
        type_of = (uu___1802_23230.type_of);
        universe_of = (uu___1802_23230.universe_of);
        check_type_of = (uu___1802_23230.check_type_of);
        use_bv_sorts = (uu___1802_23230.use_bv_sorts);
        qtbl_name_and_index = (uu___1802_23230.qtbl_name_and_index);
        normalized_eff_names = (uu___1802_23230.normalized_eff_names);
        fv_delta_depths = (uu___1802_23230.fv_delta_depths);
        proof_ns = (uu___1802_23230.proof_ns);
        synth_hook = (uu___1802_23230.synth_hook);
        splice = (uu___1802_23230.splice);
        postprocess = (uu___1802_23230.postprocess);
        is_native_tactic = (uu___1802_23230.is_native_tactic);
        identifier_info = (uu___1802_23230.identifier_info);
        tc_hooks = (uu___1802_23230.tc_hooks);
        dsenv = (uu___1802_23230.dsenv);
        nbe = (uu___1802_23230.nbe);
        strict_args_tab = (uu___1802_23230.strict_args_tab)
      }), uu____23224)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23242 =
      let uu____23245 = FStar_Ident.id_of_text ""  in [uu____23245]  in
    FStar_Ident.lid_of_ids uu____23242  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23252 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23252
        then
          let uu____23257 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23257 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1810_23285 = env  in
       {
         solver = (uu___1810_23285.solver);
         range = (uu___1810_23285.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1810_23285.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1810_23285.expected_typ);
         sigtab = (uu___1810_23285.sigtab);
         attrtab = (uu___1810_23285.attrtab);
         instantiate_imp = (uu___1810_23285.instantiate_imp);
         effects = (uu___1810_23285.effects);
         generalize = (uu___1810_23285.generalize);
         letrecs = (uu___1810_23285.letrecs);
         top_level = (uu___1810_23285.top_level);
         check_uvars = (uu___1810_23285.check_uvars);
         use_eq = (uu___1810_23285.use_eq);
         is_iface = (uu___1810_23285.is_iface);
         admit = (uu___1810_23285.admit);
         lax = (uu___1810_23285.lax);
         lax_universes = (uu___1810_23285.lax_universes);
         phase1 = (uu___1810_23285.phase1);
         failhard = (uu___1810_23285.failhard);
         nosynth = (uu___1810_23285.nosynth);
         uvar_subtyping = (uu___1810_23285.uvar_subtyping);
         tc_term = (uu___1810_23285.tc_term);
         type_of = (uu___1810_23285.type_of);
         universe_of = (uu___1810_23285.universe_of);
         check_type_of = (uu___1810_23285.check_type_of);
         use_bv_sorts = (uu___1810_23285.use_bv_sorts);
         qtbl_name_and_index = (uu___1810_23285.qtbl_name_and_index);
         normalized_eff_names = (uu___1810_23285.normalized_eff_names);
         fv_delta_depths = (uu___1810_23285.fv_delta_depths);
         proof_ns = (uu___1810_23285.proof_ns);
         synth_hook = (uu___1810_23285.synth_hook);
         splice = (uu___1810_23285.splice);
         postprocess = (uu___1810_23285.postprocess);
         is_native_tactic = (uu___1810_23285.is_native_tactic);
         identifier_info = (uu___1810_23285.identifier_info);
         tc_hooks = (uu___1810_23285.tc_hooks);
         dsenv = (uu___1810_23285.dsenv);
         nbe = (uu___1810_23285.nbe);
         strict_args_tab = (uu___1810_23285.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23337)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23341,(uu____23342,t)))::tl1
          ->
          let uu____23363 =
            let uu____23366 = FStar_Syntax_Free.uvars t  in
            ext out uu____23366  in
          aux uu____23363 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23369;
            FStar_Syntax_Syntax.index = uu____23370;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23378 =
            let uu____23381 = FStar_Syntax_Free.uvars t  in
            ext out uu____23381  in
          aux uu____23378 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23439)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23443,(uu____23444,t)))::tl1
          ->
          let uu____23465 =
            let uu____23468 = FStar_Syntax_Free.univs t  in
            ext out uu____23468  in
          aux uu____23465 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23471;
            FStar_Syntax_Syntax.index = uu____23472;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23480 =
            let uu____23483 = FStar_Syntax_Free.univs t  in
            ext out uu____23483  in
          aux uu____23480 tl1
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
          let uu____23545 = FStar_Util.set_add uname out  in
          aux uu____23545 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23548,(uu____23549,t)))::tl1
          ->
          let uu____23570 =
            let uu____23573 = FStar_Syntax_Free.univnames t  in
            ext out uu____23573  in
          aux uu____23570 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23576;
            FStar_Syntax_Syntax.index = uu____23577;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23585 =
            let uu____23588 = FStar_Syntax_Free.univnames t  in
            ext out uu____23588  in
          aux uu____23585 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_23609  ->
            match uu___11_23609 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23613 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23626 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23637 =
      let uu____23646 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23646
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23637 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23694 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_23707  ->
              match uu___12_23707 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23710 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____23710
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23716) ->
                  let uu____23733 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____23733))
       in
    FStar_All.pipe_right uu____23694 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_23747  ->
    match uu___13_23747 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23753 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____23753
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23776  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23831) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____23864,uu____23865) -> false  in
      let uu____23879 =
        FStar_List.tryFind
          (fun uu____23901  ->
             match uu____23901 with | (p,uu____23912) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____23879 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23931,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23961 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23961
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1953_23983 = e  in
        {
          solver = (uu___1953_23983.solver);
          range = (uu___1953_23983.range);
          curmodule = (uu___1953_23983.curmodule);
          gamma = (uu___1953_23983.gamma);
          gamma_sig = (uu___1953_23983.gamma_sig);
          gamma_cache = (uu___1953_23983.gamma_cache);
          modules = (uu___1953_23983.modules);
          expected_typ = (uu___1953_23983.expected_typ);
          sigtab = (uu___1953_23983.sigtab);
          attrtab = (uu___1953_23983.attrtab);
          instantiate_imp = (uu___1953_23983.instantiate_imp);
          effects = (uu___1953_23983.effects);
          generalize = (uu___1953_23983.generalize);
          letrecs = (uu___1953_23983.letrecs);
          top_level = (uu___1953_23983.top_level);
          check_uvars = (uu___1953_23983.check_uvars);
          use_eq = (uu___1953_23983.use_eq);
          is_iface = (uu___1953_23983.is_iface);
          admit = (uu___1953_23983.admit);
          lax = (uu___1953_23983.lax);
          lax_universes = (uu___1953_23983.lax_universes);
          phase1 = (uu___1953_23983.phase1);
          failhard = (uu___1953_23983.failhard);
          nosynth = (uu___1953_23983.nosynth);
          uvar_subtyping = (uu___1953_23983.uvar_subtyping);
          tc_term = (uu___1953_23983.tc_term);
          type_of = (uu___1953_23983.type_of);
          universe_of = (uu___1953_23983.universe_of);
          check_type_of = (uu___1953_23983.check_type_of);
          use_bv_sorts = (uu___1953_23983.use_bv_sorts);
          qtbl_name_and_index = (uu___1953_23983.qtbl_name_and_index);
          normalized_eff_names = (uu___1953_23983.normalized_eff_names);
          fv_delta_depths = (uu___1953_23983.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1953_23983.synth_hook);
          splice = (uu___1953_23983.splice);
          postprocess = (uu___1953_23983.postprocess);
          is_native_tactic = (uu___1953_23983.is_native_tactic);
          identifier_info = (uu___1953_23983.identifier_info);
          tc_hooks = (uu___1953_23983.tc_hooks);
          dsenv = (uu___1953_23983.dsenv);
          nbe = (uu___1953_23983.nbe);
          strict_args_tab = (uu___1953_23983.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1962_24031 = e  in
      {
        solver = (uu___1962_24031.solver);
        range = (uu___1962_24031.range);
        curmodule = (uu___1962_24031.curmodule);
        gamma = (uu___1962_24031.gamma);
        gamma_sig = (uu___1962_24031.gamma_sig);
        gamma_cache = (uu___1962_24031.gamma_cache);
        modules = (uu___1962_24031.modules);
        expected_typ = (uu___1962_24031.expected_typ);
        sigtab = (uu___1962_24031.sigtab);
        attrtab = (uu___1962_24031.attrtab);
        instantiate_imp = (uu___1962_24031.instantiate_imp);
        effects = (uu___1962_24031.effects);
        generalize = (uu___1962_24031.generalize);
        letrecs = (uu___1962_24031.letrecs);
        top_level = (uu___1962_24031.top_level);
        check_uvars = (uu___1962_24031.check_uvars);
        use_eq = (uu___1962_24031.use_eq);
        is_iface = (uu___1962_24031.is_iface);
        admit = (uu___1962_24031.admit);
        lax = (uu___1962_24031.lax);
        lax_universes = (uu___1962_24031.lax_universes);
        phase1 = (uu___1962_24031.phase1);
        failhard = (uu___1962_24031.failhard);
        nosynth = (uu___1962_24031.nosynth);
        uvar_subtyping = (uu___1962_24031.uvar_subtyping);
        tc_term = (uu___1962_24031.tc_term);
        type_of = (uu___1962_24031.type_of);
        universe_of = (uu___1962_24031.universe_of);
        check_type_of = (uu___1962_24031.check_type_of);
        use_bv_sorts = (uu___1962_24031.use_bv_sorts);
        qtbl_name_and_index = (uu___1962_24031.qtbl_name_and_index);
        normalized_eff_names = (uu___1962_24031.normalized_eff_names);
        fv_delta_depths = (uu___1962_24031.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1962_24031.synth_hook);
        splice = (uu___1962_24031.splice);
        postprocess = (uu___1962_24031.postprocess);
        is_native_tactic = (uu___1962_24031.is_native_tactic);
        identifier_info = (uu___1962_24031.identifier_info);
        tc_hooks = (uu___1962_24031.tc_hooks);
        dsenv = (uu___1962_24031.dsenv);
        nbe = (uu___1962_24031.nbe);
        strict_args_tab = (uu___1962_24031.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24047 = FStar_Syntax_Free.names t  in
      let uu____24050 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24047 uu____24050
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24073 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24073
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24083 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24083
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24104 =
      match uu____24104 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24124 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24124)
       in
    let uu____24132 =
      let uu____24136 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24136 FStar_List.rev  in
    FStar_All.pipe_right uu____24132 (FStar_String.concat " ")
  
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
                  (let uu____24206 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24206 with
                   | FStar_Pervasives_Native.Some uu____24210 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24213 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24223;
        univ_ineqs = uu____24224; implicits = uu____24225;_} -> true
    | uu____24237 -> false
  
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
          let uu___2006_24268 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2006_24268.deferred);
            univ_ineqs = (uu___2006_24268.univ_ineqs);
            implicits = (uu___2006_24268.implicits)
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
          let uu____24307 = FStar_Options.defensive ()  in
          if uu____24307
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24313 =
              let uu____24315 =
                let uu____24317 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24317  in
              Prims.op_Negation uu____24315  in
            (if uu____24313
             then
               let uu____24324 =
                 let uu____24330 =
                   let uu____24332 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24334 =
                     let uu____24336 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24336
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24332 uu____24334
                    in
                 (FStar_Errors.Warning_Defensive, uu____24330)  in
               FStar_Errors.log_issue rng uu____24324
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
          let uu____24376 =
            let uu____24378 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24378  in
          if uu____24376
          then ()
          else
            (let uu____24383 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24383 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24409 =
            let uu____24411 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24411  in
          if uu____24409
          then ()
          else
            (let uu____24416 = bound_vars e  in
             def_check_closed_in rng msg uu____24416 t)
  
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
          let uu___2043_24455 = g  in
          let uu____24456 =
            let uu____24457 =
              let uu____24458 =
                let uu____24465 =
                  let uu____24466 =
                    let uu____24483 =
                      let uu____24494 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24494]  in
                    (f, uu____24483)  in
                  FStar_Syntax_Syntax.Tm_app uu____24466  in
                FStar_Syntax_Syntax.mk uu____24465  in
              uu____24458 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24531  -> FStar_TypeChecker_Common.NonTrivial _24531)
              uu____24457
             in
          {
            guard_f = uu____24456;
            deferred = (uu___2043_24455.deferred);
            univ_ineqs = (uu___2043_24455.univ_ineqs);
            implicits = (uu___2043_24455.implicits)
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
          let uu___2050_24549 = g  in
          let uu____24550 =
            let uu____24551 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24551  in
          {
            guard_f = uu____24550;
            deferred = (uu___2050_24549.deferred);
            univ_ineqs = (uu___2050_24549.univ_ineqs);
            implicits = (uu___2050_24549.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2055_24568 = g  in
          let uu____24569 =
            let uu____24570 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24570  in
          {
            guard_f = uu____24569;
            deferred = (uu___2055_24568.deferred);
            univ_ineqs = (uu___2055_24568.univ_ineqs);
            implicits = (uu___2055_24568.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2059_24572 = g  in
          let uu____24573 =
            let uu____24574 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24574  in
          {
            guard_f = uu____24573;
            deferred = (uu___2059_24572.deferred);
            univ_ineqs = (uu___2059_24572.univ_ineqs);
            implicits = (uu___2059_24572.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24581 ->
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
          let uu____24598 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24598
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24605 =
      let uu____24606 = FStar_Syntax_Util.unmeta t  in
      uu____24606.FStar_Syntax_Syntax.n  in
    match uu____24605 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24610 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24653 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24653;
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
                       let uu____24748 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24748
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2114_24755 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2114_24755.deferred);
              univ_ineqs = (uu___2114_24755.univ_ineqs);
              implicits = (uu___2114_24755.implicits)
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
               let uu____24789 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24789
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
            let uu___2129_24816 = g  in
            let uu____24817 =
              let uu____24818 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24818  in
            {
              guard_f = uu____24817;
              deferred = (uu___2129_24816.deferred);
              univ_ineqs = (uu___2129_24816.univ_ineqs);
              implicits = (uu___2129_24816.implicits)
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
              let uu____24876 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____24876 with
              | FStar_Pervasives_Native.Some
                  (uu____24901::(tm,uu____24903)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____24967 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____24985 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____24985;
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
                      let uu___2151_25017 = trivial_guard  in
                      {
                        guard_f = (uu___2151_25017.guard_f);
                        deferred = (uu___2151_25017.deferred);
                        univ_ineqs = (uu___2151_25017.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25035  -> ());
    push = (fun uu____25037  -> ());
    pop = (fun uu____25040  -> ());
    snapshot =
      (fun uu____25043  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25062  -> fun uu____25063  -> ());
    encode_sig = (fun uu____25078  -> fun uu____25079  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25085 =
             let uu____25092 = FStar_Options.peek ()  in (e, g, uu____25092)
              in
           [uu____25085]);
    solve = (fun uu____25108  -> fun uu____25109  -> fun uu____25110  -> ());
    finish = (fun uu____25117  -> ());
    refresh = (fun uu____25119  -> ())
  } 