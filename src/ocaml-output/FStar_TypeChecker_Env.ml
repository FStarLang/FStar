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
    }
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
        tc_hooks; dsenv; nbe = nbe1;_} -> solver
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> range
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> curmodule
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> gamma
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> gamma_sig
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> gamma_cache
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> modules
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> expected_typ
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> sigtab
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> attrtab
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> is_pattern
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> instantiate_imp
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> effects
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> generalize
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> letrecs
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> top_level
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> check_uvars
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> use_eq
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> is_iface
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> admit1
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> lax1
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> lax_universes
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> phase1
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> failhard
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> nosynth
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> uvar_subtyping
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> tc_term
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> type_of
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> universe_of
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> check_type_of
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> use_bv_sorts
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> qtbl_name_and_index
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> normalized_eff_names
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> fv_delta_depths
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> proof_ns
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> synth_hook
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> splice1
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> postprocess
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> is_native_tactic
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> identifier_info
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> tc_hooks
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> dsenv
  
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
        tc_hooks; dsenv; nbe = nbe1;_} -> nbe1
  
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
           (fun uu___0_11796  ->
              match uu___0_11796 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____11799 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____11799  in
                  let uu____11800 =
                    let uu____11801 = FStar_Syntax_Subst.compress y  in
                    uu____11801.FStar_Syntax_Syntax.n  in
                  (match uu____11800 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____11805 =
                         let uu___329_11806 = y1  in
                         let uu____11807 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___329_11806.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___329_11806.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____11807
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____11805
                   | uu____11810 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___335_11824 = env  in
      let uu____11825 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___335_11824.solver);
        range = (uu___335_11824.range);
        curmodule = (uu___335_11824.curmodule);
        gamma = uu____11825;
        gamma_sig = (uu___335_11824.gamma_sig);
        gamma_cache = (uu___335_11824.gamma_cache);
        modules = (uu___335_11824.modules);
        expected_typ = (uu___335_11824.expected_typ);
        sigtab = (uu___335_11824.sigtab);
        attrtab = (uu___335_11824.attrtab);
        is_pattern = (uu___335_11824.is_pattern);
        instantiate_imp = (uu___335_11824.instantiate_imp);
        effects = (uu___335_11824.effects);
        generalize = (uu___335_11824.generalize);
        letrecs = (uu___335_11824.letrecs);
        top_level = (uu___335_11824.top_level);
        check_uvars = (uu___335_11824.check_uvars);
        use_eq = (uu___335_11824.use_eq);
        is_iface = (uu___335_11824.is_iface);
        admit = (uu___335_11824.admit);
        lax = (uu___335_11824.lax);
        lax_universes = (uu___335_11824.lax_universes);
        phase1 = (uu___335_11824.phase1);
        failhard = (uu___335_11824.failhard);
        nosynth = (uu___335_11824.nosynth);
        uvar_subtyping = (uu___335_11824.uvar_subtyping);
        tc_term = (uu___335_11824.tc_term);
        type_of = (uu___335_11824.type_of);
        universe_of = (uu___335_11824.universe_of);
        check_type_of = (uu___335_11824.check_type_of);
        use_bv_sorts = (uu___335_11824.use_bv_sorts);
        qtbl_name_and_index = (uu___335_11824.qtbl_name_and_index);
        normalized_eff_names = (uu___335_11824.normalized_eff_names);
        fv_delta_depths = (uu___335_11824.fv_delta_depths);
        proof_ns = (uu___335_11824.proof_ns);
        synth_hook = (uu___335_11824.synth_hook);
        splice = (uu___335_11824.splice);
        postprocess = (uu___335_11824.postprocess);
        is_native_tactic = (uu___335_11824.is_native_tactic);
        identifier_info = (uu___335_11824.identifier_info);
        tc_hooks = (uu___335_11824.tc_hooks);
        dsenv = (uu___335_11824.dsenv);
        nbe = (uu___335_11824.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____11833  -> fun uu____11834  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___342_11856 = env  in
      {
        solver = (uu___342_11856.solver);
        range = (uu___342_11856.range);
        curmodule = (uu___342_11856.curmodule);
        gamma = (uu___342_11856.gamma);
        gamma_sig = (uu___342_11856.gamma_sig);
        gamma_cache = (uu___342_11856.gamma_cache);
        modules = (uu___342_11856.modules);
        expected_typ = (uu___342_11856.expected_typ);
        sigtab = (uu___342_11856.sigtab);
        attrtab = (uu___342_11856.attrtab);
        is_pattern = (uu___342_11856.is_pattern);
        instantiate_imp = (uu___342_11856.instantiate_imp);
        effects = (uu___342_11856.effects);
        generalize = (uu___342_11856.generalize);
        letrecs = (uu___342_11856.letrecs);
        top_level = (uu___342_11856.top_level);
        check_uvars = (uu___342_11856.check_uvars);
        use_eq = (uu___342_11856.use_eq);
        is_iface = (uu___342_11856.is_iface);
        admit = (uu___342_11856.admit);
        lax = (uu___342_11856.lax);
        lax_universes = (uu___342_11856.lax_universes);
        phase1 = (uu___342_11856.phase1);
        failhard = (uu___342_11856.failhard);
        nosynth = (uu___342_11856.nosynth);
        uvar_subtyping = (uu___342_11856.uvar_subtyping);
        tc_term = (uu___342_11856.tc_term);
        type_of = (uu___342_11856.type_of);
        universe_of = (uu___342_11856.universe_of);
        check_type_of = (uu___342_11856.check_type_of);
        use_bv_sorts = (uu___342_11856.use_bv_sorts);
        qtbl_name_and_index = (uu___342_11856.qtbl_name_and_index);
        normalized_eff_names = (uu___342_11856.normalized_eff_names);
        fv_delta_depths = (uu___342_11856.fv_delta_depths);
        proof_ns = (uu___342_11856.proof_ns);
        synth_hook = (uu___342_11856.synth_hook);
        splice = (uu___342_11856.splice);
        postprocess = (uu___342_11856.postprocess);
        is_native_tactic = (uu___342_11856.is_native_tactic);
        identifier_info = (uu___342_11856.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___342_11856.dsenv);
        nbe = (uu___342_11856.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___346_11868 = e  in
      let uu____11869 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___346_11868.solver);
        range = (uu___346_11868.range);
        curmodule = (uu___346_11868.curmodule);
        gamma = (uu___346_11868.gamma);
        gamma_sig = (uu___346_11868.gamma_sig);
        gamma_cache = (uu___346_11868.gamma_cache);
        modules = (uu___346_11868.modules);
        expected_typ = (uu___346_11868.expected_typ);
        sigtab = (uu___346_11868.sigtab);
        attrtab = (uu___346_11868.attrtab);
        is_pattern = (uu___346_11868.is_pattern);
        instantiate_imp = (uu___346_11868.instantiate_imp);
        effects = (uu___346_11868.effects);
        generalize = (uu___346_11868.generalize);
        letrecs = (uu___346_11868.letrecs);
        top_level = (uu___346_11868.top_level);
        check_uvars = (uu___346_11868.check_uvars);
        use_eq = (uu___346_11868.use_eq);
        is_iface = (uu___346_11868.is_iface);
        admit = (uu___346_11868.admit);
        lax = (uu___346_11868.lax);
        lax_universes = (uu___346_11868.lax_universes);
        phase1 = (uu___346_11868.phase1);
        failhard = (uu___346_11868.failhard);
        nosynth = (uu___346_11868.nosynth);
        uvar_subtyping = (uu___346_11868.uvar_subtyping);
        tc_term = (uu___346_11868.tc_term);
        type_of = (uu___346_11868.type_of);
        universe_of = (uu___346_11868.universe_of);
        check_type_of = (uu___346_11868.check_type_of);
        use_bv_sorts = (uu___346_11868.use_bv_sorts);
        qtbl_name_and_index = (uu___346_11868.qtbl_name_and_index);
        normalized_eff_names = (uu___346_11868.normalized_eff_names);
        fv_delta_depths = (uu___346_11868.fv_delta_depths);
        proof_ns = (uu___346_11868.proof_ns);
        synth_hook = (uu___346_11868.synth_hook);
        splice = (uu___346_11868.splice);
        postprocess = (uu___346_11868.postprocess);
        is_native_tactic = (uu___346_11868.is_native_tactic);
        identifier_info = (uu___346_11868.identifier_info);
        tc_hooks = (uu___346_11868.tc_hooks);
        dsenv = uu____11869;
        nbe = (uu___346_11868.nbe)
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
      | (NoDelta ,uu____11898) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____11901,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____11903,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____11906 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____11920 . unit -> 'Auu____11920 FStar_Util.smap =
  fun uu____11927  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____11933 . unit -> 'Auu____11933 FStar_Util.smap =
  fun uu____11940  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____12078 = new_gamma_cache ()  in
                  let uu____12081 = new_sigtab ()  in
                  let uu____12084 = new_sigtab ()  in
                  let uu____12091 =
                    let uu____12106 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12106, FStar_Pervasives_Native.None)  in
                  let uu____12127 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12131 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12135 = FStar_Options.using_facts_from ()  in
                  let uu____12136 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12139 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12078;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12081;
                    attrtab = uu____12084;
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
                    qtbl_name_and_index = uu____12091;
                    normalized_eff_names = uu____12127;
                    fv_delta_depths = uu____12131;
                    proof_ns = uu____12135;
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
                    is_native_tactic = (fun uu____12201  -> false);
                    identifier_info = uu____12136;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12139;
                    nbe = nbe1
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
  fun uu____12280  ->
    let uu____12281 = FStar_ST.op_Bang query_indices  in
    match uu____12281 with
    | [] -> failwith "Empty query indices!"
    | uu____12336 ->
        let uu____12346 =
          let uu____12356 =
            let uu____12364 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12364  in
          let uu____12418 = FStar_ST.op_Bang query_indices  in uu____12356 ::
            uu____12418
           in
        FStar_ST.op_Colon_Equals query_indices uu____12346
  
let (pop_query_indices : unit -> unit) =
  fun uu____12514  ->
    let uu____12515 = FStar_ST.op_Bang query_indices  in
    match uu____12515 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____12642  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____12679  ->
    match uu____12679 with
    | (l,n1) ->
        let uu____12689 = FStar_ST.op_Bang query_indices  in
        (match uu____12689 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____12811 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____12834  ->
    let uu____12835 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____12835
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____12903 =
       let uu____12906 = FStar_ST.op_Bang stack  in env :: uu____12906  in
     FStar_ST.op_Colon_Equals stack uu____12903);
    (let uu___414_12955 = env  in
     let uu____12956 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____12959 = FStar_Util.smap_copy (sigtab env)  in
     let uu____12962 = FStar_Util.smap_copy (attrtab env)  in
     let uu____12969 =
       let uu____12984 =
         let uu____12988 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____12988  in
       let uu____13020 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____12984, uu____13020)  in
     let uu____13069 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13072 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13075 =
       let uu____13078 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13078  in
     {
       solver = (uu___414_12955.solver);
       range = (uu___414_12955.range);
       curmodule = (uu___414_12955.curmodule);
       gamma = (uu___414_12955.gamma);
       gamma_sig = (uu___414_12955.gamma_sig);
       gamma_cache = uu____12956;
       modules = (uu___414_12955.modules);
       expected_typ = (uu___414_12955.expected_typ);
       sigtab = uu____12959;
       attrtab = uu____12962;
       is_pattern = (uu___414_12955.is_pattern);
       instantiate_imp = (uu___414_12955.instantiate_imp);
       effects = (uu___414_12955.effects);
       generalize = (uu___414_12955.generalize);
       letrecs = (uu___414_12955.letrecs);
       top_level = (uu___414_12955.top_level);
       check_uvars = (uu___414_12955.check_uvars);
       use_eq = (uu___414_12955.use_eq);
       is_iface = (uu___414_12955.is_iface);
       admit = (uu___414_12955.admit);
       lax = (uu___414_12955.lax);
       lax_universes = (uu___414_12955.lax_universes);
       phase1 = (uu___414_12955.phase1);
       failhard = (uu___414_12955.failhard);
       nosynth = (uu___414_12955.nosynth);
       uvar_subtyping = (uu___414_12955.uvar_subtyping);
       tc_term = (uu___414_12955.tc_term);
       type_of = (uu___414_12955.type_of);
       universe_of = (uu___414_12955.universe_of);
       check_type_of = (uu___414_12955.check_type_of);
       use_bv_sorts = (uu___414_12955.use_bv_sorts);
       qtbl_name_and_index = uu____12969;
       normalized_eff_names = uu____13069;
       fv_delta_depths = uu____13072;
       proof_ns = (uu___414_12955.proof_ns);
       synth_hook = (uu___414_12955.synth_hook);
       splice = (uu___414_12955.splice);
       postprocess = (uu___414_12955.postprocess);
       is_native_tactic = (uu___414_12955.is_native_tactic);
       identifier_info = uu____13075;
       tc_hooks = (uu___414_12955.tc_hooks);
       dsenv = (uu___414_12955.dsenv);
       nbe = (uu___414_12955.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13103  ->
    let uu____13104 = FStar_ST.op_Bang stack  in
    match uu____13104 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13158 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13248  ->
           let uu____13249 = snapshot_stack env  in
           match uu____13249 with
           | (stack_depth,env1) ->
               let uu____13283 = snapshot_query_indices ()  in
               (match uu____13283 with
                | (query_indices_depth,()) ->
                    let uu____13316 = (env1.solver).snapshot msg  in
                    (match uu____13316 with
                     | (solver_depth,()) ->
                         let uu____13373 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13373 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___439_13440 = env1  in
                                 {
                                   solver = (uu___439_13440.solver);
                                   range = (uu___439_13440.range);
                                   curmodule = (uu___439_13440.curmodule);
                                   gamma = (uu___439_13440.gamma);
                                   gamma_sig = (uu___439_13440.gamma_sig);
                                   gamma_cache = (uu___439_13440.gamma_cache);
                                   modules = (uu___439_13440.modules);
                                   expected_typ =
                                     (uu___439_13440.expected_typ);
                                   sigtab = (uu___439_13440.sigtab);
                                   attrtab = (uu___439_13440.attrtab);
                                   is_pattern = (uu___439_13440.is_pattern);
                                   instantiate_imp =
                                     (uu___439_13440.instantiate_imp);
                                   effects = (uu___439_13440.effects);
                                   generalize = (uu___439_13440.generalize);
                                   letrecs = (uu___439_13440.letrecs);
                                   top_level = (uu___439_13440.top_level);
                                   check_uvars = (uu___439_13440.check_uvars);
                                   use_eq = (uu___439_13440.use_eq);
                                   is_iface = (uu___439_13440.is_iface);
                                   admit = (uu___439_13440.admit);
                                   lax = (uu___439_13440.lax);
                                   lax_universes =
                                     (uu___439_13440.lax_universes);
                                   phase1 = (uu___439_13440.phase1);
                                   failhard = (uu___439_13440.failhard);
                                   nosynth = (uu___439_13440.nosynth);
                                   uvar_subtyping =
                                     (uu___439_13440.uvar_subtyping);
                                   tc_term = (uu___439_13440.tc_term);
                                   type_of = (uu___439_13440.type_of);
                                   universe_of = (uu___439_13440.universe_of);
                                   check_type_of =
                                     (uu___439_13440.check_type_of);
                                   use_bv_sorts =
                                     (uu___439_13440.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___439_13440.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___439_13440.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___439_13440.fv_delta_depths);
                                   proof_ns = (uu___439_13440.proof_ns);
                                   synth_hook = (uu___439_13440.synth_hook);
                                   splice = (uu___439_13440.splice);
                                   postprocess = (uu___439_13440.postprocess);
                                   is_native_tactic =
                                     (uu___439_13440.is_native_tactic);
                                   identifier_info =
                                     (uu___439_13440.identifier_info);
                                   tc_hooks = (uu___439_13440.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___439_13440.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13474  ->
             let uu____13475 =
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
             match uu____13475 with
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
                             ((let uu____13655 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13655
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13671 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13671
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____13703,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____13745 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____13775  ->
                  match uu____13775 with
                  | (m,uu____13783) -> FStar_Ident.lid_equals l m))
           in
        (match uu____13745 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___484_13798 = env  in
               {
                 solver = (uu___484_13798.solver);
                 range = (uu___484_13798.range);
                 curmodule = (uu___484_13798.curmodule);
                 gamma = (uu___484_13798.gamma);
                 gamma_sig = (uu___484_13798.gamma_sig);
                 gamma_cache = (uu___484_13798.gamma_cache);
                 modules = (uu___484_13798.modules);
                 expected_typ = (uu___484_13798.expected_typ);
                 sigtab = (uu___484_13798.sigtab);
                 attrtab = (uu___484_13798.attrtab);
                 is_pattern = (uu___484_13798.is_pattern);
                 instantiate_imp = (uu___484_13798.instantiate_imp);
                 effects = (uu___484_13798.effects);
                 generalize = (uu___484_13798.generalize);
                 letrecs = (uu___484_13798.letrecs);
                 top_level = (uu___484_13798.top_level);
                 check_uvars = (uu___484_13798.check_uvars);
                 use_eq = (uu___484_13798.use_eq);
                 is_iface = (uu___484_13798.is_iface);
                 admit = (uu___484_13798.admit);
                 lax = (uu___484_13798.lax);
                 lax_universes = (uu___484_13798.lax_universes);
                 phase1 = (uu___484_13798.phase1);
                 failhard = (uu___484_13798.failhard);
                 nosynth = (uu___484_13798.nosynth);
                 uvar_subtyping = (uu___484_13798.uvar_subtyping);
                 tc_term = (uu___484_13798.tc_term);
                 type_of = (uu___484_13798.type_of);
                 universe_of = (uu___484_13798.universe_of);
                 check_type_of = (uu___484_13798.check_type_of);
                 use_bv_sorts = (uu___484_13798.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___484_13798.normalized_eff_names);
                 fv_delta_depths = (uu___484_13798.fv_delta_depths);
                 proof_ns = (uu___484_13798.proof_ns);
                 synth_hook = (uu___484_13798.synth_hook);
                 splice = (uu___484_13798.splice);
                 postprocess = (uu___484_13798.postprocess);
                 is_native_tactic = (uu___484_13798.is_native_tactic);
                 identifier_info = (uu___484_13798.identifier_info);
                 tc_hooks = (uu___484_13798.tc_hooks);
                 dsenv = (uu___484_13798.dsenv);
                 nbe = (uu___484_13798.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____13815,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___493_13831 = env  in
               {
                 solver = (uu___493_13831.solver);
                 range = (uu___493_13831.range);
                 curmodule = (uu___493_13831.curmodule);
                 gamma = (uu___493_13831.gamma);
                 gamma_sig = (uu___493_13831.gamma_sig);
                 gamma_cache = (uu___493_13831.gamma_cache);
                 modules = (uu___493_13831.modules);
                 expected_typ = (uu___493_13831.expected_typ);
                 sigtab = (uu___493_13831.sigtab);
                 attrtab = (uu___493_13831.attrtab);
                 is_pattern = (uu___493_13831.is_pattern);
                 instantiate_imp = (uu___493_13831.instantiate_imp);
                 effects = (uu___493_13831.effects);
                 generalize = (uu___493_13831.generalize);
                 letrecs = (uu___493_13831.letrecs);
                 top_level = (uu___493_13831.top_level);
                 check_uvars = (uu___493_13831.check_uvars);
                 use_eq = (uu___493_13831.use_eq);
                 is_iface = (uu___493_13831.is_iface);
                 admit = (uu___493_13831.admit);
                 lax = (uu___493_13831.lax);
                 lax_universes = (uu___493_13831.lax_universes);
                 phase1 = (uu___493_13831.phase1);
                 failhard = (uu___493_13831.failhard);
                 nosynth = (uu___493_13831.nosynth);
                 uvar_subtyping = (uu___493_13831.uvar_subtyping);
                 tc_term = (uu___493_13831.tc_term);
                 type_of = (uu___493_13831.type_of);
                 universe_of = (uu___493_13831.universe_of);
                 check_type_of = (uu___493_13831.check_type_of);
                 use_bv_sorts = (uu___493_13831.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___493_13831.normalized_eff_names);
                 fv_delta_depths = (uu___493_13831.fv_delta_depths);
                 proof_ns = (uu___493_13831.proof_ns);
                 synth_hook = (uu___493_13831.synth_hook);
                 splice = (uu___493_13831.splice);
                 postprocess = (uu___493_13831.postprocess);
                 is_native_tactic = (uu___493_13831.is_native_tactic);
                 identifier_info = (uu___493_13831.identifier_info);
                 tc_hooks = (uu___493_13831.tc_hooks);
                 dsenv = (uu___493_13831.dsenv);
                 nbe = (uu___493_13831.nbe)
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
        (let uu___500_13874 = e  in
         {
           solver = (uu___500_13874.solver);
           range = r;
           curmodule = (uu___500_13874.curmodule);
           gamma = (uu___500_13874.gamma);
           gamma_sig = (uu___500_13874.gamma_sig);
           gamma_cache = (uu___500_13874.gamma_cache);
           modules = (uu___500_13874.modules);
           expected_typ = (uu___500_13874.expected_typ);
           sigtab = (uu___500_13874.sigtab);
           attrtab = (uu___500_13874.attrtab);
           is_pattern = (uu___500_13874.is_pattern);
           instantiate_imp = (uu___500_13874.instantiate_imp);
           effects = (uu___500_13874.effects);
           generalize = (uu___500_13874.generalize);
           letrecs = (uu___500_13874.letrecs);
           top_level = (uu___500_13874.top_level);
           check_uvars = (uu___500_13874.check_uvars);
           use_eq = (uu___500_13874.use_eq);
           is_iface = (uu___500_13874.is_iface);
           admit = (uu___500_13874.admit);
           lax = (uu___500_13874.lax);
           lax_universes = (uu___500_13874.lax_universes);
           phase1 = (uu___500_13874.phase1);
           failhard = (uu___500_13874.failhard);
           nosynth = (uu___500_13874.nosynth);
           uvar_subtyping = (uu___500_13874.uvar_subtyping);
           tc_term = (uu___500_13874.tc_term);
           type_of = (uu___500_13874.type_of);
           universe_of = (uu___500_13874.universe_of);
           check_type_of = (uu___500_13874.check_type_of);
           use_bv_sorts = (uu___500_13874.use_bv_sorts);
           qtbl_name_and_index = (uu___500_13874.qtbl_name_and_index);
           normalized_eff_names = (uu___500_13874.normalized_eff_names);
           fv_delta_depths = (uu___500_13874.fv_delta_depths);
           proof_ns = (uu___500_13874.proof_ns);
           synth_hook = (uu___500_13874.synth_hook);
           splice = (uu___500_13874.splice);
           postprocess = (uu___500_13874.postprocess);
           is_native_tactic = (uu___500_13874.is_native_tactic);
           identifier_info = (uu___500_13874.identifier_info);
           tc_hooks = (uu___500_13874.tc_hooks);
           dsenv = (uu___500_13874.dsenv);
           nbe = (uu___500_13874.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____13894 =
        let uu____13895 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____13895 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____13894
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____13950 =
          let uu____13951 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____13951 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____13950
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14006 =
          let uu____14007 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14007 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14006
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14062 =
        let uu____14063 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14063 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14062
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___517_14127 = env  in
      {
        solver = (uu___517_14127.solver);
        range = (uu___517_14127.range);
        curmodule = lid;
        gamma = (uu___517_14127.gamma);
        gamma_sig = (uu___517_14127.gamma_sig);
        gamma_cache = (uu___517_14127.gamma_cache);
        modules = (uu___517_14127.modules);
        expected_typ = (uu___517_14127.expected_typ);
        sigtab = (uu___517_14127.sigtab);
        attrtab = (uu___517_14127.attrtab);
        is_pattern = (uu___517_14127.is_pattern);
        instantiate_imp = (uu___517_14127.instantiate_imp);
        effects = (uu___517_14127.effects);
        generalize = (uu___517_14127.generalize);
        letrecs = (uu___517_14127.letrecs);
        top_level = (uu___517_14127.top_level);
        check_uvars = (uu___517_14127.check_uvars);
        use_eq = (uu___517_14127.use_eq);
        is_iface = (uu___517_14127.is_iface);
        admit = (uu___517_14127.admit);
        lax = (uu___517_14127.lax);
        lax_universes = (uu___517_14127.lax_universes);
        phase1 = (uu___517_14127.phase1);
        failhard = (uu___517_14127.failhard);
        nosynth = (uu___517_14127.nosynth);
        uvar_subtyping = (uu___517_14127.uvar_subtyping);
        tc_term = (uu___517_14127.tc_term);
        type_of = (uu___517_14127.type_of);
        universe_of = (uu___517_14127.universe_of);
        check_type_of = (uu___517_14127.check_type_of);
        use_bv_sorts = (uu___517_14127.use_bv_sorts);
        qtbl_name_and_index = (uu___517_14127.qtbl_name_and_index);
        normalized_eff_names = (uu___517_14127.normalized_eff_names);
        fv_delta_depths = (uu___517_14127.fv_delta_depths);
        proof_ns = (uu___517_14127.proof_ns);
        synth_hook = (uu___517_14127.synth_hook);
        splice = (uu___517_14127.splice);
        postprocess = (uu___517_14127.postprocess);
        is_native_tactic = (uu___517_14127.is_native_tactic);
        identifier_info = (uu___517_14127.identifier_info);
        tc_hooks = (uu___517_14127.tc_hooks);
        dsenv = (uu___517_14127.dsenv);
        nbe = (uu___517_14127.nbe)
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
      let uu____14158 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14158
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14171 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14171)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14186 =
      let uu____14188 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14188  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14186)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14197  ->
    let uu____14198 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14198
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
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
      | ((formals,t),uu____14298) ->
          let vs = mk_univ_subst formals us  in
          let uu____14322 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14322)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14339  ->
    match uu___1_14339 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14365  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14385 = inst_tscheme t  in
      match uu____14385 with
      | (us,t1) ->
          let uu____14396 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14396)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14417  ->
          match uu____14417 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____14439 =
                         let uu____14441 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____14445 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____14449 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____14451 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____14441 uu____14445 uu____14449 uu____14451
                          in
                       failwith uu____14439)
                    else ();
                    (let uu____14456 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____14456))
               | uu____14465 ->
                   let uu____14466 =
                     let uu____14468 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____14468
                      in
                   failwith uu____14466)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14480 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14491 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14502 -> false
  
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
             | ([],uu____14550) -> Maybe
             | (uu____14557,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14577 -> No  in
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
          let uu____14671 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14671 with
          | FStar_Pervasives_Native.None  ->
              let uu____14694 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_14738  ->
                     match uu___2_14738 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____14777 = FStar_Ident.lid_equals lid l  in
                         if uu____14777
                         then
                           let uu____14800 =
                             let uu____14819 =
                               let uu____14834 = inst_tscheme t  in
                               FStar_Util.Inl uu____14834  in
                             let uu____14849 = FStar_Ident.range_of_lid l  in
                             (uu____14819, uu____14849)  in
                           FStar_Pervasives_Native.Some uu____14800
                         else FStar_Pervasives_Native.None
                     | uu____14902 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____14694
                (fun uu____14940  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_14949  ->
                        match uu___3_14949 with
                        | (uu____14952,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____14954);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____14955;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____14956;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____14957;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____14958;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____14978 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____14978
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
                                  uu____15030 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15037 -> cache t  in
                            let uu____15038 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15038 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15044 =
                                   let uu____15045 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15045)
                                    in
                                 maybe_cache uu____15044)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15116 = find_in_sigtab env lid  in
         match uu____15116 with
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
      let uu____15197 = lookup_qname env lid  in
      match uu____15197 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15218,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15332 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15332 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15377 =
          let uu____15380 = lookup_attr env1 attr  in se1 :: uu____15380  in
        FStar_Util.smap_add (attrtab env1) attr uu____15377  in
      FStar_List.iter
        (fun attr  ->
           let uu____15390 =
             let uu____15391 = FStar_Syntax_Subst.compress attr  in
             uu____15391.FStar_Syntax_Syntax.n  in
           match uu____15390 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15395 =
                 let uu____15397 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15397.FStar_Ident.str  in
               add_one1 env se uu____15395
           | uu____15398 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15421) ->
          add_sigelts env ses
      | uu____15430 ->
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
            | uu____15445 -> ()))

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
        (fun uu___4_15477  ->
           match uu___4_15477 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15495 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____15557,lb::[]),uu____15559) ->
            let uu____15568 =
              let uu____15577 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15586 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15577, uu____15586)  in
            FStar_Pervasives_Native.Some uu____15568
        | FStar_Syntax_Syntax.Sig_let ((uu____15599,lbs),uu____15601) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15633 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15646 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15646
                     then
                       let uu____15659 =
                         let uu____15668 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____15677 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15668, uu____15677)  in
                       FStar_Pervasives_Native.Some uu____15659
                     else FStar_Pervasives_Native.None)
        | uu____15700 -> FStar_Pervasives_Native.None
  
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
          let uu____15760 =
            let uu____15769 =
              let uu____15774 =
                let uu____15775 =
                  let uu____15778 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____15778
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____15775)  in
              inst_tscheme1 uu____15774  in
            (uu____15769, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15760
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____15800,uu____15801) ->
          let uu____15806 =
            let uu____15815 =
              let uu____15820 =
                let uu____15821 =
                  let uu____15824 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____15824  in
                (us, uu____15821)  in
              inst_tscheme1 uu____15820  in
            (uu____15815, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15806
      | uu____15843 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____15932 =
          match uu____15932 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16028,uvs,t,uu____16031,uu____16032,uu____16033);
                      FStar_Syntax_Syntax.sigrng = uu____16034;
                      FStar_Syntax_Syntax.sigquals = uu____16035;
                      FStar_Syntax_Syntax.sigmeta = uu____16036;
                      FStar_Syntax_Syntax.sigattrs = uu____16037;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16060 =
                     let uu____16069 = inst_tscheme1 (uvs, t)  in
                     (uu____16069, rng)  in
                   FStar_Pervasives_Native.Some uu____16060
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16093;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16095;
                      FStar_Syntax_Syntax.sigattrs = uu____16096;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16113 =
                     let uu____16115 = in_cur_mod env l  in uu____16115 = Yes
                      in
                   if uu____16113
                   then
                     let uu____16127 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16127
                      then
                        let uu____16143 =
                          let uu____16152 = inst_tscheme1 (uvs, t)  in
                          (uu____16152, rng)  in
                        FStar_Pervasives_Native.Some uu____16143
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16185 =
                        let uu____16194 = inst_tscheme1 (uvs, t)  in
                        (uu____16194, rng)  in
                      FStar_Pervasives_Native.Some uu____16185)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16219,uu____16220);
                      FStar_Syntax_Syntax.sigrng = uu____16221;
                      FStar_Syntax_Syntax.sigquals = uu____16222;
                      FStar_Syntax_Syntax.sigmeta = uu____16223;
                      FStar_Syntax_Syntax.sigattrs = uu____16224;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16265 =
                          let uu____16274 = inst_tscheme1 (uvs, k)  in
                          (uu____16274, rng)  in
                        FStar_Pervasives_Native.Some uu____16265
                    | uu____16295 ->
                        let uu____16296 =
                          let uu____16305 =
                            let uu____16310 =
                              let uu____16311 =
                                let uu____16314 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16314
                                 in
                              (uvs, uu____16311)  in
                            inst_tscheme1 uu____16310  in
                          (uu____16305, rng)  in
                        FStar_Pervasives_Native.Some uu____16296)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16337,uu____16338);
                      FStar_Syntax_Syntax.sigrng = uu____16339;
                      FStar_Syntax_Syntax.sigquals = uu____16340;
                      FStar_Syntax_Syntax.sigmeta = uu____16341;
                      FStar_Syntax_Syntax.sigattrs = uu____16342;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16384 =
                          let uu____16393 = inst_tscheme_with (uvs, k) us  in
                          (uu____16393, rng)  in
                        FStar_Pervasives_Native.Some uu____16384
                    | uu____16414 ->
                        let uu____16415 =
                          let uu____16424 =
                            let uu____16429 =
                              let uu____16430 =
                                let uu____16433 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16433
                                 in
                              (uvs, uu____16430)  in
                            inst_tscheme_with uu____16429 us  in
                          (uu____16424, rng)  in
                        FStar_Pervasives_Native.Some uu____16415)
               | FStar_Util.Inr se ->
                   let uu____16469 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16490;
                          FStar_Syntax_Syntax.sigrng = uu____16491;
                          FStar_Syntax_Syntax.sigquals = uu____16492;
                          FStar_Syntax_Syntax.sigmeta = uu____16493;
                          FStar_Syntax_Syntax.sigattrs = uu____16494;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16509 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____16469
                     (FStar_Util.map_option
                        (fun uu____16557  ->
                           match uu____16557 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16588 =
          let uu____16599 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16599 mapper  in
        match uu____16588 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____16673 =
              let uu____16684 =
                let uu____16691 =
                  let uu___844_16694 = t  in
                  let uu____16695 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___844_16694.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____16695;
                    FStar_Syntax_Syntax.vars =
                      (uu___844_16694.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____16691)  in
              (uu____16684, r)  in
            FStar_Pervasives_Native.Some uu____16673
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16744 = lookup_qname env l  in
      match uu____16744 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____16765 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____16819 = try_lookup_bv env bv  in
      match uu____16819 with
      | FStar_Pervasives_Native.None  ->
          let uu____16834 = variable_not_found bv  in
          FStar_Errors.raise_error uu____16834 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____16850 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____16851 =
            let uu____16852 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____16852  in
          (uu____16850, uu____16851)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____16874 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____16874 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____16940 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____16940  in
          let uu____16941 =
            let uu____16950 =
              let uu____16955 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____16955)  in
            (uu____16950, r1)  in
          FStar_Pervasives_Native.Some uu____16941
  
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
        let uu____16990 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____16990 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17023,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17048 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17048  in
            let uu____17049 =
              let uu____17054 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17054, r1)  in
            FStar_Pervasives_Native.Some uu____17049
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17078 = try_lookup_lid env l  in
      match uu____17078 with
      | FStar_Pervasives_Native.None  ->
          let uu____17105 = name_not_found l  in
          let uu____17111 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17105 uu____17111
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17154  ->
              match uu___5_17154 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17158 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17179 = lookup_qname env lid  in
      match uu____17179 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17188,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17191;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17193;
              FStar_Syntax_Syntax.sigattrs = uu____17194;_},FStar_Pervasives_Native.None
            ),uu____17195)
          ->
          let uu____17244 =
            let uu____17251 =
              let uu____17252 =
                let uu____17255 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17255 t  in
              (uvs, uu____17252)  in
            (uu____17251, q)  in
          FStar_Pervasives_Native.Some uu____17244
      | uu____17268 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17290 = lookup_qname env lid  in
      match uu____17290 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17295,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17298;
              FStar_Syntax_Syntax.sigquals = uu____17299;
              FStar_Syntax_Syntax.sigmeta = uu____17300;
              FStar_Syntax_Syntax.sigattrs = uu____17301;_},FStar_Pervasives_Native.None
            ),uu____17302)
          ->
          let uu____17351 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17351 (uvs, t)
      | uu____17356 ->
          let uu____17357 = name_not_found lid  in
          let uu____17363 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17357 uu____17363
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17383 = lookup_qname env lid  in
      match uu____17383 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17388,uvs,t,uu____17391,uu____17392,uu____17393);
              FStar_Syntax_Syntax.sigrng = uu____17394;
              FStar_Syntax_Syntax.sigquals = uu____17395;
              FStar_Syntax_Syntax.sigmeta = uu____17396;
              FStar_Syntax_Syntax.sigattrs = uu____17397;_},FStar_Pervasives_Native.None
            ),uu____17398)
          ->
          let uu____17453 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17453 (uvs, t)
      | uu____17458 ->
          let uu____17459 = name_not_found lid  in
          let uu____17465 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17459 uu____17465
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17488 = lookup_qname env lid  in
      match uu____17488 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17496,uu____17497,uu____17498,uu____17499,uu____17500,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17502;
              FStar_Syntax_Syntax.sigquals = uu____17503;
              FStar_Syntax_Syntax.sigmeta = uu____17504;
              FStar_Syntax_Syntax.sigattrs = uu____17505;_},uu____17506),uu____17507)
          -> (true, dcs)
      | uu____17570 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17586 = lookup_qname env lid  in
      match uu____17586 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17587,uu____17588,uu____17589,l,uu____17591,uu____17592);
              FStar_Syntax_Syntax.sigrng = uu____17593;
              FStar_Syntax_Syntax.sigquals = uu____17594;
              FStar_Syntax_Syntax.sigmeta = uu____17595;
              FStar_Syntax_Syntax.sigattrs = uu____17596;_},uu____17597),uu____17598)
          -> l
      | uu____17655 ->
          let uu____17656 =
            let uu____17658 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____17658  in
          failwith uu____17656
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____17728)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____17785) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____17809 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____17809
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____17844 -> FStar_Pervasives_Native.None)
          | uu____17853 -> FStar_Pervasives_Native.None
  
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
        let uu____17915 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____17915
  
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
        let uu____17948 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____17948
  
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
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____18000,uu____18001) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18050),uu____18051) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18100 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18118 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18128 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18145 ->
                  let uu____18152 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18152
              | FStar_Syntax_Syntax.Sig_let ((uu____18153,lbs),uu____18155)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18171 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18171
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18178 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18186 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18187 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18194 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18195 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18196 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18197 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18210 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18228 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18228
           (fun d_opt  ->
              let uu____18241 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18241
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18251 =
                   let uu____18254 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18254  in
                 match uu____18251 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18255 =
                       let uu____18257 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18257
                        in
                     failwith uu____18255
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18262 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18262
                       then
                         let uu____18265 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18267 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18269 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18265 uu____18267 uu____18269
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
        (FStar_Util.Inr (se,uu____18294),uu____18295) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18344 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18366),uu____18367) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18416 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18438 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18438
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____18461 = lookup_attrs_of_lid env fv_lid1  in
        match uu____18461 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18485 =
                      let uu____18486 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18486.FStar_Syntax_Syntax.n  in
                    match uu____18485 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____18491 -> false))
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____18525 = lookup_qname env ftv  in
      match uu____18525 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18529) ->
          let uu____18574 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____18574 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____18595,t),r) ->
               let uu____18610 =
                 let uu____18611 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____18611 t  in
               FStar_Pervasives_Native.Some uu____18610)
      | uu____18612 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____18624 = try_lookup_effect_lid env ftv  in
      match uu____18624 with
      | FStar_Pervasives_Native.None  ->
          let uu____18627 = name_not_found ftv  in
          let uu____18633 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____18627 uu____18633
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
        let uu____18657 = lookup_qname env lid0  in
        match uu____18657 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____18668);
                FStar_Syntax_Syntax.sigrng = uu____18669;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____18671;
                FStar_Syntax_Syntax.sigattrs = uu____18672;_},FStar_Pervasives_Native.None
              ),uu____18673)
            ->
            let lid1 =
              let uu____18727 =
                let uu____18728 = FStar_Ident.range_of_lid lid  in
                let uu____18729 =
                  let uu____18730 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____18730  in
                FStar_Range.set_use_range uu____18728 uu____18729  in
              FStar_Ident.set_lid_range lid uu____18727  in
            let uu____18731 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_18737  ->
                      match uu___6_18737 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____18740 -> false))
               in
            if uu____18731
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____18759 =
                      let uu____18761 =
                        let uu____18763 = get_range env  in
                        FStar_Range.string_of_range uu____18763  in
                      let uu____18764 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____18766 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____18761 uu____18764 uu____18766
                       in
                    failwith uu____18759)
                  in
               match (binders, univs1) with
               | ([],uu____18787) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____18813,uu____18814::uu____18815::uu____18816) ->
                   let uu____18837 =
                     let uu____18839 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____18841 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____18839 uu____18841
                      in
                   failwith uu____18837
               | uu____18852 ->
                   let uu____18867 =
                     let uu____18872 =
                       let uu____18873 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____18873)  in
                     inst_tscheme_with uu____18872 insts  in
                   (match uu____18867 with
                    | (uu____18886,t) ->
                        let t1 =
                          let uu____18889 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____18889 t  in
                        let uu____18890 =
                          let uu____18891 = FStar_Syntax_Subst.compress t1
                             in
                          uu____18891.FStar_Syntax_Syntax.n  in
                        (match uu____18890 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____18926 -> failwith "Impossible")))
        | uu____18934 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____18958 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____18958 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____18971,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____18978 = find1 l2  in
            (match uu____18978 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____18985 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____18985 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____18989 = find1 l  in
            (match uu____18989 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____18994 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____18994
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19009 = lookup_qname env l1  in
      match uu____19009 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19012;
              FStar_Syntax_Syntax.sigrng = uu____19013;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19015;
              FStar_Syntax_Syntax.sigattrs = uu____19016;_},uu____19017),uu____19018)
          -> q
      | uu____19069 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19093 =
          let uu____19094 =
            let uu____19096 = FStar_Util.string_of_int i  in
            let uu____19098 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19096 uu____19098
             in
          failwith uu____19094  in
        let uu____19101 = lookup_datacon env lid  in
        match uu____19101 with
        | (uu____19106,t) ->
            let uu____19108 =
              let uu____19109 = FStar_Syntax_Subst.compress t  in
              uu____19109.FStar_Syntax_Syntax.n  in
            (match uu____19108 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19113) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19157 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19157
                      FStar_Pervasives_Native.fst)
             | uu____19168 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19182 = lookup_qname env l  in
      match uu____19182 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19184,uu____19185,uu____19186);
              FStar_Syntax_Syntax.sigrng = uu____19187;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19189;
              FStar_Syntax_Syntax.sigattrs = uu____19190;_},uu____19191),uu____19192)
          ->
          FStar_Util.for_some
            (fun uu___7_19245  ->
               match uu___7_19245 with
               | FStar_Syntax_Syntax.Projector uu____19247 -> true
               | uu____19253 -> false) quals
      | uu____19255 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19269 = lookup_qname env lid  in
      match uu____19269 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19271,uu____19272,uu____19273,uu____19274,uu____19275,uu____19276);
              FStar_Syntax_Syntax.sigrng = uu____19277;
              FStar_Syntax_Syntax.sigquals = uu____19278;
              FStar_Syntax_Syntax.sigmeta = uu____19279;
              FStar_Syntax_Syntax.sigattrs = uu____19280;_},uu____19281),uu____19282)
          -> true
      | uu____19340 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19354 = lookup_qname env lid  in
      match uu____19354 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19356,uu____19357,uu____19358,uu____19359,uu____19360,uu____19361);
              FStar_Syntax_Syntax.sigrng = uu____19362;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19364;
              FStar_Syntax_Syntax.sigattrs = uu____19365;_},uu____19366),uu____19367)
          ->
          FStar_Util.for_some
            (fun uu___8_19428  ->
               match uu___8_19428 with
               | FStar_Syntax_Syntax.RecordType uu____19430 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19440 -> true
               | uu____19450 -> false) quals
      | uu____19452 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19462,uu____19463);
            FStar_Syntax_Syntax.sigrng = uu____19464;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19466;
            FStar_Syntax_Syntax.sigattrs = uu____19467;_},uu____19468),uu____19469)
        ->
        FStar_Util.for_some
          (fun uu___9_19526  ->
             match uu___9_19526 with
             | FStar_Syntax_Syntax.Action uu____19528 -> true
             | uu____19530 -> false) quals
    | uu____19532 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19546 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____19546
  
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
      let uu____19563 =
        let uu____19564 = FStar_Syntax_Util.un_uinst head1  in
        uu____19564.FStar_Syntax_Syntax.n  in
      match uu____19563 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____19570 ->
               true
           | uu____19573 -> false)
      | uu____19575 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19589 = lookup_qname env l  in
      match uu____19589 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____19592),uu____19593) ->
          FStar_Util.for_some
            (fun uu___10_19641  ->
               match uu___10_19641 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____19644 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____19646 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____19722 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____19740) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____19758 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____19766 ->
                 FStar_Pervasives_Native.Some true
             | uu____19785 -> FStar_Pervasives_Native.Some false)
         in
      let uu____19788 =
        let uu____19792 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____19792 mapper  in
      match uu____19788 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____19852 = lookup_qname env lid  in
      match uu____19852 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19856,uu____19857,tps,uu____19859,uu____19860,uu____19861);
              FStar_Syntax_Syntax.sigrng = uu____19862;
              FStar_Syntax_Syntax.sigquals = uu____19863;
              FStar_Syntax_Syntax.sigmeta = uu____19864;
              FStar_Syntax_Syntax.sigattrs = uu____19865;_},uu____19866),uu____19867)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____19933 -> FStar_Pervasives_Native.None
  
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
           (fun uu____19979  ->
              match uu____19979 with
              | (d,uu____19988) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20004 = effect_decl_opt env l  in
      match uu____20004 with
      | FStar_Pervasives_Native.None  ->
          let uu____20019 = name_not_found l  in
          let uu____20025 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20019 uu____20025
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20048  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20067  ->
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
        let uu____20099 = FStar_Ident.lid_equals l1 l2  in
        if uu____20099
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20110 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20110
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20121 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20174  ->
                        match uu____20174 with
                        | (m1,m2,uu____20188,uu____20189,uu____20190) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20121 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20207 =
                    let uu____20213 =
                      let uu____20215 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20217 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20215
                        uu____20217
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20213)
                     in
                  FStar_Errors.raise_error uu____20207 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20227,uu____20228,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20262 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20262
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
  'Auu____20282 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20282) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20311 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20337  ->
                match uu____20337 with
                | (d,uu____20344) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20311 with
      | FStar_Pervasives_Native.None  ->
          let uu____20355 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20355
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20370 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____20370 with
           | (uu____20385,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20403)::(wp,uu____20405)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20461 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          let uu____20519 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____20519
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____20524 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____20524
             then
               FStar_Syntax_Syntax.mk_GTotal' res_t
                 (FStar_Pervasives_Native.Some res_u)
             else
               (let eff_name1 = norm_eff_name env eff_name  in
                let ed = get_effect_decl env eff_name1  in
                let null_wp =
                  inst_effect_fun_with [res_u] env ed
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let null_wp_res =
                  let uu____20535 = get_range env  in
                  let uu____20536 =
                    let uu____20543 =
                      let uu____20544 =
                        let uu____20561 =
                          let uu____20572 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____20572]  in
                        (null_wp, uu____20561)  in
                      FStar_Syntax_Syntax.Tm_app uu____20544  in
                    FStar_Syntax_Syntax.mk uu____20543  in
                  uu____20536 FStar_Pervasives_Native.None uu____20535  in
                let uu____20609 =
                  let uu____20610 =
                    let uu____20621 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____20621]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____20610;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____20609))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1498_20659 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1498_20659.order);
              joins = (uu___1498_20659.joins)
            }  in
          let uu___1501_20668 = env  in
          {
            solver = (uu___1501_20668.solver);
            range = (uu___1501_20668.range);
            curmodule = (uu___1501_20668.curmodule);
            gamma = (uu___1501_20668.gamma);
            gamma_sig = (uu___1501_20668.gamma_sig);
            gamma_cache = (uu___1501_20668.gamma_cache);
            modules = (uu___1501_20668.modules);
            expected_typ = (uu___1501_20668.expected_typ);
            sigtab = (uu___1501_20668.sigtab);
            attrtab = (uu___1501_20668.attrtab);
            is_pattern = (uu___1501_20668.is_pattern);
            instantiate_imp = (uu___1501_20668.instantiate_imp);
            effects;
            generalize = (uu___1501_20668.generalize);
            letrecs = (uu___1501_20668.letrecs);
            top_level = (uu___1501_20668.top_level);
            check_uvars = (uu___1501_20668.check_uvars);
            use_eq = (uu___1501_20668.use_eq);
            is_iface = (uu___1501_20668.is_iface);
            admit = (uu___1501_20668.admit);
            lax = (uu___1501_20668.lax);
            lax_universes = (uu___1501_20668.lax_universes);
            phase1 = (uu___1501_20668.phase1);
            failhard = (uu___1501_20668.failhard);
            nosynth = (uu___1501_20668.nosynth);
            uvar_subtyping = (uu___1501_20668.uvar_subtyping);
            tc_term = (uu___1501_20668.tc_term);
            type_of = (uu___1501_20668.type_of);
            universe_of = (uu___1501_20668.universe_of);
            check_type_of = (uu___1501_20668.check_type_of);
            use_bv_sorts = (uu___1501_20668.use_bv_sorts);
            qtbl_name_and_index = (uu___1501_20668.qtbl_name_and_index);
            normalized_eff_names = (uu___1501_20668.normalized_eff_names);
            fv_delta_depths = (uu___1501_20668.fv_delta_depths);
            proof_ns = (uu___1501_20668.proof_ns);
            synth_hook = (uu___1501_20668.synth_hook);
            splice = (uu___1501_20668.splice);
            postprocess = (uu___1501_20668.postprocess);
            is_native_tactic = (uu___1501_20668.is_native_tactic);
            identifier_info = (uu___1501_20668.identifier_info);
            tc_hooks = (uu___1501_20668.tc_hooks);
            dsenv = (uu___1501_20668.dsenv);
            nbe = (uu___1501_20668.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____20698 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____20698  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____20856 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____20857 = l1 u t wp e  in
                                l2 u t uu____20856 uu____20857))
                | uu____20858 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____20930 = inst_tscheme_with lift_t [u]  in
            match uu____20930 with
            | (uu____20937,lift_t1) ->
                let uu____20939 =
                  let uu____20946 =
                    let uu____20947 =
                      let uu____20964 =
                        let uu____20975 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____20984 =
                          let uu____20995 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____20995]  in
                        uu____20975 :: uu____20984  in
                      (lift_t1, uu____20964)  in
                    FStar_Syntax_Syntax.Tm_app uu____20947  in
                  FStar_Syntax_Syntax.mk uu____20946  in
                uu____20939 FStar_Pervasives_Native.None
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
            let uu____21105 = inst_tscheme_with lift_t [u]  in
            match uu____21105 with
            | (uu____21112,lift_t1) ->
                let uu____21114 =
                  let uu____21121 =
                    let uu____21122 =
                      let uu____21139 =
                        let uu____21150 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21159 =
                          let uu____21170 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21179 =
                            let uu____21190 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21190]  in
                          uu____21170 :: uu____21179  in
                        uu____21150 :: uu____21159  in
                      (lift_t1, uu____21139)  in
                    FStar_Syntax_Syntax.Tm_app uu____21122  in
                  FStar_Syntax_Syntax.mk uu____21121  in
                uu____21114 FStar_Pervasives_Native.None
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
              let uu____21292 =
                let uu____21293 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21293
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21292  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21302 =
              let uu____21304 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21304  in
            let uu____21305 =
              let uu____21307 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21335 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21335)
                 in
              FStar_Util.dflt "none" uu____21307  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21302
              uu____21305
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21364  ->
                    match uu____21364 with
                    | (e,uu____21372) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21395 =
            match uu____21395 with
            | (i,j) ->
                let uu____21406 = FStar_Ident.lid_equals i j  in
                if uu____21406
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _21413  -> FStar_Pervasives_Native.Some _21413)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____21442 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____21452 = FStar_Ident.lid_equals i k  in
                        if uu____21452
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____21466 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____21466
                                  then []
                                  else
                                    (let uu____21473 =
                                       let uu____21482 =
                                         find_edge order1 (i, k)  in
                                       let uu____21485 =
                                         find_edge order1 (k, j)  in
                                       (uu____21482, uu____21485)  in
                                     match uu____21473 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____21500 =
                                           compose_edges e1 e2  in
                                         [uu____21500]
                                     | uu____21501 -> [])))))
                 in
              FStar_List.append order1 uu____21442  in
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
                   let uu____21531 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____21534 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____21534
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____21531
                   then
                     let uu____21541 =
                       let uu____21547 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____21547)
                        in
                     let uu____21551 = get_range env  in
                     FStar_Errors.raise_error uu____21541 uu____21551
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____21629 = FStar_Ident.lid_equals i j
                                   in
                                if uu____21629
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____21681 =
                                              let uu____21690 =
                                                find_edge order2 (i, k)  in
                                              let uu____21693 =
                                                find_edge order2 (j, k)  in
                                              (uu____21690, uu____21693)  in
                                            match uu____21681 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____21735,uu____21736)
                                                     ->
                                                     let uu____21743 =
                                                       let uu____21750 =
                                                         let uu____21752 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21752
                                                          in
                                                       let uu____21755 =
                                                         let uu____21757 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21757
                                                          in
                                                       (uu____21750,
                                                         uu____21755)
                                                        in
                                                     (match uu____21743 with
                                                      | (true ,true ) ->
                                                          let uu____21774 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____21774
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
                                            | uu____21817 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1628_21890 = env.effects  in
              { decls = (uu___1628_21890.decls); order = order2; joins }  in
            let uu___1631_21891 = env  in
            {
              solver = (uu___1631_21891.solver);
              range = (uu___1631_21891.range);
              curmodule = (uu___1631_21891.curmodule);
              gamma = (uu___1631_21891.gamma);
              gamma_sig = (uu___1631_21891.gamma_sig);
              gamma_cache = (uu___1631_21891.gamma_cache);
              modules = (uu___1631_21891.modules);
              expected_typ = (uu___1631_21891.expected_typ);
              sigtab = (uu___1631_21891.sigtab);
              attrtab = (uu___1631_21891.attrtab);
              is_pattern = (uu___1631_21891.is_pattern);
              instantiate_imp = (uu___1631_21891.instantiate_imp);
              effects;
              generalize = (uu___1631_21891.generalize);
              letrecs = (uu___1631_21891.letrecs);
              top_level = (uu___1631_21891.top_level);
              check_uvars = (uu___1631_21891.check_uvars);
              use_eq = (uu___1631_21891.use_eq);
              is_iface = (uu___1631_21891.is_iface);
              admit = (uu___1631_21891.admit);
              lax = (uu___1631_21891.lax);
              lax_universes = (uu___1631_21891.lax_universes);
              phase1 = (uu___1631_21891.phase1);
              failhard = (uu___1631_21891.failhard);
              nosynth = (uu___1631_21891.nosynth);
              uvar_subtyping = (uu___1631_21891.uvar_subtyping);
              tc_term = (uu___1631_21891.tc_term);
              type_of = (uu___1631_21891.type_of);
              universe_of = (uu___1631_21891.universe_of);
              check_type_of = (uu___1631_21891.check_type_of);
              use_bv_sorts = (uu___1631_21891.use_bv_sorts);
              qtbl_name_and_index = (uu___1631_21891.qtbl_name_and_index);
              normalized_eff_names = (uu___1631_21891.normalized_eff_names);
              fv_delta_depths = (uu___1631_21891.fv_delta_depths);
              proof_ns = (uu___1631_21891.proof_ns);
              synth_hook = (uu___1631_21891.synth_hook);
              splice = (uu___1631_21891.splice);
              postprocess = (uu___1631_21891.postprocess);
              is_native_tactic = (uu___1631_21891.is_native_tactic);
              identifier_info = (uu___1631_21891.identifier_info);
              tc_hooks = (uu___1631_21891.tc_hooks);
              dsenv = (uu___1631_21891.dsenv);
              nbe = (uu___1631_21891.nbe)
            }))
      | uu____21892 -> env
  
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
        | uu____21921 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21934 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21934 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21951 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21951 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____21976 =
                     let uu____21982 =
                       let uu____21984 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____21992 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22003 =
                         let uu____22005 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22005  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21984 uu____21992 uu____22003
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21982)
                      in
                   FStar_Errors.raise_error uu____21976
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22013 =
                     let uu____22024 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22024 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22061  ->
                        fun uu____22062  ->
                          match (uu____22061, uu____22062) with
                          | ((x,uu____22092),(t,uu____22094)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22013
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22125 =
                     let uu___1669_22126 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1669_22126.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1669_22126.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1669_22126.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1669_22126.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22125
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22138 .
    'Auu____22138 ->
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
          let uu____22168 = effect_decl_opt env effect_name  in
          match uu____22168 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22207 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22230 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22269 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22269
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22274 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22274
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22289 =
                     let uu____22292 = get_range env  in
                     let uu____22293 =
                       let uu____22300 =
                         let uu____22301 =
                           let uu____22318 =
                             let uu____22329 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22329; wp]  in
                           (repr, uu____22318)  in
                         FStar_Syntax_Syntax.Tm_app uu____22301  in
                       FStar_Syntax_Syntax.mk uu____22300  in
                     uu____22293 FStar_Pervasives_Native.None uu____22292  in
                   FStar_Pervasives_Native.Some uu____22289)
  
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
      | uu____22473 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22488 =
        let uu____22489 = FStar_Syntax_Subst.compress t  in
        uu____22489.FStar_Syntax_Syntax.n  in
      match uu____22488 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22493,c) ->
          is_reifiable_comp env c
      | uu____22515 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22535 =
           let uu____22537 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22537  in
         if uu____22535
         then
           let uu____22540 =
             let uu____22546 =
               let uu____22548 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22548
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22546)  in
           let uu____22552 = get_range env  in
           FStar_Errors.raise_error uu____22540 uu____22552
         else ());
        (let uu____22555 = effect_repr_aux true env c u_c  in
         match uu____22555 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1734_22591 = env  in
        {
          solver = (uu___1734_22591.solver);
          range = (uu___1734_22591.range);
          curmodule = (uu___1734_22591.curmodule);
          gamma = (uu___1734_22591.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1734_22591.gamma_cache);
          modules = (uu___1734_22591.modules);
          expected_typ = (uu___1734_22591.expected_typ);
          sigtab = (uu___1734_22591.sigtab);
          attrtab = (uu___1734_22591.attrtab);
          is_pattern = (uu___1734_22591.is_pattern);
          instantiate_imp = (uu___1734_22591.instantiate_imp);
          effects = (uu___1734_22591.effects);
          generalize = (uu___1734_22591.generalize);
          letrecs = (uu___1734_22591.letrecs);
          top_level = (uu___1734_22591.top_level);
          check_uvars = (uu___1734_22591.check_uvars);
          use_eq = (uu___1734_22591.use_eq);
          is_iface = (uu___1734_22591.is_iface);
          admit = (uu___1734_22591.admit);
          lax = (uu___1734_22591.lax);
          lax_universes = (uu___1734_22591.lax_universes);
          phase1 = (uu___1734_22591.phase1);
          failhard = (uu___1734_22591.failhard);
          nosynth = (uu___1734_22591.nosynth);
          uvar_subtyping = (uu___1734_22591.uvar_subtyping);
          tc_term = (uu___1734_22591.tc_term);
          type_of = (uu___1734_22591.type_of);
          universe_of = (uu___1734_22591.universe_of);
          check_type_of = (uu___1734_22591.check_type_of);
          use_bv_sorts = (uu___1734_22591.use_bv_sorts);
          qtbl_name_and_index = (uu___1734_22591.qtbl_name_and_index);
          normalized_eff_names = (uu___1734_22591.normalized_eff_names);
          fv_delta_depths = (uu___1734_22591.fv_delta_depths);
          proof_ns = (uu___1734_22591.proof_ns);
          synth_hook = (uu___1734_22591.synth_hook);
          splice = (uu___1734_22591.splice);
          postprocess = (uu___1734_22591.postprocess);
          is_native_tactic = (uu___1734_22591.is_native_tactic);
          identifier_info = (uu___1734_22591.identifier_info);
          tc_hooks = (uu___1734_22591.tc_hooks);
          dsenv = (uu___1734_22591.dsenv);
          nbe = (uu___1734_22591.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1741_22605 = env  in
      {
        solver = (uu___1741_22605.solver);
        range = (uu___1741_22605.range);
        curmodule = (uu___1741_22605.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1741_22605.gamma_sig);
        gamma_cache = (uu___1741_22605.gamma_cache);
        modules = (uu___1741_22605.modules);
        expected_typ = (uu___1741_22605.expected_typ);
        sigtab = (uu___1741_22605.sigtab);
        attrtab = (uu___1741_22605.attrtab);
        is_pattern = (uu___1741_22605.is_pattern);
        instantiate_imp = (uu___1741_22605.instantiate_imp);
        effects = (uu___1741_22605.effects);
        generalize = (uu___1741_22605.generalize);
        letrecs = (uu___1741_22605.letrecs);
        top_level = (uu___1741_22605.top_level);
        check_uvars = (uu___1741_22605.check_uvars);
        use_eq = (uu___1741_22605.use_eq);
        is_iface = (uu___1741_22605.is_iface);
        admit = (uu___1741_22605.admit);
        lax = (uu___1741_22605.lax);
        lax_universes = (uu___1741_22605.lax_universes);
        phase1 = (uu___1741_22605.phase1);
        failhard = (uu___1741_22605.failhard);
        nosynth = (uu___1741_22605.nosynth);
        uvar_subtyping = (uu___1741_22605.uvar_subtyping);
        tc_term = (uu___1741_22605.tc_term);
        type_of = (uu___1741_22605.type_of);
        universe_of = (uu___1741_22605.universe_of);
        check_type_of = (uu___1741_22605.check_type_of);
        use_bv_sorts = (uu___1741_22605.use_bv_sorts);
        qtbl_name_and_index = (uu___1741_22605.qtbl_name_and_index);
        normalized_eff_names = (uu___1741_22605.normalized_eff_names);
        fv_delta_depths = (uu___1741_22605.fv_delta_depths);
        proof_ns = (uu___1741_22605.proof_ns);
        synth_hook = (uu___1741_22605.synth_hook);
        splice = (uu___1741_22605.splice);
        postprocess = (uu___1741_22605.postprocess);
        is_native_tactic = (uu___1741_22605.is_native_tactic);
        identifier_info = (uu___1741_22605.identifier_info);
        tc_hooks = (uu___1741_22605.tc_hooks);
        dsenv = (uu___1741_22605.dsenv);
        nbe = (uu___1741_22605.nbe)
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
            (let uu___1754_22663 = env  in
             {
               solver = (uu___1754_22663.solver);
               range = (uu___1754_22663.range);
               curmodule = (uu___1754_22663.curmodule);
               gamma = rest;
               gamma_sig = (uu___1754_22663.gamma_sig);
               gamma_cache = (uu___1754_22663.gamma_cache);
               modules = (uu___1754_22663.modules);
               expected_typ = (uu___1754_22663.expected_typ);
               sigtab = (uu___1754_22663.sigtab);
               attrtab = (uu___1754_22663.attrtab);
               is_pattern = (uu___1754_22663.is_pattern);
               instantiate_imp = (uu___1754_22663.instantiate_imp);
               effects = (uu___1754_22663.effects);
               generalize = (uu___1754_22663.generalize);
               letrecs = (uu___1754_22663.letrecs);
               top_level = (uu___1754_22663.top_level);
               check_uvars = (uu___1754_22663.check_uvars);
               use_eq = (uu___1754_22663.use_eq);
               is_iface = (uu___1754_22663.is_iface);
               admit = (uu___1754_22663.admit);
               lax = (uu___1754_22663.lax);
               lax_universes = (uu___1754_22663.lax_universes);
               phase1 = (uu___1754_22663.phase1);
               failhard = (uu___1754_22663.failhard);
               nosynth = (uu___1754_22663.nosynth);
               uvar_subtyping = (uu___1754_22663.uvar_subtyping);
               tc_term = (uu___1754_22663.tc_term);
               type_of = (uu___1754_22663.type_of);
               universe_of = (uu___1754_22663.universe_of);
               check_type_of = (uu___1754_22663.check_type_of);
               use_bv_sorts = (uu___1754_22663.use_bv_sorts);
               qtbl_name_and_index = (uu___1754_22663.qtbl_name_and_index);
               normalized_eff_names = (uu___1754_22663.normalized_eff_names);
               fv_delta_depths = (uu___1754_22663.fv_delta_depths);
               proof_ns = (uu___1754_22663.proof_ns);
               synth_hook = (uu___1754_22663.synth_hook);
               splice = (uu___1754_22663.splice);
               postprocess = (uu___1754_22663.postprocess);
               is_native_tactic = (uu___1754_22663.is_native_tactic);
               identifier_info = (uu___1754_22663.identifier_info);
               tc_hooks = (uu___1754_22663.tc_hooks);
               dsenv = (uu___1754_22663.dsenv);
               nbe = (uu___1754_22663.nbe)
             }))
    | uu____22664 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____22693  ->
             match uu____22693 with | (x,uu____22701) -> push_bv env1 x) env
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
            let uu___1768_22736 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1768_22736.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1768_22736.FStar_Syntax_Syntax.index);
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
      (let uu___1779_22778 = env  in
       {
         solver = (uu___1779_22778.solver);
         range = (uu___1779_22778.range);
         curmodule = (uu___1779_22778.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1779_22778.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1779_22778.sigtab);
         attrtab = (uu___1779_22778.attrtab);
         is_pattern = (uu___1779_22778.is_pattern);
         instantiate_imp = (uu___1779_22778.instantiate_imp);
         effects = (uu___1779_22778.effects);
         generalize = (uu___1779_22778.generalize);
         letrecs = (uu___1779_22778.letrecs);
         top_level = (uu___1779_22778.top_level);
         check_uvars = (uu___1779_22778.check_uvars);
         use_eq = (uu___1779_22778.use_eq);
         is_iface = (uu___1779_22778.is_iface);
         admit = (uu___1779_22778.admit);
         lax = (uu___1779_22778.lax);
         lax_universes = (uu___1779_22778.lax_universes);
         phase1 = (uu___1779_22778.phase1);
         failhard = (uu___1779_22778.failhard);
         nosynth = (uu___1779_22778.nosynth);
         uvar_subtyping = (uu___1779_22778.uvar_subtyping);
         tc_term = (uu___1779_22778.tc_term);
         type_of = (uu___1779_22778.type_of);
         universe_of = (uu___1779_22778.universe_of);
         check_type_of = (uu___1779_22778.check_type_of);
         use_bv_sorts = (uu___1779_22778.use_bv_sorts);
         qtbl_name_and_index = (uu___1779_22778.qtbl_name_and_index);
         normalized_eff_names = (uu___1779_22778.normalized_eff_names);
         fv_delta_depths = (uu___1779_22778.fv_delta_depths);
         proof_ns = (uu___1779_22778.proof_ns);
         synth_hook = (uu___1779_22778.synth_hook);
         splice = (uu___1779_22778.splice);
         postprocess = (uu___1779_22778.postprocess);
         is_native_tactic = (uu___1779_22778.is_native_tactic);
         identifier_info = (uu___1779_22778.identifier_info);
         tc_hooks = (uu___1779_22778.tc_hooks);
         dsenv = (uu___1779_22778.dsenv);
         nbe = (uu___1779_22778.nbe)
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
        let uu____22822 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____22822 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____22850 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____22850)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1794_22866 = env  in
      {
        solver = (uu___1794_22866.solver);
        range = (uu___1794_22866.range);
        curmodule = (uu___1794_22866.curmodule);
        gamma = (uu___1794_22866.gamma);
        gamma_sig = (uu___1794_22866.gamma_sig);
        gamma_cache = (uu___1794_22866.gamma_cache);
        modules = (uu___1794_22866.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1794_22866.sigtab);
        attrtab = (uu___1794_22866.attrtab);
        is_pattern = (uu___1794_22866.is_pattern);
        instantiate_imp = (uu___1794_22866.instantiate_imp);
        effects = (uu___1794_22866.effects);
        generalize = (uu___1794_22866.generalize);
        letrecs = (uu___1794_22866.letrecs);
        top_level = (uu___1794_22866.top_level);
        check_uvars = (uu___1794_22866.check_uvars);
        use_eq = false;
        is_iface = (uu___1794_22866.is_iface);
        admit = (uu___1794_22866.admit);
        lax = (uu___1794_22866.lax);
        lax_universes = (uu___1794_22866.lax_universes);
        phase1 = (uu___1794_22866.phase1);
        failhard = (uu___1794_22866.failhard);
        nosynth = (uu___1794_22866.nosynth);
        uvar_subtyping = (uu___1794_22866.uvar_subtyping);
        tc_term = (uu___1794_22866.tc_term);
        type_of = (uu___1794_22866.type_of);
        universe_of = (uu___1794_22866.universe_of);
        check_type_of = (uu___1794_22866.check_type_of);
        use_bv_sorts = (uu___1794_22866.use_bv_sorts);
        qtbl_name_and_index = (uu___1794_22866.qtbl_name_and_index);
        normalized_eff_names = (uu___1794_22866.normalized_eff_names);
        fv_delta_depths = (uu___1794_22866.fv_delta_depths);
        proof_ns = (uu___1794_22866.proof_ns);
        synth_hook = (uu___1794_22866.synth_hook);
        splice = (uu___1794_22866.splice);
        postprocess = (uu___1794_22866.postprocess);
        is_native_tactic = (uu___1794_22866.is_native_tactic);
        identifier_info = (uu___1794_22866.identifier_info);
        tc_hooks = (uu___1794_22866.tc_hooks);
        dsenv = (uu___1794_22866.dsenv);
        nbe = (uu___1794_22866.nbe)
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
    let uu____22897 = expected_typ env_  in
    ((let uu___1801_22903 = env_  in
      {
        solver = (uu___1801_22903.solver);
        range = (uu___1801_22903.range);
        curmodule = (uu___1801_22903.curmodule);
        gamma = (uu___1801_22903.gamma);
        gamma_sig = (uu___1801_22903.gamma_sig);
        gamma_cache = (uu___1801_22903.gamma_cache);
        modules = (uu___1801_22903.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1801_22903.sigtab);
        attrtab = (uu___1801_22903.attrtab);
        is_pattern = (uu___1801_22903.is_pattern);
        instantiate_imp = (uu___1801_22903.instantiate_imp);
        effects = (uu___1801_22903.effects);
        generalize = (uu___1801_22903.generalize);
        letrecs = (uu___1801_22903.letrecs);
        top_level = (uu___1801_22903.top_level);
        check_uvars = (uu___1801_22903.check_uvars);
        use_eq = false;
        is_iface = (uu___1801_22903.is_iface);
        admit = (uu___1801_22903.admit);
        lax = (uu___1801_22903.lax);
        lax_universes = (uu___1801_22903.lax_universes);
        phase1 = (uu___1801_22903.phase1);
        failhard = (uu___1801_22903.failhard);
        nosynth = (uu___1801_22903.nosynth);
        uvar_subtyping = (uu___1801_22903.uvar_subtyping);
        tc_term = (uu___1801_22903.tc_term);
        type_of = (uu___1801_22903.type_of);
        universe_of = (uu___1801_22903.universe_of);
        check_type_of = (uu___1801_22903.check_type_of);
        use_bv_sorts = (uu___1801_22903.use_bv_sorts);
        qtbl_name_and_index = (uu___1801_22903.qtbl_name_and_index);
        normalized_eff_names = (uu___1801_22903.normalized_eff_names);
        fv_delta_depths = (uu___1801_22903.fv_delta_depths);
        proof_ns = (uu___1801_22903.proof_ns);
        synth_hook = (uu___1801_22903.synth_hook);
        splice = (uu___1801_22903.splice);
        postprocess = (uu___1801_22903.postprocess);
        is_native_tactic = (uu___1801_22903.is_native_tactic);
        identifier_info = (uu___1801_22903.identifier_info);
        tc_hooks = (uu___1801_22903.tc_hooks);
        dsenv = (uu___1801_22903.dsenv);
        nbe = (uu___1801_22903.nbe)
      }), uu____22897)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____22915 =
      let uu____22918 = FStar_Ident.id_of_text ""  in [uu____22918]  in
    FStar_Ident.lid_of_ids uu____22915  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____22925 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____22925
        then
          let uu____22930 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____22930 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1809_22958 = env  in
       {
         solver = (uu___1809_22958.solver);
         range = (uu___1809_22958.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1809_22958.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1809_22958.expected_typ);
         sigtab = (uu___1809_22958.sigtab);
         attrtab = (uu___1809_22958.attrtab);
         is_pattern = (uu___1809_22958.is_pattern);
         instantiate_imp = (uu___1809_22958.instantiate_imp);
         effects = (uu___1809_22958.effects);
         generalize = (uu___1809_22958.generalize);
         letrecs = (uu___1809_22958.letrecs);
         top_level = (uu___1809_22958.top_level);
         check_uvars = (uu___1809_22958.check_uvars);
         use_eq = (uu___1809_22958.use_eq);
         is_iface = (uu___1809_22958.is_iface);
         admit = (uu___1809_22958.admit);
         lax = (uu___1809_22958.lax);
         lax_universes = (uu___1809_22958.lax_universes);
         phase1 = (uu___1809_22958.phase1);
         failhard = (uu___1809_22958.failhard);
         nosynth = (uu___1809_22958.nosynth);
         uvar_subtyping = (uu___1809_22958.uvar_subtyping);
         tc_term = (uu___1809_22958.tc_term);
         type_of = (uu___1809_22958.type_of);
         universe_of = (uu___1809_22958.universe_of);
         check_type_of = (uu___1809_22958.check_type_of);
         use_bv_sorts = (uu___1809_22958.use_bv_sorts);
         qtbl_name_and_index = (uu___1809_22958.qtbl_name_and_index);
         normalized_eff_names = (uu___1809_22958.normalized_eff_names);
         fv_delta_depths = (uu___1809_22958.fv_delta_depths);
         proof_ns = (uu___1809_22958.proof_ns);
         synth_hook = (uu___1809_22958.synth_hook);
         splice = (uu___1809_22958.splice);
         postprocess = (uu___1809_22958.postprocess);
         is_native_tactic = (uu___1809_22958.is_native_tactic);
         identifier_info = (uu___1809_22958.identifier_info);
         tc_hooks = (uu___1809_22958.tc_hooks);
         dsenv = (uu___1809_22958.dsenv);
         nbe = (uu___1809_22958.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23010)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23014,(uu____23015,t)))::tl1
          ->
          let uu____23036 =
            let uu____23039 = FStar_Syntax_Free.uvars t  in
            ext out uu____23039  in
          aux uu____23036 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23042;
            FStar_Syntax_Syntax.index = uu____23043;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23051 =
            let uu____23054 = FStar_Syntax_Free.uvars t  in
            ext out uu____23054  in
          aux uu____23051 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23112)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23116,(uu____23117,t)))::tl1
          ->
          let uu____23138 =
            let uu____23141 = FStar_Syntax_Free.univs t  in
            ext out uu____23141  in
          aux uu____23138 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23144;
            FStar_Syntax_Syntax.index = uu____23145;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23153 =
            let uu____23156 = FStar_Syntax_Free.univs t  in
            ext out uu____23156  in
          aux uu____23153 tl1
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
          let uu____23218 = FStar_Util.set_add uname out  in
          aux uu____23218 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23221,(uu____23222,t)))::tl1
          ->
          let uu____23243 =
            let uu____23246 = FStar_Syntax_Free.univnames t  in
            ext out uu____23246  in
          aux uu____23243 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23249;
            FStar_Syntax_Syntax.index = uu____23250;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23258 =
            let uu____23261 = FStar_Syntax_Free.univnames t  in
            ext out uu____23261  in
          aux uu____23258 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_23282  ->
            match uu___11_23282 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23286 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23299 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23310 =
      let uu____23319 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23319
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23310 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23367 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_23380  ->
              match uu___12_23380 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23383 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____23383
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23389) ->
                  let uu____23406 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____23406))
       in
    FStar_All.pipe_right uu____23367 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_23420  ->
    match uu___13_23420 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23426 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____23426
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23449  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23504) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____23537,uu____23538) -> false  in
      let uu____23552 =
        FStar_List.tryFind
          (fun uu____23574  ->
             match uu____23574 with | (p,uu____23585) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____23552 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23604,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23634 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23634
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1952_23656 = e  in
        {
          solver = (uu___1952_23656.solver);
          range = (uu___1952_23656.range);
          curmodule = (uu___1952_23656.curmodule);
          gamma = (uu___1952_23656.gamma);
          gamma_sig = (uu___1952_23656.gamma_sig);
          gamma_cache = (uu___1952_23656.gamma_cache);
          modules = (uu___1952_23656.modules);
          expected_typ = (uu___1952_23656.expected_typ);
          sigtab = (uu___1952_23656.sigtab);
          attrtab = (uu___1952_23656.attrtab);
          is_pattern = (uu___1952_23656.is_pattern);
          instantiate_imp = (uu___1952_23656.instantiate_imp);
          effects = (uu___1952_23656.effects);
          generalize = (uu___1952_23656.generalize);
          letrecs = (uu___1952_23656.letrecs);
          top_level = (uu___1952_23656.top_level);
          check_uvars = (uu___1952_23656.check_uvars);
          use_eq = (uu___1952_23656.use_eq);
          is_iface = (uu___1952_23656.is_iface);
          admit = (uu___1952_23656.admit);
          lax = (uu___1952_23656.lax);
          lax_universes = (uu___1952_23656.lax_universes);
          phase1 = (uu___1952_23656.phase1);
          failhard = (uu___1952_23656.failhard);
          nosynth = (uu___1952_23656.nosynth);
          uvar_subtyping = (uu___1952_23656.uvar_subtyping);
          tc_term = (uu___1952_23656.tc_term);
          type_of = (uu___1952_23656.type_of);
          universe_of = (uu___1952_23656.universe_of);
          check_type_of = (uu___1952_23656.check_type_of);
          use_bv_sorts = (uu___1952_23656.use_bv_sorts);
          qtbl_name_and_index = (uu___1952_23656.qtbl_name_and_index);
          normalized_eff_names = (uu___1952_23656.normalized_eff_names);
          fv_delta_depths = (uu___1952_23656.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1952_23656.synth_hook);
          splice = (uu___1952_23656.splice);
          postprocess = (uu___1952_23656.postprocess);
          is_native_tactic = (uu___1952_23656.is_native_tactic);
          identifier_info = (uu___1952_23656.identifier_info);
          tc_hooks = (uu___1952_23656.tc_hooks);
          dsenv = (uu___1952_23656.dsenv);
          nbe = (uu___1952_23656.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1961_23704 = e  in
      {
        solver = (uu___1961_23704.solver);
        range = (uu___1961_23704.range);
        curmodule = (uu___1961_23704.curmodule);
        gamma = (uu___1961_23704.gamma);
        gamma_sig = (uu___1961_23704.gamma_sig);
        gamma_cache = (uu___1961_23704.gamma_cache);
        modules = (uu___1961_23704.modules);
        expected_typ = (uu___1961_23704.expected_typ);
        sigtab = (uu___1961_23704.sigtab);
        attrtab = (uu___1961_23704.attrtab);
        is_pattern = (uu___1961_23704.is_pattern);
        instantiate_imp = (uu___1961_23704.instantiate_imp);
        effects = (uu___1961_23704.effects);
        generalize = (uu___1961_23704.generalize);
        letrecs = (uu___1961_23704.letrecs);
        top_level = (uu___1961_23704.top_level);
        check_uvars = (uu___1961_23704.check_uvars);
        use_eq = (uu___1961_23704.use_eq);
        is_iface = (uu___1961_23704.is_iface);
        admit = (uu___1961_23704.admit);
        lax = (uu___1961_23704.lax);
        lax_universes = (uu___1961_23704.lax_universes);
        phase1 = (uu___1961_23704.phase1);
        failhard = (uu___1961_23704.failhard);
        nosynth = (uu___1961_23704.nosynth);
        uvar_subtyping = (uu___1961_23704.uvar_subtyping);
        tc_term = (uu___1961_23704.tc_term);
        type_of = (uu___1961_23704.type_of);
        universe_of = (uu___1961_23704.universe_of);
        check_type_of = (uu___1961_23704.check_type_of);
        use_bv_sorts = (uu___1961_23704.use_bv_sorts);
        qtbl_name_and_index = (uu___1961_23704.qtbl_name_and_index);
        normalized_eff_names = (uu___1961_23704.normalized_eff_names);
        fv_delta_depths = (uu___1961_23704.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1961_23704.synth_hook);
        splice = (uu___1961_23704.splice);
        postprocess = (uu___1961_23704.postprocess);
        is_native_tactic = (uu___1961_23704.is_native_tactic);
        identifier_info = (uu___1961_23704.identifier_info);
        tc_hooks = (uu___1961_23704.tc_hooks);
        dsenv = (uu___1961_23704.dsenv);
        nbe = (uu___1961_23704.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____23720 = FStar_Syntax_Free.names t  in
      let uu____23723 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____23720 uu____23723
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____23746 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____23746
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____23756 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____23756
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____23777 =
      match uu____23777 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____23797 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____23797)
       in
    let uu____23805 =
      let uu____23809 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____23809 FStar_List.rev  in
    FStar_All.pipe_right uu____23805 (FStar_String.concat " ")
  
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
                  (let uu____23879 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____23879 with
                   | FStar_Pervasives_Native.Some uu____23883 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____23886 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____23896;
        univ_ineqs = uu____23897; implicits = uu____23898;_} -> true
    | uu____23910 -> false
  
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
          let uu___2005_23941 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2005_23941.deferred);
            univ_ineqs = (uu___2005_23941.univ_ineqs);
            implicits = (uu___2005_23941.implicits)
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
          let uu____23980 = FStar_Options.defensive ()  in
          if uu____23980
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____23986 =
              let uu____23988 =
                let uu____23990 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____23990  in
              Prims.op_Negation uu____23988  in
            (if uu____23986
             then
               let uu____23997 =
                 let uu____24003 =
                   let uu____24005 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24007 =
                     let uu____24009 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24009
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24005 uu____24007
                    in
                 (FStar_Errors.Warning_Defensive, uu____24003)  in
               FStar_Errors.log_issue rng uu____23997
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
          let uu____24049 =
            let uu____24051 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24051  in
          if uu____24049
          then ()
          else
            (let uu____24056 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24056 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24082 =
            let uu____24084 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24084  in
          if uu____24082
          then ()
          else
            (let uu____24089 = bound_vars e  in
             def_check_closed_in rng msg uu____24089 t)
  
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
          let uu___2042_24128 = g  in
          let uu____24129 =
            let uu____24130 =
              let uu____24131 =
                let uu____24138 =
                  let uu____24139 =
                    let uu____24156 =
                      let uu____24167 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24167]  in
                    (f, uu____24156)  in
                  FStar_Syntax_Syntax.Tm_app uu____24139  in
                FStar_Syntax_Syntax.mk uu____24138  in
              uu____24131 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24204  -> FStar_TypeChecker_Common.NonTrivial _24204)
              uu____24130
             in
          {
            guard_f = uu____24129;
            deferred = (uu___2042_24128.deferred);
            univ_ineqs = (uu___2042_24128.univ_ineqs);
            implicits = (uu___2042_24128.implicits)
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
          let uu___2049_24222 = g  in
          let uu____24223 =
            let uu____24224 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24224  in
          {
            guard_f = uu____24223;
            deferred = (uu___2049_24222.deferred);
            univ_ineqs = (uu___2049_24222.univ_ineqs);
            implicits = (uu___2049_24222.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2054_24241 = g  in
          let uu____24242 =
            let uu____24243 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24243  in
          {
            guard_f = uu____24242;
            deferred = (uu___2054_24241.deferred);
            univ_ineqs = (uu___2054_24241.univ_ineqs);
            implicits = (uu___2054_24241.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2058_24245 = g  in
          let uu____24246 =
            let uu____24247 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24247  in
          {
            guard_f = uu____24246;
            deferred = (uu___2058_24245.deferred);
            univ_ineqs = (uu___2058_24245.univ_ineqs);
            implicits = (uu___2058_24245.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24254 ->
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
          let uu____24271 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24271
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24278 =
      let uu____24279 = FStar_Syntax_Util.unmeta t  in
      uu____24279.FStar_Syntax_Syntax.n  in
    match uu____24278 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24283 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24326 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24326;
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
                       let uu____24421 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24421
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2113_24428 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2113_24428.deferred);
              univ_ineqs = (uu___2113_24428.univ_ineqs);
              implicits = (uu___2113_24428.implicits)
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
               let uu____24462 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24462
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
            let uu___2128_24489 = g  in
            let uu____24490 =
              let uu____24491 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24491  in
            {
              guard_f = uu____24490;
              deferred = (uu___2128_24489.deferred);
              univ_ineqs = (uu___2128_24489.univ_ineqs);
              implicits = (uu___2128_24489.implicits)
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
              let uu____24549 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____24549 with
              | FStar_Pervasives_Native.Some
                  (uu____24574::(tm,uu____24576)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____24640 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____24658 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____24658;
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
                      let uu___2150_24690 = trivial_guard  in
                      {
                        guard_f = (uu___2150_24690.guard_f);
                        deferred = (uu___2150_24690.deferred);
                        univ_ineqs = (uu___2150_24690.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____24708  -> ());
    push = (fun uu____24710  -> ());
    pop = (fun uu____24713  -> ());
    snapshot =
      (fun uu____24716  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____24735  -> fun uu____24736  -> ());
    encode_sig = (fun uu____24751  -> fun uu____24752  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____24758 =
             let uu____24765 = FStar_Options.peek ()  in (e, g, uu____24765)
              in
           [uu____24758]);
    solve = (fun uu____24781  -> fun uu____24782  -> fun uu____24783  -> ());
    finish = (fun uu____24790  -> ());
    refresh = (fun uu____24792  -> ())
  } 