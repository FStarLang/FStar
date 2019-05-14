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
  fun projectee  -> match projectee with | Beta  -> true | uu____127 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____138 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____149 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____161 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____179 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____190 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____201 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding _0 -> true | uu____214 -> false
  
let (__proj__Eager_unfolding__item___0 : step -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding _0 -> _0 
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____235 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____246 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____258 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____283 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____326 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____369 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____405 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____416 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____427 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____438 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____449 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____460 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____471 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____482 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____493 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____504 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____515 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____526 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____537 -> false
  
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
      | uu____674 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only of Prims.bool 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____715 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____726 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only _0 -> true
    | uu____739 -> false
  
let (__proj__Eager_unfolding_only__item___0 : delta_level -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding_only _0 -> _0 
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____761 -> false
  
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
           (fun uu___0_49267  ->
              match uu___0_49267 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____49283 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____49283  in
                  let uu____49292 =
                    let uu____49293 = FStar_Syntax_Subst.compress y  in
                    uu____49293.FStar_Syntax_Syntax.n  in
                  (match uu____49292 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____49310 =
                         let uu___339_49321 = y1  in
                         let uu____49332 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___339_49321.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___339_49321.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____49332
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____49310
                   | uu____49343 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___345_49519 = env  in
      let uu____49628 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___345_49519.solver);
        range = (uu___345_49519.range);
        curmodule = (uu___345_49519.curmodule);
        gamma = uu____49628;
        gamma_sig = (uu___345_49519.gamma_sig);
        gamma_cache = (uu___345_49519.gamma_cache);
        modules = (uu___345_49519.modules);
        expected_typ = (uu___345_49519.expected_typ);
        sigtab = (uu___345_49519.sigtab);
        attrtab = (uu___345_49519.attrtab);
        is_pattern = (uu___345_49519.is_pattern);
        instantiate_imp = (uu___345_49519.instantiate_imp);
        effects = (uu___345_49519.effects);
        generalize = (uu___345_49519.generalize);
        letrecs = (uu___345_49519.letrecs);
        top_level = (uu___345_49519.top_level);
        check_uvars = (uu___345_49519.check_uvars);
        use_eq = (uu___345_49519.use_eq);
        is_iface = (uu___345_49519.is_iface);
        admit = (uu___345_49519.admit);
        lax = (uu___345_49519.lax);
        lax_universes = (uu___345_49519.lax_universes);
        phase1 = (uu___345_49519.phase1);
        failhard = (uu___345_49519.failhard);
        nosynth = (uu___345_49519.nosynth);
        uvar_subtyping = (uu___345_49519.uvar_subtyping);
        tc_term = (uu___345_49519.tc_term);
        type_of = (uu___345_49519.type_of);
        universe_of = (uu___345_49519.universe_of);
        check_type_of = (uu___345_49519.check_type_of);
        use_bv_sorts = (uu___345_49519.use_bv_sorts);
        qtbl_name_and_index = (uu___345_49519.qtbl_name_and_index);
        normalized_eff_names = (uu___345_49519.normalized_eff_names);
        fv_delta_depths = (uu___345_49519.fv_delta_depths);
        proof_ns = (uu___345_49519.proof_ns);
        synth_hook = (uu___345_49519.synth_hook);
        splice = (uu___345_49519.splice);
        postprocess = (uu___345_49519.postprocess);
        is_native_tactic = (uu___345_49519.is_native_tactic);
        identifier_info = (uu___345_49519.identifier_info);
        tc_hooks = (uu___345_49519.tc_hooks);
        dsenv = (uu___345_49519.dsenv);
        nbe = (uu___345_49519.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____49642  -> fun uu____49643  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___352_49998 = env  in
      {
        solver = (uu___352_49998.solver);
        range = (uu___352_49998.range);
        curmodule = (uu___352_49998.curmodule);
        gamma = (uu___352_49998.gamma);
        gamma_sig = (uu___352_49998.gamma_sig);
        gamma_cache = (uu___352_49998.gamma_cache);
        modules = (uu___352_49998.modules);
        expected_typ = (uu___352_49998.expected_typ);
        sigtab = (uu___352_49998.sigtab);
        attrtab = (uu___352_49998.attrtab);
        is_pattern = (uu___352_49998.is_pattern);
        instantiate_imp = (uu___352_49998.instantiate_imp);
        effects = (uu___352_49998.effects);
        generalize = (uu___352_49998.generalize);
        letrecs = (uu___352_49998.letrecs);
        top_level = (uu___352_49998.top_level);
        check_uvars = (uu___352_49998.check_uvars);
        use_eq = (uu___352_49998.use_eq);
        is_iface = (uu___352_49998.is_iface);
        admit = (uu___352_49998.admit);
        lax = (uu___352_49998.lax);
        lax_universes = (uu___352_49998.lax_universes);
        phase1 = (uu___352_49998.phase1);
        failhard = (uu___352_49998.failhard);
        nosynth = (uu___352_49998.nosynth);
        uvar_subtyping = (uu___352_49998.uvar_subtyping);
        tc_term = (uu___352_49998.tc_term);
        type_of = (uu___352_49998.type_of);
        universe_of = (uu___352_49998.universe_of);
        check_type_of = (uu___352_49998.check_type_of);
        use_bv_sorts = (uu___352_49998.use_bv_sorts);
        qtbl_name_and_index = (uu___352_49998.qtbl_name_and_index);
        normalized_eff_names = (uu___352_49998.normalized_eff_names);
        fv_delta_depths = (uu___352_49998.fv_delta_depths);
        proof_ns = (uu___352_49998.proof_ns);
        synth_hook = (uu___352_49998.synth_hook);
        splice = (uu___352_49998.splice);
        postprocess = (uu___352_49998.postprocess);
        is_native_tactic = (uu___352_49998.is_native_tactic);
        identifier_info = (uu___352_49998.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___352_49998.dsenv);
        nbe = (uu___352_49998.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___356_50280 = e  in
      let uu____50389 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___356_50280.solver);
        range = (uu___356_50280.range);
        curmodule = (uu___356_50280.curmodule);
        gamma = (uu___356_50280.gamma);
        gamma_sig = (uu___356_50280.gamma_sig);
        gamma_cache = (uu___356_50280.gamma_cache);
        modules = (uu___356_50280.modules);
        expected_typ = (uu___356_50280.expected_typ);
        sigtab = (uu___356_50280.sigtab);
        attrtab = (uu___356_50280.attrtab);
        is_pattern = (uu___356_50280.is_pattern);
        instantiate_imp = (uu___356_50280.instantiate_imp);
        effects = (uu___356_50280.effects);
        generalize = (uu___356_50280.generalize);
        letrecs = (uu___356_50280.letrecs);
        top_level = (uu___356_50280.top_level);
        check_uvars = (uu___356_50280.check_uvars);
        use_eq = (uu___356_50280.use_eq);
        is_iface = (uu___356_50280.is_iface);
        admit = (uu___356_50280.admit);
        lax = (uu___356_50280.lax);
        lax_universes = (uu___356_50280.lax_universes);
        phase1 = (uu___356_50280.phase1);
        failhard = (uu___356_50280.failhard);
        nosynth = (uu___356_50280.nosynth);
        uvar_subtyping = (uu___356_50280.uvar_subtyping);
        tc_term = (uu___356_50280.tc_term);
        type_of = (uu___356_50280.type_of);
        universe_of = (uu___356_50280.universe_of);
        check_type_of = (uu___356_50280.check_type_of);
        use_bv_sorts = (uu___356_50280.use_bv_sorts);
        qtbl_name_and_index = (uu___356_50280.qtbl_name_and_index);
        normalized_eff_names = (uu___356_50280.normalized_eff_names);
        fv_delta_depths = (uu___356_50280.fv_delta_depths);
        proof_ns = (uu___356_50280.proof_ns);
        synth_hook = (uu___356_50280.synth_hook);
        splice = (uu___356_50280.splice);
        postprocess = (uu___356_50280.postprocess);
        is_native_tactic = (uu___356_50280.is_native_tactic);
        identifier_info = (uu___356_50280.identifier_info);
        tc_hooks = (uu___356_50280.tc_hooks);
        dsenv = uu____50389;
        nbe = (uu___356_50280.nbe)
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
      | (NoDelta ,uu____50693) -> true
      | (Eager_unfolding_only
         uu____50695,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold
         uu____50698,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____50700,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____50703 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____50717 . unit -> 'Auu____50717 FStar_Util.smap =
  fun uu____50724  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____50730 . unit -> 'Auu____50730 FStar_Util.smap =
  fun uu____50737  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____51619 = new_gamma_cache ()  in
                  let uu____51622 = new_sigtab ()  in
                  let uu____51635 = new_sigtab ()  in
                  let uu____51652 =
                    let uu____51671 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____51671, FStar_Pervasives_Native.None)  in
                  let uu____51700 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____51712 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____51716 = FStar_Options.using_facts_from ()  in
                  let uu____51717 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____51726 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____51619;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____51622;
                    attrtab = uu____51635;
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
                    qtbl_name_and_index = uu____51652;
                    normalized_eff_names = uu____51700;
                    fv_delta_depths = uu____51712;
                    proof_ns = uu____51716;
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
                    is_native_tactic = (fun uu____52052  -> false);
                    identifier_info = uu____51717;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____51726;
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
  fun uu____52597  ->
    let uu____52598 = FStar_ST.op_Bang query_indices  in
    match uu____52598 with
    | [] -> failwith "Empty query indices!"
    | uu____52669 ->
        let uu____52683 =
          let uu____52697 =
            let uu____52709 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____52709  in
          let uu____52779 = FStar_ST.op_Bang query_indices  in uu____52697 ::
            uu____52779
           in
        FStar_ST.op_Colon_Equals query_indices uu____52683
  
let (pop_query_indices : unit -> unit) =
  fun uu____52899  ->
    let uu____52900 = FStar_ST.op_Bang query_indices  in
    match uu____52900 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____53063  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____53112  ->
    match uu____53112 with
    | (l,n1) ->
        let uu____53134 = FStar_ST.op_Bang query_indices  in
        (match uu____53134 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____53300 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____53331  ->
    let uu____53332 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____53332
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____53740 =
       let uu____53797 = FStar_ST.op_Bang stack  in env :: uu____53797  in
     FStar_ST.op_Colon_Equals stack uu____53740);
    (let uu___425_54170 = env  in
     let uu____54279 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____54282 = FStar_Util.smap_copy (sigtab env)  in
     let uu____54295 = FStar_Util.smap_copy (attrtab env)  in
     let uu____54312 =
       let uu____54331 =
         let uu____54335 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____54335  in
       let uu____54375 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____54331, uu____54375)  in
     let uu____54444 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____54455 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____54458 =
       let uu____54464 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____54464  in
     {
       solver = (uu___425_54170.solver);
       range = (uu___425_54170.range);
       curmodule = (uu___425_54170.curmodule);
       gamma = (uu___425_54170.gamma);
       gamma_sig = (uu___425_54170.gamma_sig);
       gamma_cache = uu____54279;
       modules = (uu___425_54170.modules);
       expected_typ = (uu___425_54170.expected_typ);
       sigtab = uu____54282;
       attrtab = uu____54295;
       is_pattern = (uu___425_54170.is_pattern);
       instantiate_imp = (uu___425_54170.instantiate_imp);
       effects = (uu___425_54170.effects);
       generalize = (uu___425_54170.generalize);
       letrecs = (uu___425_54170.letrecs);
       top_level = (uu___425_54170.top_level);
       check_uvars = (uu___425_54170.check_uvars);
       use_eq = (uu___425_54170.use_eq);
       is_iface = (uu___425_54170.is_iface);
       admit = (uu___425_54170.admit);
       lax = (uu___425_54170.lax);
       lax_universes = (uu___425_54170.lax_universes);
       phase1 = (uu___425_54170.phase1);
       failhard = (uu___425_54170.failhard);
       nosynth = (uu___425_54170.nosynth);
       uvar_subtyping = (uu___425_54170.uvar_subtyping);
       tc_term = (uu___425_54170.tc_term);
       type_of = (uu___425_54170.type_of);
       universe_of = (uu___425_54170.universe_of);
       check_type_of = (uu___425_54170.check_type_of);
       use_bv_sorts = (uu___425_54170.use_bv_sorts);
       qtbl_name_and_index = uu____54312;
       normalized_eff_names = uu____54444;
       fv_delta_depths = uu____54455;
       proof_ns = (uu___425_54170.proof_ns);
       synth_hook = (uu___425_54170.synth_hook);
       splice = (uu___425_54170.splice);
       postprocess = (uu___425_54170.postprocess);
       is_native_tactic = (uu___425_54170.is_native_tactic);
       identifier_info = uu____54458;
       tc_hooks = (uu___425_54170.tc_hooks);
       dsenv = (uu___425_54170.dsenv);
       nbe = (uu___425_54170.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____54558  ->
    let uu____54559 = FStar_ST.op_Bang stack  in
    match uu____54559 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____55099 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____55999  ->
           let uu____56000 = snapshot_stack env  in
           match uu____56000 with
           | (stack_depth,env1) ->
               let uu____56250 = snapshot_query_indices ()  in
               (match uu____56250 with
                | (query_indices_depth,()) ->
                    let uu____56337 = (env1.solver).snapshot msg  in
                    (match uu____56337 with
                     | (solver_depth,()) ->
                         let uu____56448 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____56448 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___450_56623 = env1  in
                                 {
                                   solver = (uu___450_56623.solver);
                                   range = (uu___450_56623.range);
                                   curmodule = (uu___450_56623.curmodule);
                                   gamma = (uu___450_56623.gamma);
                                   gamma_sig = (uu___450_56623.gamma_sig);
                                   gamma_cache = (uu___450_56623.gamma_cache);
                                   modules = (uu___450_56623.modules);
                                   expected_typ =
                                     (uu___450_56623.expected_typ);
                                   sigtab = (uu___450_56623.sigtab);
                                   attrtab = (uu___450_56623.attrtab);
                                   is_pattern = (uu___450_56623.is_pattern);
                                   instantiate_imp =
                                     (uu___450_56623.instantiate_imp);
                                   effects = (uu___450_56623.effects);
                                   generalize = (uu___450_56623.generalize);
                                   letrecs = (uu___450_56623.letrecs);
                                   top_level = (uu___450_56623.top_level);
                                   check_uvars = (uu___450_56623.check_uvars);
                                   use_eq = (uu___450_56623.use_eq);
                                   is_iface = (uu___450_56623.is_iface);
                                   admit = (uu___450_56623.admit);
                                   lax = (uu___450_56623.lax);
                                   lax_universes =
                                     (uu___450_56623.lax_universes);
                                   phase1 = (uu___450_56623.phase1);
                                   failhard = (uu___450_56623.failhard);
                                   nosynth = (uu___450_56623.nosynth);
                                   uvar_subtyping =
                                     (uu___450_56623.uvar_subtyping);
                                   tc_term = (uu___450_56623.tc_term);
                                   type_of = (uu___450_56623.type_of);
                                   universe_of = (uu___450_56623.universe_of);
                                   check_type_of =
                                     (uu___450_56623.check_type_of);
                                   use_bv_sorts =
                                     (uu___450_56623.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___450_56623.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___450_56623.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___450_56623.fv_delta_depths);
                                   proof_ns = (uu___450_56623.proof_ns);
                                   synth_hook = (uu___450_56623.synth_hook);
                                   splice = (uu___450_56623.splice);
                                   postprocess = (uu___450_56623.postprocess);
                                   is_native_tactic =
                                     (uu___450_56623.is_native_tactic);
                                   identifier_info =
                                     (uu___450_56623.identifier_info);
                                   tc_hooks = (uu___450_56623.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___450_56623.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____56895  ->
             let uu____56896 =
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
             match uu____56896 with
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
                             ((let uu____57346 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____57346
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____57524 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____57524
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____58046,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____58112 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____58158  ->
                  match uu____58158 with
                  | (m,uu____58170) -> FStar_Ident.lid_equals l m))
           in
        (match uu____58112 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___495_58255 = env  in
               {
                 solver = (uu___495_58255.solver);
                 range = (uu___495_58255.range);
                 curmodule = (uu___495_58255.curmodule);
                 gamma = (uu___495_58255.gamma);
                 gamma_sig = (uu___495_58255.gamma_sig);
                 gamma_cache = (uu___495_58255.gamma_cache);
                 modules = (uu___495_58255.modules);
                 expected_typ = (uu___495_58255.expected_typ);
                 sigtab = (uu___495_58255.sigtab);
                 attrtab = (uu___495_58255.attrtab);
                 is_pattern = (uu___495_58255.is_pattern);
                 instantiate_imp = (uu___495_58255.instantiate_imp);
                 effects = (uu___495_58255.effects);
                 generalize = (uu___495_58255.generalize);
                 letrecs = (uu___495_58255.letrecs);
                 top_level = (uu___495_58255.top_level);
                 check_uvars = (uu___495_58255.check_uvars);
                 use_eq = (uu___495_58255.use_eq);
                 is_iface = (uu___495_58255.is_iface);
                 admit = (uu___495_58255.admit);
                 lax = (uu___495_58255.lax);
                 lax_universes = (uu___495_58255.lax_universes);
                 phase1 = (uu___495_58255.phase1);
                 failhard = (uu___495_58255.failhard);
                 nosynth = (uu___495_58255.nosynth);
                 uvar_subtyping = (uu___495_58255.uvar_subtyping);
                 tc_term = (uu___495_58255.tc_term);
                 type_of = (uu___495_58255.type_of);
                 universe_of = (uu___495_58255.universe_of);
                 check_type_of = (uu___495_58255.check_type_of);
                 use_bv_sorts = (uu___495_58255.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___495_58255.normalized_eff_names);
                 fv_delta_depths = (uu___495_58255.fv_delta_depths);
                 proof_ns = (uu___495_58255.proof_ns);
                 synth_hook = (uu___495_58255.synth_hook);
                 splice = (uu___495_58255.splice);
                 postprocess = (uu___495_58255.postprocess);
                 is_native_tactic = (uu___495_58255.is_native_tactic);
                 identifier_info = (uu___495_58255.identifier_info);
                 tc_hooks = (uu___495_58255.tc_hooks);
                 dsenv = (uu___495_58255.dsenv);
                 nbe = (uu___495_58255.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____58392,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___504_58424 = env  in
               {
                 solver = (uu___504_58424.solver);
                 range = (uu___504_58424.range);
                 curmodule = (uu___504_58424.curmodule);
                 gamma = (uu___504_58424.gamma);
                 gamma_sig = (uu___504_58424.gamma_sig);
                 gamma_cache = (uu___504_58424.gamma_cache);
                 modules = (uu___504_58424.modules);
                 expected_typ = (uu___504_58424.expected_typ);
                 sigtab = (uu___504_58424.sigtab);
                 attrtab = (uu___504_58424.attrtab);
                 is_pattern = (uu___504_58424.is_pattern);
                 instantiate_imp = (uu___504_58424.instantiate_imp);
                 effects = (uu___504_58424.effects);
                 generalize = (uu___504_58424.generalize);
                 letrecs = (uu___504_58424.letrecs);
                 top_level = (uu___504_58424.top_level);
                 check_uvars = (uu___504_58424.check_uvars);
                 use_eq = (uu___504_58424.use_eq);
                 is_iface = (uu___504_58424.is_iface);
                 admit = (uu___504_58424.admit);
                 lax = (uu___504_58424.lax);
                 lax_universes = (uu___504_58424.lax_universes);
                 phase1 = (uu___504_58424.phase1);
                 failhard = (uu___504_58424.failhard);
                 nosynth = (uu___504_58424.nosynth);
                 uvar_subtyping = (uu___504_58424.uvar_subtyping);
                 tc_term = (uu___504_58424.tc_term);
                 type_of = (uu___504_58424.type_of);
                 universe_of = (uu___504_58424.universe_of);
                 check_type_of = (uu___504_58424.check_type_of);
                 use_bv_sorts = (uu___504_58424.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___504_58424.normalized_eff_names);
                 fv_delta_depths = (uu___504_58424.fv_delta_depths);
                 proof_ns = (uu___504_58424.proof_ns);
                 synth_hook = (uu___504_58424.synth_hook);
                 splice = (uu___504_58424.splice);
                 postprocess = (uu___504_58424.postprocess);
                 is_native_tactic = (uu___504_58424.is_native_tactic);
                 identifier_info = (uu___504_58424.identifier_info);
                 tc_hooks = (uu___504_58424.tc_hooks);
                 dsenv = (uu___504_58424.dsenv);
                 nbe = (uu___504_58424.nbe)
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
        (let uu___511_58911 = e  in
         {
           solver = (uu___511_58911.solver);
           range = r;
           curmodule = (uu___511_58911.curmodule);
           gamma = (uu___511_58911.gamma);
           gamma_sig = (uu___511_58911.gamma_sig);
           gamma_cache = (uu___511_58911.gamma_cache);
           modules = (uu___511_58911.modules);
           expected_typ = (uu___511_58911.expected_typ);
           sigtab = (uu___511_58911.sigtab);
           attrtab = (uu___511_58911.attrtab);
           is_pattern = (uu___511_58911.is_pattern);
           instantiate_imp = (uu___511_58911.instantiate_imp);
           effects = (uu___511_58911.effects);
           generalize = (uu___511_58911.generalize);
           letrecs = (uu___511_58911.letrecs);
           top_level = (uu___511_58911.top_level);
           check_uvars = (uu___511_58911.check_uvars);
           use_eq = (uu___511_58911.use_eq);
           is_iface = (uu___511_58911.is_iface);
           admit = (uu___511_58911.admit);
           lax = (uu___511_58911.lax);
           lax_universes = (uu___511_58911.lax_universes);
           phase1 = (uu___511_58911.phase1);
           failhard = (uu___511_58911.failhard);
           nosynth = (uu___511_58911.nosynth);
           uvar_subtyping = (uu___511_58911.uvar_subtyping);
           tc_term = (uu___511_58911.tc_term);
           type_of = (uu___511_58911.type_of);
           universe_of = (uu___511_58911.universe_of);
           check_type_of = (uu___511_58911.check_type_of);
           use_bv_sorts = (uu___511_58911.use_bv_sorts);
           qtbl_name_and_index = (uu___511_58911.qtbl_name_and_index);
           normalized_eff_names = (uu___511_58911.normalized_eff_names);
           fv_delta_depths = (uu___511_58911.fv_delta_depths);
           proof_ns = (uu___511_58911.proof_ns);
           synth_hook = (uu___511_58911.synth_hook);
           splice = (uu___511_58911.splice);
           postprocess = (uu___511_58911.postprocess);
           is_native_tactic = (uu___511_58911.is_native_tactic);
           identifier_info = (uu___511_58911.identifier_info);
           tc_hooks = (uu___511_58911.tc_hooks);
           dsenv = (uu___511_58911.dsenv);
           nbe = (uu___511_58911.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____59255 =
        let uu____59262 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____59262 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____59255
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____59461 =
          let uu____59468 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____59468 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____59461
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____59663 =
          let uu____59670 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____59670 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____59663
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____59867 =
        let uu____59874 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____59874 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____59867
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___528_60354 = env  in
      {
        solver = (uu___528_60354.solver);
        range = (uu___528_60354.range);
        curmodule = lid;
        gamma = (uu___528_60354.gamma);
        gamma_sig = (uu___528_60354.gamma_sig);
        gamma_cache = (uu___528_60354.gamma_cache);
        modules = (uu___528_60354.modules);
        expected_typ = (uu___528_60354.expected_typ);
        sigtab = (uu___528_60354.sigtab);
        attrtab = (uu___528_60354.attrtab);
        is_pattern = (uu___528_60354.is_pattern);
        instantiate_imp = (uu___528_60354.instantiate_imp);
        effects = (uu___528_60354.effects);
        generalize = (uu___528_60354.generalize);
        letrecs = (uu___528_60354.letrecs);
        top_level = (uu___528_60354.top_level);
        check_uvars = (uu___528_60354.check_uvars);
        use_eq = (uu___528_60354.use_eq);
        is_iface = (uu___528_60354.is_iface);
        admit = (uu___528_60354.admit);
        lax = (uu___528_60354.lax);
        lax_universes = (uu___528_60354.lax_universes);
        phase1 = (uu___528_60354.phase1);
        failhard = (uu___528_60354.failhard);
        nosynth = (uu___528_60354.nosynth);
        uvar_subtyping = (uu___528_60354.uvar_subtyping);
        tc_term = (uu___528_60354.tc_term);
        type_of = (uu___528_60354.type_of);
        universe_of = (uu___528_60354.universe_of);
        check_type_of = (uu___528_60354.check_type_of);
        use_bv_sorts = (uu___528_60354.use_bv_sorts);
        qtbl_name_and_index = (uu___528_60354.qtbl_name_and_index);
        normalized_eff_names = (uu___528_60354.normalized_eff_names);
        fv_delta_depths = (uu___528_60354.fv_delta_depths);
        proof_ns = (uu___528_60354.proof_ns);
        synth_hook = (uu___528_60354.synth_hook);
        splice = (uu___528_60354.splice);
        postprocess = (uu___528_60354.postprocess);
        is_native_tactic = (uu___528_60354.is_native_tactic);
        identifier_info = (uu___528_60354.identifier_info);
        tc_hooks = (uu___528_60354.tc_hooks);
        dsenv = (uu___528_60354.dsenv);
        nbe = (uu___528_60354.nbe)
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
      let uu____60754 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____60754
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____60780 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____60780)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____60805 =
      let uu____60807 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____60807  in
    (FStar_Errors.Fatal_VariableNotFound, uu____60805)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____60816  ->
    let uu____60817 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____60817
  
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
      | ((formals,t),uu____60965) ->
          let vs = mk_univ_subst formals us  in
          let uu____61007 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____61007)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_61044  ->
    match uu___1_61044 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____61106  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____61138 = inst_tscheme t  in
      match uu____61138 with
      | (us,t1) ->
          let uu____61165 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____61165)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____61276  ->
          match uu____61276 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____61403 =
                         let uu____61405 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____61411 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____61415 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____61417 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____61405 uu____61411 uu____61415 uu____61417
                          in
                       failwith uu____61403)
                    else ();
                    (let uu____61422 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____61422))
               | uu____61447 ->
                   let uu____61448 =
                     let uu____61450 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____61450
                      in
                   failwith uu____61448)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____61466 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____61477 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____61488 -> false
  
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
             | ([],uu____61688) -> Maybe
             | (uu____61703,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____61747 -> No  in
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
          let uu____61988 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____61988 with
          | FStar_Pervasives_Native.None  ->
              let uu____62020 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_62082  ->
                     match uu___2_62082 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____62150 = FStar_Ident.lid_equals lid l  in
                         if uu____62150
                         then
                           let uu____62182 =
                             let uu____62210 =
                               let uu____62234 = inst_tscheme t  in
                               FStar_Util.Inl uu____62234  in
                             let uu____62262 = FStar_Ident.range_of_lid l  in
                             (uu____62210, uu____62262)  in
                           FStar_Pervasives_Native.Some uu____62182
                         else FStar_Pervasives_Native.None
                     | uu____62342 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____62020
                (fun uu____62398  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_62407  ->
                        match uu___3_62407 with
                        | (uu____62410,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____62412);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____62413;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____62414;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____62415;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____62416;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____62483 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____62483
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
                                  uu____62584 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____62599 -> cache t  in
                            let uu____62600 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____62600 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____62626 =
                                   let uu____62627 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____62627)
                                    in
                                 maybe_cache uu____62626)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____62739 = find_in_sigtab env lid  in
         match uu____62739 with
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
      let uu____63007 = lookup_qname env lid  in
      match uu____63007 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____63047,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____63357 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____63357 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____63673 =
          let uu____63681 = lookup_attr env1 attr  in se1 :: uu____63681  in
        FStar_Util.smap_add (attrtab env1) attr uu____63673  in
      FStar_List.iter
        (fun attr  ->
           let uu____63714 =
             let uu____63715 = FStar_Syntax_Subst.compress attr  in
             uu____63715.FStar_Syntax_Syntax.n  in
           match uu____63714 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____63730 =
                 let uu____63732 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____63732.FStar_Ident.str  in
               add_one1 env se uu____63730
           | uu____63741 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____63941) ->
          add_sigelts env ses
      | uu____63968 ->
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
            | uu____64065 -> ()))

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
        (fun uu___4_64292  ->
           match uu___4_64292 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____64327 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____64427,lb::[]),uu____64429) ->
            let uu____64474 =
              let uu____64487 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____64506 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____64487, uu____64506)  in
            FStar_Pervasives_Native.Some uu____64474
        | FStar_Syntax_Syntax.Sig_let ((uu____64527,lbs),uu____64529) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____64605 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____64646 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____64646
                     then
                       let uu____64663 =
                         let uu____64676 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____64695 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____64676, uu____64695)  in
                       FStar_Pervasives_Native.Some uu____64663
                     else FStar_Pervasives_Native.None)
        | uu____64730 -> FStar_Pervasives_Native.None
  
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
          let uu____64840 =
            let uu____64853 =
              let uu____64862 =
                let uu____64863 =
                  let uu____64874 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____64874
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____64863)  in
              inst_tscheme1 uu____64862  in
            (uu____64853, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____64840
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____64918,uu____64919) ->
          let uu____64940 =
            let uu____64953 =
              let uu____64962 =
                let uu____64963 =
                  let uu____64974 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____64974  in
                (us, uu____64963)  in
              inst_tscheme1 uu____64962  in
            (uu____64953, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____64940
      | uu____65015 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____65249 =
          match uu____65249 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____65401,uvs,t,uu____65404,uu____65405,uu____65406);
                      FStar_Syntax_Syntax.sigrng = uu____65407;
                      FStar_Syntax_Syntax.sigquals = uu____65408;
                      FStar_Syntax_Syntax.sigmeta = uu____65409;
                      FStar_Syntax_Syntax.sigattrs = uu____65410;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____65485 =
                     let uu____65498 = inst_tscheme1 (uvs, t)  in
                     (uu____65498, rng)  in
                   FStar_Pervasives_Native.Some uu____65485
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____65540;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____65542;
                      FStar_Syntax_Syntax.sigattrs = uu____65543;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____65596 =
                     let uu____65598 = in_cur_mod env l  in uu____65598 = Yes
                      in
                   if uu____65596
                   then
                     let uu____65614 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____65614
                      then
                        let uu____65634 =
                          let uu____65647 = inst_tscheme1 (uvs, t)  in
                          (uu____65647, rng)  in
                        FStar_Pervasives_Native.Some uu____65634
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____65702 =
                        let uu____65715 = inst_tscheme1 (uvs, t)  in
                        (uu____65715, rng)  in
                      FStar_Pervasives_Native.Some uu____65702)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____65758,uu____65759);
                      FStar_Syntax_Syntax.sigrng = uu____65760;
                      FStar_Syntax_Syntax.sigquals = uu____65761;
                      FStar_Syntax_Syntax.sigmeta = uu____65762;
                      FStar_Syntax_Syntax.sigattrs = uu____65763;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____65865 =
                          let uu____65878 = inst_tscheme1 (uvs, k)  in
                          (uu____65878, rng)  in
                        FStar_Pervasives_Native.Some uu____65865
                    | uu____65917 ->
                        let uu____65918 =
                          let uu____65931 =
                            let uu____65940 =
                              let uu____65941 =
                                let uu____65952 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____65952
                                 in
                              (uvs, uu____65941)  in
                            inst_tscheme1 uu____65940  in
                          (uu____65931, rng)  in
                        FStar_Pervasives_Native.Some uu____65918)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____65997,uu____65998);
                      FStar_Syntax_Syntax.sigrng = uu____65999;
                      FStar_Syntax_Syntax.sigquals = uu____66000;
                      FStar_Syntax_Syntax.sigmeta = uu____66001;
                      FStar_Syntax_Syntax.sigattrs = uu____66002;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____66105 =
                          let uu____66118 = inst_tscheme_with (uvs, k) us  in
                          (uu____66118, rng)  in
                        FStar_Pervasives_Native.Some uu____66105
                    | uu____66157 ->
                        let uu____66158 =
                          let uu____66171 =
                            let uu____66180 =
                              let uu____66181 =
                                let uu____66192 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____66192
                                 in
                              (uvs, uu____66181)  in
                            inst_tscheme_with uu____66180 us  in
                          (uu____66171, rng)  in
                        FStar_Pervasives_Native.Some uu____66158)
               | FStar_Util.Inr se ->
                   let uu____66264 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____66293;
                          FStar_Syntax_Syntax.sigrng = uu____66294;
                          FStar_Syntax_Syntax.sigquals = uu____66295;
                          FStar_Syntax_Syntax.sigmeta = uu____66296;
                          FStar_Syntax_Syntax.sigattrs = uu____66297;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____66332 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____66264
                     (FStar_Util.map_option
                        (fun uu____66406  ->
                           match uu____66406 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____66457 =
          let uu____66472 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____66472 mapper  in
        match uu____66457 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____66588 =
              let uu____66603 =
                let uu____66614 =
                  let uu___855_66625 = t  in
                  let uu____66634 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_66625.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____66634;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_66625.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____66614)  in
              (uu____66603, r)  in
            FStar_Pervasives_Native.Some uu____66588
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____66819 = lookup_qname env l  in
      match uu____66819 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____66849 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____67043 = try_lookup_bv env bv  in
      match uu____67043 with
      | FStar_Pervasives_Native.None  ->
          let uu____67070 = variable_not_found bv  in
          FStar_Errors.raise_error uu____67070 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____67102 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____67111 =
            let uu____67112 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____67112  in
          (uu____67102, uu____67111)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____67258 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____67258 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____67356 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____67356  in
          let uu____67357 =
            let uu____67370 =
              let uu____67379 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____67379)  in
            (uu____67370, r1)  in
          FStar_Pervasives_Native.Some uu____67357
  
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
        let uu____67554 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____67554 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____67603,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____67644 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____67644  in
            let uu____67645 =
              let uu____67654 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____67654, r1)  in
            FStar_Pervasives_Native.Some uu____67645
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____67814 = try_lookup_lid env l  in
      match uu____67814 with
      | FStar_Pervasives_Native.None  ->
          let uu____67853 = name_not_found l  in
          let uu____67859 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____67853 uu____67859
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_68026  ->
              match uu___5_68026 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____68032 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____68169 = lookup_qname env lid  in
      match uu____68169 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68178,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68181;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____68183;
              FStar_Syntax_Syntax.sigattrs = uu____68184;_},FStar_Pervasives_Native.None
            ),uu____68185)
          ->
          let uu____68288 =
            let uu____68295 =
              let uu____68296 =
                let uu____68307 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____68307 t  in
              (uvs, uu____68296)  in
            (uu____68295, q)  in
          FStar_Pervasives_Native.Some uu____68288
      | uu____68326 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68468 = lookup_qname env lid  in
      match uu____68468 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68477,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68480;
              FStar_Syntax_Syntax.sigquals = uu____68481;
              FStar_Syntax_Syntax.sigmeta = uu____68482;
              FStar_Syntax_Syntax.sigattrs = uu____68483;_},FStar_Pervasives_Native.None
            ),uu____68484)
          ->
          let uu____68587 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68587 (uvs, t)
      | uu____68598 ->
          let uu____68599 = name_not_found lid  in
          let uu____68605 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68599 uu____68605
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68749 = lookup_qname env lid  in
      match uu____68749 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68758,uvs,t,uu____68761,uu____68762,uu____68763);
              FStar_Syntax_Syntax.sigrng = uu____68764;
              FStar_Syntax_Syntax.sigquals = uu____68765;
              FStar_Syntax_Syntax.sigmeta = uu____68766;
              FStar_Syntax_Syntax.sigattrs = uu____68767;_},FStar_Pervasives_Native.None
            ),uu____68768)
          ->
          let uu____68893 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68893 (uvs, t)
      | uu____68904 ->
          let uu____68905 = name_not_found lid  in
          let uu____68911 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68905 uu____68911
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____69058 = lookup_qname env lid  in
      match uu____69058 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____69070,uu____69071,uu____69072,uu____69073,uu____69074,dcs);
              FStar_Syntax_Syntax.sigrng = uu____69076;
              FStar_Syntax_Syntax.sigquals = uu____69077;
              FStar_Syntax_Syntax.sigmeta = uu____69078;
              FStar_Syntax_Syntax.sigattrs = uu____69079;_},uu____69080),uu____69081)
          -> (true, dcs)
      | uu____69218 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____69362 = lookup_qname env lid  in
      match uu____69362 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____69367,uu____69368,uu____69369,l,uu____69371,uu____69372);
              FStar_Syntax_Syntax.sigrng = uu____69373;
              FStar_Syntax_Syntax.sigquals = uu____69374;
              FStar_Syntax_Syntax.sigmeta = uu____69375;
              FStar_Syntax_Syntax.sigattrs = uu____69376;_},uu____69377),uu____69378)
          -> l
      | uu____69505 ->
          let uu____69506 =
            let uu____69508 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____69508  in
          failwith uu____69506
  
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
                    (fun uu___6_69606  ->
                       match uu___6_69606 with
                       | Eager_unfolding_only (true ) ->
                           FStar_All.pipe_right attrs
                             (FStar_Util.for_some
                                (fun at  ->
                                   FStar_Syntax_Util.is_fvar
                                     FStar_Parser_Const.unfold_for_smt_attr
                                     at))
                       | uu____69626 -> false)))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69645)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69745) when
                   (visible se.FStar_Syntax_Syntax.sigquals
                      se.FStar_Syntax_Syntax.sigattrs)
                     && ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69825 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69825
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69884 -> FStar_Pervasives_Native.None)
          | uu____69899 -> FStar_Pervasives_Native.None
  
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
        let uu____70099 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____70099
  
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
        let uu____70256 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____70256
  
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
             (FStar_Util.Inl uu____70339,uu____70340) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____70420),uu____70421) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____70507 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____70541 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____70560 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____70593 ->
                  let uu____70608 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____70608
              | FStar_Syntax_Syntax.Sig_let ((uu____70609,lbs),uu____70611)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____70677 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____70677
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____70684 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____70700 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____70705 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____70720 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____70741 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____70762 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____70771 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____70792 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____70936 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____70936
           (fun d_opt  ->
              let uu____70949 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____70949
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____70959 =
                   let uu____70962 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____70962  in
                 match uu____70959 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____70967 =
                       let uu____70969 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____70969
                        in
                     failwith uu____70967
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____70974 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____70974
                       then
                         let uu____70977 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____70979 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____70981 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____70977 uu____70979 uu____70981
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
        (FStar_Util.Inr (se,uu____71006),uu____71007) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____71093 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____71127),uu____71128) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____71218 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____71368 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____71368
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____71519 = lookup_attrs_of_lid env fv_lid1  in
        match uu____71519 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____71579 =
                      let uu____71580 = FStar_Syntax_Util.un_uinst tm  in
                      uu____71580.FStar_Syntax_Syntax.n  in
                    match uu____71579 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____71596 -> false))
  
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
      let uu____71880 = lookup_qname env ftv  in
      match uu____71880 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____71888) ->
          let uu____71970 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____71970 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____72007,t),r) ->
               let uu____72038 =
                 let uu____72047 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____72047 t  in
               FStar_Pervasives_Native.Some uu____72038)
      | uu____72052 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____72192 = try_lookup_effect_lid env ftv  in
      match uu____72192 with
      | FStar_Pervasives_Native.None  ->
          let uu____72207 = name_not_found ftv  in
          let uu____72213 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____72207 uu____72213
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
        let uu____72369 = lookup_qname env lid0  in
        match uu____72369 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____72384);
                FStar_Syntax_Syntax.sigrng = uu____72385;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____72387;
                FStar_Syntax_Syntax.sigattrs = uu____72388;_},FStar_Pervasives_Native.None
              ),uu____72389)
            ->
            let lid1 =
              let uu____72505 =
                let uu____72506 = FStar_Ident.range_of_lid lid  in
                let uu____72507 =
                  let uu____72508 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____72508  in
                FStar_Range.set_use_range uu____72506 uu____72507  in
              FStar_Ident.set_lid_range lid uu____72505  in
            let uu____72509 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___7_72515  ->
                      match uu___7_72515 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____72518 -> false))
               in
            if uu____72509
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____72547 =
                      let uu____72549 =
                        let uu____72551 = get_range env  in
                        FStar_Range.string_of_range uu____72551  in
                      let uu____72552 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____72554 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____72549 uu____72552 uu____72554
                       in
                    failwith uu____72547)
                  in
               match (binders, univs1) with
               | ([],uu____72586) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____72630,uu____72631::uu____72632::uu____72633) ->
                   let uu____72676 =
                     let uu____72678 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____72680 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____72678 uu____72680
                      in
                   failwith uu____72676
               | uu____72697 ->
                   let uu____72719 =
                     let uu____72728 =
                       let uu____72729 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____72729)  in
                     inst_tscheme_with uu____72728 insts  in
                   (match uu____72719 with
                    | (uu____72760,t) ->
                        let t1 =
                          let uu____72779 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____72779 t  in
                        let uu____72780 =
                          let uu____72781 = FStar_Syntax_Subst.compress t1
                             in
                          uu____72781.FStar_Syntax_Syntax.n  in
                        (match uu____72780 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____72854 -> failwith "Impossible")))
        | uu____72866 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____73026 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____73026 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____73055,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____73082 = find1 l2  in
            (match uu____73082 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____73125 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____73125 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____73153 = find1 l  in
            (match uu____73153 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____73182 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____73182
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____73321 = lookup_qname env l1  in
      match uu____73321 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____73324;
              FStar_Syntax_Syntax.sigrng = uu____73325;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73327;
              FStar_Syntax_Syntax.sigattrs = uu____73328;_},uu____73329),uu____73330)
          -> q
      | uu____73439 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____73587 =
          let uu____73588 =
            let uu____73590 = FStar_Util.string_of_int i  in
            let uu____73592 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____73590 uu____73592
             in
          failwith uu____73588  in
        let uu____73599 = lookup_datacon env lid  in
        match uu____73599 with
        | (uu____73612,t) ->
            let uu____73622 =
              let uu____73623 = FStar_Syntax_Subst.compress t  in
              uu____73623.FStar_Syntax_Syntax.n  in
            (match uu____73622 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____73639) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____73720 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____73720
                      FStar_Pervasives_Native.fst)
             | uu____73767 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____73897 = lookup_qname env l  in
      match uu____73897 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73899,uu____73900,uu____73901);
              FStar_Syntax_Syntax.sigrng = uu____73902;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____73904;
              FStar_Syntax_Syntax.sigattrs = uu____73905;_},uu____73906),uu____73907)
          ->
          FStar_Util.for_some
            (fun uu___8_74014  ->
               match uu___8_74014 with
               | FStar_Syntax_Syntax.Projector uu____74016 -> true
               | uu____74028 -> false) quals
      | uu____74030 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____74160 = lookup_qname env lid  in
      match uu____74160 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____74162,uu____74163,uu____74164,uu____74165,uu____74166,uu____74167);
              FStar_Syntax_Syntax.sigrng = uu____74168;
              FStar_Syntax_Syntax.sigquals = uu____74169;
              FStar_Syntax_Syntax.sigmeta = uu____74170;
              FStar_Syntax_Syntax.sigattrs = uu____74171;_},uu____74172),uu____74173)
          -> true
      | uu____74301 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____74431 = lookup_qname env lid  in
      match uu____74431 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____74433,uu____74434,uu____74435,uu____74436,uu____74437,uu____74438);
              FStar_Syntax_Syntax.sigrng = uu____74439;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____74441;
              FStar_Syntax_Syntax.sigattrs = uu____74442;_},uu____74443),uu____74444)
          ->
          FStar_Util.for_some
            (fun uu___9_74575  ->
               match uu___9_74575 with
               | FStar_Syntax_Syntax.RecordType uu____74577 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____74591 -> true
               | uu____74605 -> false) quals
      | uu____74607 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____74617,uu____74618);
            FStar_Syntax_Syntax.sigrng = uu____74619;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____74621;
            FStar_Syntax_Syntax.sigattrs = uu____74622;_},uu____74623),uu____74624)
        ->
        FStar_Util.for_some
          (fun uu___10_74727  ->
             match uu___10_74727 with
             | FStar_Syntax_Syntax.Action uu____74729 -> true
             | uu____74735 -> false) quals
    | uu____74737 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____74867 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____74867
  
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
      let uu____75068 =
        let uu____75069 = FStar_Syntax_Util.un_uinst head1  in
        uu____75069.FStar_Syntax_Syntax.n  in
      match uu____75068 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75086 ->
               true
           | uu____75089 -> false)
      | uu____75091 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75221 = lookup_qname env l  in
      match uu____75221 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75224),uu____75225) ->
          FStar_Util.for_some
            (fun uu___11_75310  ->
               match uu___11_75310 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75313 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75315 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75534 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75565) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75602 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75618 ->
                 FStar_Pervasives_Native.Some true
             | uu____75653 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75656 =
        let uu____75660 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75660 mapper  in
      match uu____75656 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75854 = lookup_qname env lid  in
      match uu____75854 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75858,uu____75859,tps,uu____75861,uu____75862,uu____75863);
              FStar_Syntax_Syntax.sigrng = uu____75864;
              FStar_Syntax_Syntax.sigquals = uu____75865;
              FStar_Syntax_Syntax.sigmeta = uu____75866;
              FStar_Syntax_Syntax.sigattrs = uu____75867;_},uu____75868),uu____75869)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____76010 -> FStar_Pervasives_Native.None
  
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
           (fun uu____76252  ->
              match uu____76252 with
              | (d,uu____76281) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____76473 = effect_decl_opt env l  in
      match uu____76473 with
      | FStar_Pervasives_Native.None  ->
          let uu____76548 = name_not_found l  in
          let uu____76554 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76548 uu____76554
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76672  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76715  ->
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
        let uu____76915 = FStar_Ident.lid_equals l1 l2  in
        if uu____76915
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76954 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76954
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76993 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____77134  ->
                        match uu____77134 with
                        | (m1,m2,uu____77170,uu____77171,uu____77172) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76993 with
              | FStar_Pervasives_Native.None  ->
                  let uu____77269 =
                    let uu____77275 =
                      let uu____77277 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____77279 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____77277
                        uu____77279
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____77275)
                     in
                  FStar_Errors.raise_error uu____77269 env.range
              | FStar_Pervasives_Native.Some
                  (uu____77303,uu____77304,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____77556 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____77556
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
  'Auu____77618 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____77618) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____77704 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____77810  ->
                match uu____77810 with
                | (d,uu____77837) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____77704 with
      | FStar_Pervasives_Native.None  ->
          let uu____77917 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____77917
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____78001 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____78001 with
           | (uu____78035,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____78083)::(wp,uu____78085)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____78208 -> failwith "Impossible"))
  
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
          let uu____78533 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____78533
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____78542 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____78542
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
                  let uu____78621 = get_range env  in
                  let uu____78622 =
                    let uu____78629 =
                      let uu____78630 =
                        let uu____78655 =
                          let uu____78670 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____78670]  in
                        (null_wp, uu____78655)  in
                      FStar_Syntax_Syntax.Tm_app uu____78630  in
                    FStar_Syntax_Syntax.mk uu____78629  in
                  uu____78622 FStar_Pervasives_Native.None uu____78621  in
                let uu____78727 =
                  let uu____78738 =
                    let uu____78753 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____78753]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____78738;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____78727))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1515_79055 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1515_79055.order);
              joins = (uu___1515_79055.joins)
            }  in
          let uu___1518_79110 = env  in
          {
            solver = (uu___1518_79110.solver);
            range = (uu___1518_79110.range);
            curmodule = (uu___1518_79110.curmodule);
            gamma = (uu___1518_79110.gamma);
            gamma_sig = (uu___1518_79110.gamma_sig);
            gamma_cache = (uu___1518_79110.gamma_cache);
            modules = (uu___1518_79110.modules);
            expected_typ = (uu___1518_79110.expected_typ);
            sigtab = (uu___1518_79110.sigtab);
            attrtab = (uu___1518_79110.attrtab);
            is_pattern = (uu___1518_79110.is_pattern);
            instantiate_imp = (uu___1518_79110.instantiate_imp);
            effects;
            generalize = (uu___1518_79110.generalize);
            letrecs = (uu___1518_79110.letrecs);
            top_level = (uu___1518_79110.top_level);
            check_uvars = (uu___1518_79110.check_uvars);
            use_eq = (uu___1518_79110.use_eq);
            is_iface = (uu___1518_79110.is_iface);
            admit = (uu___1518_79110.admit);
            lax = (uu___1518_79110.lax);
            lax_universes = (uu___1518_79110.lax_universes);
            phase1 = (uu___1518_79110.phase1);
            failhard = (uu___1518_79110.failhard);
            nosynth = (uu___1518_79110.nosynth);
            uvar_subtyping = (uu___1518_79110.uvar_subtyping);
            tc_term = (uu___1518_79110.tc_term);
            type_of = (uu___1518_79110.type_of);
            universe_of = (uu___1518_79110.universe_of);
            check_type_of = (uu___1518_79110.check_type_of);
            use_bv_sorts = (uu___1518_79110.use_bv_sorts);
            qtbl_name_and_index = (uu___1518_79110.qtbl_name_and_index);
            normalized_eff_names = (uu___1518_79110.normalized_eff_names);
            fv_delta_depths = (uu___1518_79110.fv_delta_depths);
            proof_ns = (uu___1518_79110.proof_ns);
            synth_hook = (uu___1518_79110.synth_hook);
            splice = (uu___1518_79110.splice);
            postprocess = (uu___1518_79110.postprocess);
            is_native_tactic = (uu___1518_79110.is_native_tactic);
            identifier_info = (uu___1518_79110.identifier_info);
            tc_hooks = (uu___1518_79110.tc_hooks);
            dsenv = (uu___1518_79110.dsenv);
            nbe = (uu___1518_79110.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____79328 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____79328  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____79682 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____79691 = l1 u t wp e  in
                                l2 u t uu____79682 uu____79691))
                | uu____79700 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____79840 = inst_tscheme_with lift_t [u]  in
            match uu____79840 with
            | (uu____79855,lift_t1) ->
                let uu____79865 =
                  let uu____79872 =
                    let uu____79873 =
                      let uu____79898 =
                        let uu____79913 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____79926 =
                          let uu____79941 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____79941]  in
                        uu____79913 :: uu____79926  in
                      (lift_t1, uu____79898)  in
                    FStar_Syntax_Syntax.Tm_app uu____79873  in
                  FStar_Syntax_Syntax.mk uu____79872  in
                uu____79865 FStar_Pervasives_Native.None
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
            let uu____80139 = inst_tscheme_with lift_t [u]  in
            match uu____80139 with
            | (uu____80154,lift_t1) ->
                let uu____80164 =
                  let uu____80171 =
                    let uu____80172 =
                      let uu____80197 =
                        let uu____80212 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____80225 =
                          let uu____80240 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____80253 =
                            let uu____80268 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____80268]  in
                          uu____80240 :: uu____80253  in
                        uu____80212 :: uu____80225  in
                      (lift_t1, uu____80197)  in
                    FStar_Syntax_Syntax.Tm_app uu____80172  in
                  FStar_Syntax_Syntax.mk uu____80171  in
                uu____80164 FStar_Pervasives_Native.None
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
              let uu____80487 =
                let uu____80494 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____80494
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____80487  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____80535 =
              let uu____80537 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____80537  in
            let uu____80546 =
              let uu____80548 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____80608 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____80608)
                 in
              FStar_Util.dflt "none" uu____80548  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____80535
              uu____80546
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____80711  ->
                    match uu____80711 with
                    | (e,uu____80743) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____80828 =
            match uu____80828 with
            | (i,j) ->
                let uu____80877 = FStar_Ident.lid_equals i j  in
                if uu____80877
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _80912  -> FStar_Pervasives_Native.Some _80912)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____81005 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____81048 = FStar_Ident.lid_equals i k  in
                        if uu____81048
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____81102 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____81102
                                  then []
                                  else
                                    (let uu____81123 =
                                       let uu____81146 =
                                         find_edge order1 (i, k)  in
                                       let uu____81164 =
                                         find_edge order1 (k, j)  in
                                       (uu____81146, uu____81164)  in
                                     match uu____81123 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____81257 =
                                           compose_edges e1 e2  in
                                         [uu____81257]
                                     | uu____81286 -> [])))))
                 in
              FStar_List.append order1 uu____81005  in
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
                   let uu____81415 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____81418 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____81418
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____81415
                   then
                     let uu____81425 =
                       let uu____81431 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____81431)
                        in
                     let uu____81435 = get_range env  in
                     FStar_Errors.raise_error uu____81425 uu____81435
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____81665 = FStar_Ident.lid_equals i j
                                   in
                                if uu____81665
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____81837 =
                                              let uu____81860 =
                                                find_edge order2 (i, k)  in
                                              let uu____81878 =
                                                find_edge order2 (j, k)  in
                                              (uu____81860, uu____81878)  in
                                            match uu____81837 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____82081,uu____82082)
                                                     ->
                                                     let uu____82143 =
                                                       let uu____82150 =
                                                         let uu____82152 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____82152
                                                          in
                                                       let uu____82177 =
                                                         let uu____82179 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____82179
                                                          in
                                                       (uu____82150,
                                                         uu____82177)
                                                        in
                                                     (match uu____82143 with
                                                      | (true ,true ) ->
                                                          let uu____82236 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____82236
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
                                            | uu____82351 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1645_82644 = env.effects  in
              { decls = (uu___1645_82644.decls); order = order2; joins }  in
            let uu___1648_82651 = env  in
            {
              solver = (uu___1648_82651.solver);
              range = (uu___1648_82651.range);
              curmodule = (uu___1648_82651.curmodule);
              gamma = (uu___1648_82651.gamma);
              gamma_sig = (uu___1648_82651.gamma_sig);
              gamma_cache = (uu___1648_82651.gamma_cache);
              modules = (uu___1648_82651.modules);
              expected_typ = (uu___1648_82651.expected_typ);
              sigtab = (uu___1648_82651.sigtab);
              attrtab = (uu___1648_82651.attrtab);
              is_pattern = (uu___1648_82651.is_pattern);
              instantiate_imp = (uu___1648_82651.instantiate_imp);
              effects;
              generalize = (uu___1648_82651.generalize);
              letrecs = (uu___1648_82651.letrecs);
              top_level = (uu___1648_82651.top_level);
              check_uvars = (uu___1648_82651.check_uvars);
              use_eq = (uu___1648_82651.use_eq);
              is_iface = (uu___1648_82651.is_iface);
              admit = (uu___1648_82651.admit);
              lax = (uu___1648_82651.lax);
              lax_universes = (uu___1648_82651.lax_universes);
              phase1 = (uu___1648_82651.phase1);
              failhard = (uu___1648_82651.failhard);
              nosynth = (uu___1648_82651.nosynth);
              uvar_subtyping = (uu___1648_82651.uvar_subtyping);
              tc_term = (uu___1648_82651.tc_term);
              type_of = (uu___1648_82651.type_of);
              universe_of = (uu___1648_82651.universe_of);
              check_type_of = (uu___1648_82651.check_type_of);
              use_bv_sorts = (uu___1648_82651.use_bv_sorts);
              qtbl_name_and_index = (uu___1648_82651.qtbl_name_and_index);
              normalized_eff_names = (uu___1648_82651.normalized_eff_names);
              fv_delta_depths = (uu___1648_82651.fv_delta_depths);
              proof_ns = (uu___1648_82651.proof_ns);
              synth_hook = (uu___1648_82651.synth_hook);
              splice = (uu___1648_82651.splice);
              postprocess = (uu___1648_82651.postprocess);
              is_native_tactic = (uu___1648_82651.is_native_tactic);
              identifier_info = (uu___1648_82651.identifier_info);
              tc_hooks = (uu___1648_82651.tc_hooks);
              dsenv = (uu___1648_82651.dsenv);
              nbe = (uu___1648_82651.nbe)
            }))
      | uu____82760 -> env
  
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
        | uu____82938 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____83082 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____83082 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____83124 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____83124 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____83175 =
                     let uu____83181 =
                       let uu____83183 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____83196 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____83211 =
                         let uu____83213 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____83213  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____83183 uu____83196 uu____83211
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____83181)
                      in
                   FStar_Errors.raise_error uu____83175
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____83229 =
                     let uu____83244 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____83244 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____83298  ->
                        fun uu____83299  ->
                          match (uu____83298, uu____83299) with
                          | ((x,uu____83347),(t,uu____83349)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____83229
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____83432 =
                     let uu___1686_83443 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1686_83443.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1686_83443.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1686_83443.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1686_83443.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____83432
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____83474 .
    'Auu____83474 ->
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
          let uu____83632 = effect_decl_opt env effect_name  in
          match uu____83632 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____83787 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____83836 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____83891 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____83891
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____83896 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____83896
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____83931 =
                     let uu____83942 = get_range env  in
                     let uu____83943 =
                       let uu____83950 =
                         let uu____83951 =
                           let uu____83976 =
                             let uu____83991 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____83991; wp]  in
                           (repr, uu____83976)  in
                         FStar_Syntax_Syntax.Tm_app uu____83951  in
                       FStar_Syntax_Syntax.mk uu____83950  in
                     uu____83943 FStar_Pervasives_Native.None uu____83942  in
                   FStar_Pervasives_Native.Some uu____83931)
  
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
      | uu____84902 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____85033 =
        let uu____85034 = FStar_Syntax_Subst.compress t  in
        uu____85034.FStar_Syntax_Syntax.n  in
      match uu____85033 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____85046,c) ->
          is_reifiable_comp env c
      | uu____85086 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____85238 =
           let uu____85240 = is_reifiable_effect env l  in
           Prims.op_Negation uu____85240  in
         if uu____85238
         then
           let uu____85243 =
             let uu____85249 =
               let uu____85251 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____85251
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____85249)  in
           let uu____85255 = get_range env  in
           FStar_Errors.raise_error uu____85243 uu____85255
         else ());
        (let uu____85258 = effect_repr_aux true env c u_c  in
         match uu____85258 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1751_85616 = env  in
        {
          solver = (uu___1751_85616.solver);
          range = (uu___1751_85616.range);
          curmodule = (uu___1751_85616.curmodule);
          gamma = (uu___1751_85616.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1751_85616.gamma_cache);
          modules = (uu___1751_85616.modules);
          expected_typ = (uu___1751_85616.expected_typ);
          sigtab = (uu___1751_85616.sigtab);
          attrtab = (uu___1751_85616.attrtab);
          is_pattern = (uu___1751_85616.is_pattern);
          instantiate_imp = (uu___1751_85616.instantiate_imp);
          effects = (uu___1751_85616.effects);
          generalize = (uu___1751_85616.generalize);
          letrecs = (uu___1751_85616.letrecs);
          top_level = (uu___1751_85616.top_level);
          check_uvars = (uu___1751_85616.check_uvars);
          use_eq = (uu___1751_85616.use_eq);
          is_iface = (uu___1751_85616.is_iface);
          admit = (uu___1751_85616.admit);
          lax = (uu___1751_85616.lax);
          lax_universes = (uu___1751_85616.lax_universes);
          phase1 = (uu___1751_85616.phase1);
          failhard = (uu___1751_85616.failhard);
          nosynth = (uu___1751_85616.nosynth);
          uvar_subtyping = (uu___1751_85616.uvar_subtyping);
          tc_term = (uu___1751_85616.tc_term);
          type_of = (uu___1751_85616.type_of);
          universe_of = (uu___1751_85616.universe_of);
          check_type_of = (uu___1751_85616.check_type_of);
          use_bv_sorts = (uu___1751_85616.use_bv_sorts);
          qtbl_name_and_index = (uu___1751_85616.qtbl_name_and_index);
          normalized_eff_names = (uu___1751_85616.normalized_eff_names);
          fv_delta_depths = (uu___1751_85616.fv_delta_depths);
          proof_ns = (uu___1751_85616.proof_ns);
          synth_hook = (uu___1751_85616.synth_hook);
          splice = (uu___1751_85616.splice);
          postprocess = (uu___1751_85616.postprocess);
          is_native_tactic = (uu___1751_85616.is_native_tactic);
          identifier_info = (uu___1751_85616.identifier_info);
          tc_hooks = (uu___1751_85616.tc_hooks);
          dsenv = (uu___1751_85616.dsenv);
          nbe = (uu___1751_85616.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1758_86008 = env  in
      {
        solver = (uu___1758_86008.solver);
        range = (uu___1758_86008.range);
        curmodule = (uu___1758_86008.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1758_86008.gamma_sig);
        gamma_cache = (uu___1758_86008.gamma_cache);
        modules = (uu___1758_86008.modules);
        expected_typ = (uu___1758_86008.expected_typ);
        sigtab = (uu___1758_86008.sigtab);
        attrtab = (uu___1758_86008.attrtab);
        is_pattern = (uu___1758_86008.is_pattern);
        instantiate_imp = (uu___1758_86008.instantiate_imp);
        effects = (uu___1758_86008.effects);
        generalize = (uu___1758_86008.generalize);
        letrecs = (uu___1758_86008.letrecs);
        top_level = (uu___1758_86008.top_level);
        check_uvars = (uu___1758_86008.check_uvars);
        use_eq = (uu___1758_86008.use_eq);
        is_iface = (uu___1758_86008.is_iface);
        admit = (uu___1758_86008.admit);
        lax = (uu___1758_86008.lax);
        lax_universes = (uu___1758_86008.lax_universes);
        phase1 = (uu___1758_86008.phase1);
        failhard = (uu___1758_86008.failhard);
        nosynth = (uu___1758_86008.nosynth);
        uvar_subtyping = (uu___1758_86008.uvar_subtyping);
        tc_term = (uu___1758_86008.tc_term);
        type_of = (uu___1758_86008.type_of);
        universe_of = (uu___1758_86008.universe_of);
        check_type_of = (uu___1758_86008.check_type_of);
        use_bv_sorts = (uu___1758_86008.use_bv_sorts);
        qtbl_name_and_index = (uu___1758_86008.qtbl_name_and_index);
        normalized_eff_names = (uu___1758_86008.normalized_eff_names);
        fv_delta_depths = (uu___1758_86008.fv_delta_depths);
        proof_ns = (uu___1758_86008.proof_ns);
        synth_hook = (uu___1758_86008.synth_hook);
        splice = (uu___1758_86008.splice);
        postprocess = (uu___1758_86008.postprocess);
        is_native_tactic = (uu___1758_86008.is_native_tactic);
        identifier_info = (uu___1758_86008.identifier_info);
        tc_hooks = (uu___1758_86008.tc_hooks);
        dsenv = (uu___1758_86008.dsenv);
        nbe = (uu___1758_86008.nbe)
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
            (let uu___1771_86985 = env  in
             {
               solver = (uu___1771_86985.solver);
               range = (uu___1771_86985.range);
               curmodule = (uu___1771_86985.curmodule);
               gamma = rest;
               gamma_sig = (uu___1771_86985.gamma_sig);
               gamma_cache = (uu___1771_86985.gamma_cache);
               modules = (uu___1771_86985.modules);
               expected_typ = (uu___1771_86985.expected_typ);
               sigtab = (uu___1771_86985.sigtab);
               attrtab = (uu___1771_86985.attrtab);
               is_pattern = (uu___1771_86985.is_pattern);
               instantiate_imp = (uu___1771_86985.instantiate_imp);
               effects = (uu___1771_86985.effects);
               generalize = (uu___1771_86985.generalize);
               letrecs = (uu___1771_86985.letrecs);
               top_level = (uu___1771_86985.top_level);
               check_uvars = (uu___1771_86985.check_uvars);
               use_eq = (uu___1771_86985.use_eq);
               is_iface = (uu___1771_86985.is_iface);
               admit = (uu___1771_86985.admit);
               lax = (uu___1771_86985.lax);
               lax_universes = (uu___1771_86985.lax_universes);
               phase1 = (uu___1771_86985.phase1);
               failhard = (uu___1771_86985.failhard);
               nosynth = (uu___1771_86985.nosynth);
               uvar_subtyping = (uu___1771_86985.uvar_subtyping);
               tc_term = (uu___1771_86985.tc_term);
               type_of = (uu___1771_86985.type_of);
               universe_of = (uu___1771_86985.universe_of);
               check_type_of = (uu___1771_86985.check_type_of);
               use_bv_sorts = (uu___1771_86985.use_bv_sorts);
               qtbl_name_and_index = (uu___1771_86985.qtbl_name_and_index);
               normalized_eff_names = (uu___1771_86985.normalized_eff_names);
               fv_delta_depths = (uu___1771_86985.fv_delta_depths);
               proof_ns = (uu___1771_86985.proof_ns);
               synth_hook = (uu___1771_86985.synth_hook);
               splice = (uu___1771_86985.splice);
               postprocess = (uu___1771_86985.postprocess);
               is_native_tactic = (uu___1771_86985.is_native_tactic);
               identifier_info = (uu___1771_86985.identifier_info);
               tc_hooks = (uu___1771_86985.tc_hooks);
               dsenv = (uu___1771_86985.dsenv);
               nbe = (uu___1771_86985.nbe)
             }))
    | uu____87094 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____87403  ->
             match uu____87403 with | (x,uu____87524) -> push_bv env1 x) env
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
            let uu___1785_87604 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1785_87604.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1785_87604.FStar_Syntax_Syntax.index);
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
      (let uu___1796_88027 = env  in
       {
         solver = (uu___1796_88027.solver);
         range = (uu___1796_88027.range);
         curmodule = (uu___1796_88027.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1796_88027.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1796_88027.sigtab);
         attrtab = (uu___1796_88027.attrtab);
         is_pattern = (uu___1796_88027.is_pattern);
         instantiate_imp = (uu___1796_88027.instantiate_imp);
         effects = (uu___1796_88027.effects);
         generalize = (uu___1796_88027.generalize);
         letrecs = (uu___1796_88027.letrecs);
         top_level = (uu___1796_88027.top_level);
         check_uvars = (uu___1796_88027.check_uvars);
         use_eq = (uu___1796_88027.use_eq);
         is_iface = (uu___1796_88027.is_iface);
         admit = (uu___1796_88027.admit);
         lax = (uu___1796_88027.lax);
         lax_universes = (uu___1796_88027.lax_universes);
         phase1 = (uu___1796_88027.phase1);
         failhard = (uu___1796_88027.failhard);
         nosynth = (uu___1796_88027.nosynth);
         uvar_subtyping = (uu___1796_88027.uvar_subtyping);
         tc_term = (uu___1796_88027.tc_term);
         type_of = (uu___1796_88027.type_of);
         universe_of = (uu___1796_88027.universe_of);
         check_type_of = (uu___1796_88027.check_type_of);
         use_bv_sorts = (uu___1796_88027.use_bv_sorts);
         qtbl_name_and_index = (uu___1796_88027.qtbl_name_and_index);
         normalized_eff_names = (uu___1796_88027.normalized_eff_names);
         fv_delta_depths = (uu___1796_88027.fv_delta_depths);
         proof_ns = (uu___1796_88027.proof_ns);
         synth_hook = (uu___1796_88027.synth_hook);
         splice = (uu___1796_88027.splice);
         postprocess = (uu___1796_88027.postprocess);
         is_native_tactic = (uu___1796_88027.is_native_tactic);
         identifier_info = (uu___1796_88027.identifier_info);
         tc_hooks = (uu___1796_88027.tc_hooks);
         dsenv = (uu___1796_88027.dsenv);
         nbe = (uu___1796_88027.nbe)
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
        let uu____88693 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____88693 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____88893 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____88893)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1811_89149 = env  in
      {
        solver = (uu___1811_89149.solver);
        range = (uu___1811_89149.range);
        curmodule = (uu___1811_89149.curmodule);
        gamma = (uu___1811_89149.gamma);
        gamma_sig = (uu___1811_89149.gamma_sig);
        gamma_cache = (uu___1811_89149.gamma_cache);
        modules = (uu___1811_89149.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1811_89149.sigtab);
        attrtab = (uu___1811_89149.attrtab);
        is_pattern = (uu___1811_89149.is_pattern);
        instantiate_imp = (uu___1811_89149.instantiate_imp);
        effects = (uu___1811_89149.effects);
        generalize = (uu___1811_89149.generalize);
        letrecs = (uu___1811_89149.letrecs);
        top_level = (uu___1811_89149.top_level);
        check_uvars = (uu___1811_89149.check_uvars);
        use_eq = false;
        is_iface = (uu___1811_89149.is_iface);
        admit = (uu___1811_89149.admit);
        lax = (uu___1811_89149.lax);
        lax_universes = (uu___1811_89149.lax_universes);
        phase1 = (uu___1811_89149.phase1);
        failhard = (uu___1811_89149.failhard);
        nosynth = (uu___1811_89149.nosynth);
        uvar_subtyping = (uu___1811_89149.uvar_subtyping);
        tc_term = (uu___1811_89149.tc_term);
        type_of = (uu___1811_89149.type_of);
        universe_of = (uu___1811_89149.universe_of);
        check_type_of = (uu___1811_89149.check_type_of);
        use_bv_sorts = (uu___1811_89149.use_bv_sorts);
        qtbl_name_and_index = (uu___1811_89149.qtbl_name_and_index);
        normalized_eff_names = (uu___1811_89149.normalized_eff_names);
        fv_delta_depths = (uu___1811_89149.fv_delta_depths);
        proof_ns = (uu___1811_89149.proof_ns);
        synth_hook = (uu___1811_89149.synth_hook);
        splice = (uu___1811_89149.splice);
        postprocess = (uu___1811_89149.postprocess);
        is_native_tactic = (uu___1811_89149.is_native_tactic);
        identifier_info = (uu___1811_89149.identifier_info);
        tc_hooks = (uu___1811_89149.tc_hooks);
        dsenv = (uu___1811_89149.dsenv);
        nbe = (uu___1811_89149.nbe)
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
    let uu____89652 = expected_typ env_  in
    ((let uu___1818_89720 = env_  in
      {
        solver = (uu___1818_89720.solver);
        range = (uu___1818_89720.range);
        curmodule = (uu___1818_89720.curmodule);
        gamma = (uu___1818_89720.gamma);
        gamma_sig = (uu___1818_89720.gamma_sig);
        gamma_cache = (uu___1818_89720.gamma_cache);
        modules = (uu___1818_89720.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1818_89720.sigtab);
        attrtab = (uu___1818_89720.attrtab);
        is_pattern = (uu___1818_89720.is_pattern);
        instantiate_imp = (uu___1818_89720.instantiate_imp);
        effects = (uu___1818_89720.effects);
        generalize = (uu___1818_89720.generalize);
        letrecs = (uu___1818_89720.letrecs);
        top_level = (uu___1818_89720.top_level);
        check_uvars = (uu___1818_89720.check_uvars);
        use_eq = false;
        is_iface = (uu___1818_89720.is_iface);
        admit = (uu___1818_89720.admit);
        lax = (uu___1818_89720.lax);
        lax_universes = (uu___1818_89720.lax_universes);
        phase1 = (uu___1818_89720.phase1);
        failhard = (uu___1818_89720.failhard);
        nosynth = (uu___1818_89720.nosynth);
        uvar_subtyping = (uu___1818_89720.uvar_subtyping);
        tc_term = (uu___1818_89720.tc_term);
        type_of = (uu___1818_89720.type_of);
        universe_of = (uu___1818_89720.universe_of);
        check_type_of = (uu___1818_89720.check_type_of);
        use_bv_sorts = (uu___1818_89720.use_bv_sorts);
        qtbl_name_and_index = (uu___1818_89720.qtbl_name_and_index);
        normalized_eff_names = (uu___1818_89720.normalized_eff_names);
        fv_delta_depths = (uu___1818_89720.fv_delta_depths);
        proof_ns = (uu___1818_89720.proof_ns);
        synth_hook = (uu___1818_89720.synth_hook);
        splice = (uu___1818_89720.splice);
        postprocess = (uu___1818_89720.postprocess);
        is_native_tactic = (uu___1818_89720.is_native_tactic);
        identifier_info = (uu___1818_89720.identifier_info);
        tc_hooks = (uu___1818_89720.tc_hooks);
        dsenv = (uu___1818_89720.dsenv);
        nbe = (uu___1818_89720.nbe)
      }), uu____89652)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____89968 =
      let uu____89973 = FStar_Ident.id_of_text ""  in [uu____89973]  in
    FStar_Ident.lid_of_ids uu____89968  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____90055 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____90055
        then
          let uu____90065 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____90065 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1826_90150 = env  in
       {
         solver = (uu___1826_90150.solver);
         range = (uu___1826_90150.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1826_90150.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1826_90150.expected_typ);
         sigtab = (uu___1826_90150.sigtab);
         attrtab = (uu___1826_90150.attrtab);
         is_pattern = (uu___1826_90150.is_pattern);
         instantiate_imp = (uu___1826_90150.instantiate_imp);
         effects = (uu___1826_90150.effects);
         generalize = (uu___1826_90150.generalize);
         letrecs = (uu___1826_90150.letrecs);
         top_level = (uu___1826_90150.top_level);
         check_uvars = (uu___1826_90150.check_uvars);
         use_eq = (uu___1826_90150.use_eq);
         is_iface = (uu___1826_90150.is_iface);
         admit = (uu___1826_90150.admit);
         lax = (uu___1826_90150.lax);
         lax_universes = (uu___1826_90150.lax_universes);
         phase1 = (uu___1826_90150.phase1);
         failhard = (uu___1826_90150.failhard);
         nosynth = (uu___1826_90150.nosynth);
         uvar_subtyping = (uu___1826_90150.uvar_subtyping);
         tc_term = (uu___1826_90150.tc_term);
         type_of = (uu___1826_90150.type_of);
         universe_of = (uu___1826_90150.universe_of);
         check_type_of = (uu___1826_90150.check_type_of);
         use_bv_sorts = (uu___1826_90150.use_bv_sorts);
         qtbl_name_and_index = (uu___1826_90150.qtbl_name_and_index);
         normalized_eff_names = (uu___1826_90150.normalized_eff_names);
         fv_delta_depths = (uu___1826_90150.fv_delta_depths);
         proof_ns = (uu___1826_90150.proof_ns);
         synth_hook = (uu___1826_90150.synth_hook);
         splice = (uu___1826_90150.splice);
         postprocess = (uu___1826_90150.postprocess);
         is_native_tactic = (uu___1826_90150.is_native_tactic);
         identifier_info = (uu___1826_90150.identifier_info);
         tc_hooks = (uu___1826_90150.tc_hooks);
         dsenv = (uu___1826_90150.dsenv);
         nbe = (uu___1826_90150.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____90506)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____90512,(uu____90513,t)))::tl1
          ->
          let uu____90560 =
            let uu____90571 = FStar_Syntax_Free.uvars t  in
            ext out uu____90571  in
          aux uu____90560 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____90582;
            FStar_Syntax_Syntax.index = uu____90583;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____90597 =
            let uu____90608 = FStar_Syntax_Free.uvars t  in
            ext out uu____90608  in
          aux uu____90597 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____90782)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____90788,(uu____90789,t)))::tl1
          ->
          let uu____90836 =
            let uu____90839 = FStar_Syntax_Free.univs t  in
            ext out uu____90839  in
          aux uu____90836 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____90842;
            FStar_Syntax_Syntax.index = uu____90843;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____90857 =
            let uu____90860 = FStar_Syntax_Free.univs t  in
            ext out uu____90860  in
          aux uu____90857 tl1
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
          let uu____91056 = FStar_Util.set_add uname out  in
          aux uu____91056 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____91063,(uu____91064,t)))::tl1
          ->
          let uu____91111 =
            let uu____91116 = FStar_Syntax_Free.univnames t  in
            ext out uu____91116  in
          aux uu____91111 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____91121;
            FStar_Syntax_Syntax.index = uu____91122;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____91136 =
            let uu____91141 = FStar_Syntax_Free.univnames t  in
            ext out uu____91141  in
          aux uu____91136 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_91179  ->
            match uu___12_91179 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____91203 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____91231 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____91249 =
      let uu____91263 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____91263
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____91249 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____91562 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_91575  ->
              match uu___13_91575 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____91583 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____91583
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____91591) ->
                  let uu____91628 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____91628))
       in
    FStar_All.pipe_right uu____91562 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_91642  ->
    match uu___14_91642 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only (true ) -> "Eager_unfolding_only true"
    | Eager_unfolding_only uu____91648 -> "Eager_unfolding_only false"
    | Unfold d ->
        let uu____91652 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____91652
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____91817  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____91993) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____92026,uu____92027) -> false  in
      let uu____92041 =
        FStar_List.tryFind
          (fun uu____92063  ->
             match uu____92063 with | (p,uu____92074) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____92041 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____92093,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____92239 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____92239
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1972_92531 = e  in
        {
          solver = (uu___1972_92531.solver);
          range = (uu___1972_92531.range);
          curmodule = (uu___1972_92531.curmodule);
          gamma = (uu___1972_92531.gamma);
          gamma_sig = (uu___1972_92531.gamma_sig);
          gamma_cache = (uu___1972_92531.gamma_cache);
          modules = (uu___1972_92531.modules);
          expected_typ = (uu___1972_92531.expected_typ);
          sigtab = (uu___1972_92531.sigtab);
          attrtab = (uu___1972_92531.attrtab);
          is_pattern = (uu___1972_92531.is_pattern);
          instantiate_imp = (uu___1972_92531.instantiate_imp);
          effects = (uu___1972_92531.effects);
          generalize = (uu___1972_92531.generalize);
          letrecs = (uu___1972_92531.letrecs);
          top_level = (uu___1972_92531.top_level);
          check_uvars = (uu___1972_92531.check_uvars);
          use_eq = (uu___1972_92531.use_eq);
          is_iface = (uu___1972_92531.is_iface);
          admit = (uu___1972_92531.admit);
          lax = (uu___1972_92531.lax);
          lax_universes = (uu___1972_92531.lax_universes);
          phase1 = (uu___1972_92531.phase1);
          failhard = (uu___1972_92531.failhard);
          nosynth = (uu___1972_92531.nosynth);
          uvar_subtyping = (uu___1972_92531.uvar_subtyping);
          tc_term = (uu___1972_92531.tc_term);
          type_of = (uu___1972_92531.type_of);
          universe_of = (uu___1972_92531.universe_of);
          check_type_of = (uu___1972_92531.check_type_of);
          use_bv_sorts = (uu___1972_92531.use_bv_sorts);
          qtbl_name_and_index = (uu___1972_92531.qtbl_name_and_index);
          normalized_eff_names = (uu___1972_92531.normalized_eff_names);
          fv_delta_depths = (uu___1972_92531.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1972_92531.synth_hook);
          splice = (uu___1972_92531.splice);
          postprocess = (uu___1972_92531.postprocess);
          is_native_tactic = (uu___1972_92531.is_native_tactic);
          identifier_info = (uu___1972_92531.identifier_info);
          tc_hooks = (uu___1972_92531.tc_hooks);
          dsenv = (uu___1972_92531.dsenv);
          nbe = (uu___1972_92531.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1981_93281 = e  in
      {
        solver = (uu___1981_93281.solver);
        range = (uu___1981_93281.range);
        curmodule = (uu___1981_93281.curmodule);
        gamma = (uu___1981_93281.gamma);
        gamma_sig = (uu___1981_93281.gamma_sig);
        gamma_cache = (uu___1981_93281.gamma_cache);
        modules = (uu___1981_93281.modules);
        expected_typ = (uu___1981_93281.expected_typ);
        sigtab = (uu___1981_93281.sigtab);
        attrtab = (uu___1981_93281.attrtab);
        is_pattern = (uu___1981_93281.is_pattern);
        instantiate_imp = (uu___1981_93281.instantiate_imp);
        effects = (uu___1981_93281.effects);
        generalize = (uu___1981_93281.generalize);
        letrecs = (uu___1981_93281.letrecs);
        top_level = (uu___1981_93281.top_level);
        check_uvars = (uu___1981_93281.check_uvars);
        use_eq = (uu___1981_93281.use_eq);
        is_iface = (uu___1981_93281.is_iface);
        admit = (uu___1981_93281.admit);
        lax = (uu___1981_93281.lax);
        lax_universes = (uu___1981_93281.lax_universes);
        phase1 = (uu___1981_93281.phase1);
        failhard = (uu___1981_93281.failhard);
        nosynth = (uu___1981_93281.nosynth);
        uvar_subtyping = (uu___1981_93281.uvar_subtyping);
        tc_term = (uu___1981_93281.tc_term);
        type_of = (uu___1981_93281.type_of);
        universe_of = (uu___1981_93281.universe_of);
        check_type_of = (uu___1981_93281.check_type_of);
        use_bv_sorts = (uu___1981_93281.use_bv_sorts);
        qtbl_name_and_index = (uu___1981_93281.qtbl_name_and_index);
        normalized_eff_names = (uu___1981_93281.normalized_eff_names);
        fv_delta_depths = (uu___1981_93281.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1981_93281.synth_hook);
        splice = (uu___1981_93281.splice);
        postprocess = (uu___1981_93281.postprocess);
        is_native_tactic = (uu___1981_93281.is_native_tactic);
        identifier_info = (uu___1981_93281.identifier_info);
        tc_hooks = (uu___1981_93281.tc_hooks);
        dsenv = (uu___1981_93281.dsenv);
        nbe = (uu___1981_93281.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____93531 = FStar_Syntax_Free.names t  in
      let uu____93539 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____93531 uu____93539
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____93708 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____93708
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____93736 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____93736
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____93875 =
      match uu____93875 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____93895 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____93895)
       in
    let uu____93903 =
      let uu____93907 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____93907 FStar_List.rev  in
    FStar_All.pipe_right uu____93903 (FStar_String.concat " ")
  
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
                  (let uu____94017 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____94017 with
                   | FStar_Pervasives_Native.Some uu____94025 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____94040 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____94062;
        univ_ineqs = uu____94063; implicits = uu____94064;_} -> true
    | uu____94080 -> false
  
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
          let uu___2025_94162 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2025_94162.deferred);
            univ_ineqs = (uu___2025_94162.univ_ineqs);
            implicits = (uu___2025_94162.implicits)
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
          let uu____94239 = FStar_Options.defensive ()  in
          if uu____94239
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____94250 =
              let uu____94252 =
                let uu____94254 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____94254  in
              Prims.op_Negation uu____94252  in
            (if uu____94250
             then
               let uu____94281 =
                 let uu____94287 =
                   let uu____94289 = FStar_Syntax_Print.term_to_string t  in
                   let uu____94291 =
                     let uu____94293 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____94293
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____94289 uu____94291
                    in
                 (FStar_Errors.Warning_Defensive, uu____94287)  in
               FStar_Errors.log_issue rng uu____94281
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
          let uu____94366 =
            let uu____94368 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____94368  in
          if uu____94366
          then ()
          else
            (let uu____94373 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____94373 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____94525 =
            let uu____94527 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____94527  in
          if uu____94525
          then ()
          else
            (let uu____94532 = bound_vars e  in
             def_check_closed_in rng msg uu____94532 t)
  
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
          let uu___2062_94724 = g  in
          let uu____94733 =
            let uu____94734 =
              let uu____94743 =
                let uu____94750 =
                  let uu____94751 =
                    let uu____94776 =
                      let uu____94791 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____94791]  in
                    (f, uu____94776)  in
                  FStar_Syntax_Syntax.Tm_app uu____94751  in
                FStar_Syntax_Syntax.mk uu____94750  in
              uu____94743 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _94852  -> FStar_TypeChecker_Common.NonTrivial _94852)
              uu____94734
             in
          {
            guard_f = uu____94733;
            deferred = (uu___2062_94724.deferred);
            univ_ineqs = (uu___2062_94724.univ_ineqs);
            implicits = (uu___2062_94724.implicits)
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
          let uu___2069_94906 = g  in
          let uu____94915 =
            let uu____94916 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____94916  in
          {
            guard_f = uu____94915;
            deferred = (uu___2069_94906.deferred);
            univ_ineqs = (uu___2069_94906.univ_ineqs);
            implicits = (uu___2069_94906.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2074_94973 = g  in
          let uu____94982 =
            let uu____94983 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____94983  in
          {
            guard_f = uu____94982;
            deferred = (uu___2074_94973.deferred);
            univ_ineqs = (uu___2074_94973.univ_ineqs);
            implicits = (uu___2074_94973.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2078_94997 = g  in
          let uu____95006 =
            let uu____95007 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____95007  in
          {
            guard_f = uu____95006;
            deferred = (uu___2078_94997.deferred);
            univ_ineqs = (uu___2078_94997.univ_ineqs);
            implicits = (uu___2078_94997.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____95022 ->
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
          let uu____95051 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____95051
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____95074 =
      let uu____95075 = FStar_Syntax_Util.unmeta t  in
      uu____95075.FStar_Syntax_Syntax.n  in
    match uu____95074 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____95090 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____95169 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____95169;
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
                       let uu____95374 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____95374
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2133_95390 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2133_95390.deferred);
              univ_ineqs = (uu___2133_95390.univ_ineqs);
              implicits = (uu___2133_95390.implicits)
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
               let uu____95570 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____95570
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
            let uu___2148_95739 = g  in
            let uu____95748 =
              let uu____95749 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____95749  in
            {
              guard_f = uu____95748;
              deferred = (uu___2148_95739.deferred);
              univ_ineqs = (uu___2148_95739.univ_ineqs);
              implicits = (uu___2148_95739.implicits)
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
              let uu____95955 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____95955 with
              | FStar_Pervasives_Native.Some
                  (uu____96000::(tm,uu____96002)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____96126 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____96164 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____96164;
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
                      let uu___2170_96234 = trivial_guard  in
                      {
                        guard_f = (uu___2170_96234.guard_f);
                        deferred = (uu___2170_96234.deferred);
                        univ_ineqs = (uu___2170_96234.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____96330  -> ());
    push = (fun uu____96386  -> ());
    pop = (fun uu____96389  -> ());
    snapshot =
      (fun uu____96392  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____96411  -> fun uu____96412  -> ());
    encode_sig = (fun uu____96427  -> fun uu____96428  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____96551 =
             let uu____96616 = FStar_Options.peek ()  in (e, g, uu____96616)
              in
           [uu____96551]);
    solve = (fun uu____96806  -> fun uu____96807  -> fun uu____96808  -> ());
    finish = (fun uu____96873  -> ());
    refresh = (fun uu____96875  -> ())
  } 