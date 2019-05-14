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
  fun projectee  -> match projectee with | Beta  -> true | uu____115 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____126 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____137 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____149 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____167 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____178 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____189 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding _0 -> true | uu____202 -> false
  
let (__proj__Eager_unfolding__item___0 : step -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding _0 -> _0 
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____223 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____234 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____246 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____267 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____294 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____321 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____345 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____356 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____367 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____378 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____389 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____400 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____411 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____422 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____433 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____444 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____455 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____466 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____477 -> false
  
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
      | uu____542 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only of Prims.bool 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____574 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____585 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only _0 -> true
    | uu____598 -> false
  
let (__proj__Eager_unfolding_only__item___0 : delta_level -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding_only _0 -> _0 
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____620 -> false
  
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
           (fun uu___0_11837  ->
              match uu___0_11837 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____11840 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____11840  in
                  let uu____11841 =
                    let uu____11842 = FStar_Syntax_Subst.compress y  in
                    uu____11842.FStar_Syntax_Syntax.n  in
                  (match uu____11841 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____11846 =
                         let uu___339_11847 = y1  in
                         let uu____11848 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___339_11847.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___339_11847.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____11848
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____11846
                   | uu____11851 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___345_11865 = env  in
      let uu____11866 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___345_11865.solver);
        range = (uu___345_11865.range);
        curmodule = (uu___345_11865.curmodule);
        gamma = uu____11866;
        gamma_sig = (uu___345_11865.gamma_sig);
        gamma_cache = (uu___345_11865.gamma_cache);
        modules = (uu___345_11865.modules);
        expected_typ = (uu___345_11865.expected_typ);
        sigtab = (uu___345_11865.sigtab);
        attrtab = (uu___345_11865.attrtab);
        is_pattern = (uu___345_11865.is_pattern);
        instantiate_imp = (uu___345_11865.instantiate_imp);
        effects = (uu___345_11865.effects);
        generalize = (uu___345_11865.generalize);
        letrecs = (uu___345_11865.letrecs);
        top_level = (uu___345_11865.top_level);
        check_uvars = (uu___345_11865.check_uvars);
        use_eq = (uu___345_11865.use_eq);
        is_iface = (uu___345_11865.is_iface);
        admit = (uu___345_11865.admit);
        lax = (uu___345_11865.lax);
        lax_universes = (uu___345_11865.lax_universes);
        phase1 = (uu___345_11865.phase1);
        failhard = (uu___345_11865.failhard);
        nosynth = (uu___345_11865.nosynth);
        uvar_subtyping = (uu___345_11865.uvar_subtyping);
        tc_term = (uu___345_11865.tc_term);
        type_of = (uu___345_11865.type_of);
        universe_of = (uu___345_11865.universe_of);
        check_type_of = (uu___345_11865.check_type_of);
        use_bv_sorts = (uu___345_11865.use_bv_sorts);
        qtbl_name_and_index = (uu___345_11865.qtbl_name_and_index);
        normalized_eff_names = (uu___345_11865.normalized_eff_names);
        fv_delta_depths = (uu___345_11865.fv_delta_depths);
        proof_ns = (uu___345_11865.proof_ns);
        synth_hook = (uu___345_11865.synth_hook);
        splice = (uu___345_11865.splice);
        postprocess = (uu___345_11865.postprocess);
        is_native_tactic = (uu___345_11865.is_native_tactic);
        identifier_info = (uu___345_11865.identifier_info);
        tc_hooks = (uu___345_11865.tc_hooks);
        dsenv = (uu___345_11865.dsenv);
        nbe = (uu___345_11865.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____11874  -> fun uu____11875  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___352_11897 = env  in
      {
        solver = (uu___352_11897.solver);
        range = (uu___352_11897.range);
        curmodule = (uu___352_11897.curmodule);
        gamma = (uu___352_11897.gamma);
        gamma_sig = (uu___352_11897.gamma_sig);
        gamma_cache = (uu___352_11897.gamma_cache);
        modules = (uu___352_11897.modules);
        expected_typ = (uu___352_11897.expected_typ);
        sigtab = (uu___352_11897.sigtab);
        attrtab = (uu___352_11897.attrtab);
        is_pattern = (uu___352_11897.is_pattern);
        instantiate_imp = (uu___352_11897.instantiate_imp);
        effects = (uu___352_11897.effects);
        generalize = (uu___352_11897.generalize);
        letrecs = (uu___352_11897.letrecs);
        top_level = (uu___352_11897.top_level);
        check_uvars = (uu___352_11897.check_uvars);
        use_eq = (uu___352_11897.use_eq);
        is_iface = (uu___352_11897.is_iface);
        admit = (uu___352_11897.admit);
        lax = (uu___352_11897.lax);
        lax_universes = (uu___352_11897.lax_universes);
        phase1 = (uu___352_11897.phase1);
        failhard = (uu___352_11897.failhard);
        nosynth = (uu___352_11897.nosynth);
        uvar_subtyping = (uu___352_11897.uvar_subtyping);
        tc_term = (uu___352_11897.tc_term);
        type_of = (uu___352_11897.type_of);
        universe_of = (uu___352_11897.universe_of);
        check_type_of = (uu___352_11897.check_type_of);
        use_bv_sorts = (uu___352_11897.use_bv_sorts);
        qtbl_name_and_index = (uu___352_11897.qtbl_name_and_index);
        normalized_eff_names = (uu___352_11897.normalized_eff_names);
        fv_delta_depths = (uu___352_11897.fv_delta_depths);
        proof_ns = (uu___352_11897.proof_ns);
        synth_hook = (uu___352_11897.synth_hook);
        splice = (uu___352_11897.splice);
        postprocess = (uu___352_11897.postprocess);
        is_native_tactic = (uu___352_11897.is_native_tactic);
        identifier_info = (uu___352_11897.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___352_11897.dsenv);
        nbe = (uu___352_11897.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___356_11909 = e  in
      let uu____11910 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___356_11909.solver);
        range = (uu___356_11909.range);
        curmodule = (uu___356_11909.curmodule);
        gamma = (uu___356_11909.gamma);
        gamma_sig = (uu___356_11909.gamma_sig);
        gamma_cache = (uu___356_11909.gamma_cache);
        modules = (uu___356_11909.modules);
        expected_typ = (uu___356_11909.expected_typ);
        sigtab = (uu___356_11909.sigtab);
        attrtab = (uu___356_11909.attrtab);
        is_pattern = (uu___356_11909.is_pattern);
        instantiate_imp = (uu___356_11909.instantiate_imp);
        effects = (uu___356_11909.effects);
        generalize = (uu___356_11909.generalize);
        letrecs = (uu___356_11909.letrecs);
        top_level = (uu___356_11909.top_level);
        check_uvars = (uu___356_11909.check_uvars);
        use_eq = (uu___356_11909.use_eq);
        is_iface = (uu___356_11909.is_iface);
        admit = (uu___356_11909.admit);
        lax = (uu___356_11909.lax);
        lax_universes = (uu___356_11909.lax_universes);
        phase1 = (uu___356_11909.phase1);
        failhard = (uu___356_11909.failhard);
        nosynth = (uu___356_11909.nosynth);
        uvar_subtyping = (uu___356_11909.uvar_subtyping);
        tc_term = (uu___356_11909.tc_term);
        type_of = (uu___356_11909.type_of);
        universe_of = (uu___356_11909.universe_of);
        check_type_of = (uu___356_11909.check_type_of);
        use_bv_sorts = (uu___356_11909.use_bv_sorts);
        qtbl_name_and_index = (uu___356_11909.qtbl_name_and_index);
        normalized_eff_names = (uu___356_11909.normalized_eff_names);
        fv_delta_depths = (uu___356_11909.fv_delta_depths);
        proof_ns = (uu___356_11909.proof_ns);
        synth_hook = (uu___356_11909.synth_hook);
        splice = (uu___356_11909.splice);
        postprocess = (uu___356_11909.postprocess);
        is_native_tactic = (uu___356_11909.is_native_tactic);
        identifier_info = (uu___356_11909.identifier_info);
        tc_hooks = (uu___356_11909.tc_hooks);
        dsenv = uu____11910;
        nbe = (uu___356_11909.nbe)
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
      | (NoDelta ,uu____11939) -> true
      | (Eager_unfolding_only
         uu____11941,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold
         uu____11944,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____11946,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____11949 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____11963 . unit -> 'Auu____11963 FStar_Util.smap =
  fun uu____11970  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____11976 . unit -> 'Auu____11976 FStar_Util.smap =
  fun uu____11983  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____12121 = new_gamma_cache ()  in
                  let uu____12124 = new_sigtab ()  in
                  let uu____12127 = new_sigtab ()  in
                  let uu____12134 =
                    let uu____12149 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12149, FStar_Pervasives_Native.None)  in
                  let uu____12170 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12174 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12178 = FStar_Options.using_facts_from ()  in
                  let uu____12179 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12182 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12121;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12124;
                    attrtab = uu____12127;
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
                    qtbl_name_and_index = uu____12134;
                    normalized_eff_names = uu____12170;
                    fv_delta_depths = uu____12174;
                    proof_ns = uu____12178;
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
                    is_native_tactic = (fun uu____12244  -> false);
                    identifier_info = uu____12179;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12182;
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
  fun uu____12323  ->
    let uu____12324 = FStar_ST.op_Bang query_indices  in
    match uu____12324 with
    | [] -> failwith "Empty query indices!"
    | uu____12379 ->
        let uu____12389 =
          let uu____12399 =
            let uu____12407 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12407  in
          let uu____12461 = FStar_ST.op_Bang query_indices  in uu____12399 ::
            uu____12461
           in
        FStar_ST.op_Colon_Equals query_indices uu____12389
  
let (pop_query_indices : unit -> unit) =
  fun uu____12557  ->
    let uu____12558 = FStar_ST.op_Bang query_indices  in
    match uu____12558 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____12685  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____12722  ->
    match uu____12722 with
    | (l,n1) ->
        let uu____12732 = FStar_ST.op_Bang query_indices  in
        (match uu____12732 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____12854 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____12877  ->
    let uu____12878 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____12878
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____12946 =
       let uu____12949 = FStar_ST.op_Bang stack  in env :: uu____12949  in
     FStar_ST.op_Colon_Equals stack uu____12946);
    (let uu___425_12998 = env  in
     let uu____12999 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13002 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13005 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13012 =
       let uu____13027 =
         let uu____13031 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13031  in
       let uu____13063 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13027, uu____13063)  in
     let uu____13112 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13115 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13118 =
       let uu____13121 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13121  in
     {
       solver = (uu___425_12998.solver);
       range = (uu___425_12998.range);
       curmodule = (uu___425_12998.curmodule);
       gamma = (uu___425_12998.gamma);
       gamma_sig = (uu___425_12998.gamma_sig);
       gamma_cache = uu____12999;
       modules = (uu___425_12998.modules);
       expected_typ = (uu___425_12998.expected_typ);
       sigtab = uu____13002;
       attrtab = uu____13005;
       is_pattern = (uu___425_12998.is_pattern);
       instantiate_imp = (uu___425_12998.instantiate_imp);
       effects = (uu___425_12998.effects);
       generalize = (uu___425_12998.generalize);
       letrecs = (uu___425_12998.letrecs);
       top_level = (uu___425_12998.top_level);
       check_uvars = (uu___425_12998.check_uvars);
       use_eq = (uu___425_12998.use_eq);
       is_iface = (uu___425_12998.is_iface);
       admit = (uu___425_12998.admit);
       lax = (uu___425_12998.lax);
       lax_universes = (uu___425_12998.lax_universes);
       phase1 = (uu___425_12998.phase1);
       failhard = (uu___425_12998.failhard);
       nosynth = (uu___425_12998.nosynth);
       uvar_subtyping = (uu___425_12998.uvar_subtyping);
       tc_term = (uu___425_12998.tc_term);
       type_of = (uu___425_12998.type_of);
       universe_of = (uu___425_12998.universe_of);
       check_type_of = (uu___425_12998.check_type_of);
       use_bv_sorts = (uu___425_12998.use_bv_sorts);
       qtbl_name_and_index = uu____13012;
       normalized_eff_names = uu____13112;
       fv_delta_depths = uu____13115;
       proof_ns = (uu___425_12998.proof_ns);
       synth_hook = (uu___425_12998.synth_hook);
       splice = (uu___425_12998.splice);
       postprocess = (uu___425_12998.postprocess);
       is_native_tactic = (uu___425_12998.is_native_tactic);
       identifier_info = uu____13118;
       tc_hooks = (uu___425_12998.tc_hooks);
       dsenv = (uu___425_12998.dsenv);
       nbe = (uu___425_12998.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13146  ->
    let uu____13147 = FStar_ST.op_Bang stack  in
    match uu____13147 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13201 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13291  ->
           let uu____13292 = snapshot_stack env  in
           match uu____13292 with
           | (stack_depth,env1) ->
               let uu____13326 = snapshot_query_indices ()  in
               (match uu____13326 with
                | (query_indices_depth,()) ->
                    let uu____13359 = (env1.solver).snapshot msg  in
                    (match uu____13359 with
                     | (solver_depth,()) ->
                         let uu____13416 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13416 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___450_13483 = env1  in
                                 {
                                   solver = (uu___450_13483.solver);
                                   range = (uu___450_13483.range);
                                   curmodule = (uu___450_13483.curmodule);
                                   gamma = (uu___450_13483.gamma);
                                   gamma_sig = (uu___450_13483.gamma_sig);
                                   gamma_cache = (uu___450_13483.gamma_cache);
                                   modules = (uu___450_13483.modules);
                                   expected_typ =
                                     (uu___450_13483.expected_typ);
                                   sigtab = (uu___450_13483.sigtab);
                                   attrtab = (uu___450_13483.attrtab);
                                   is_pattern = (uu___450_13483.is_pattern);
                                   instantiate_imp =
                                     (uu___450_13483.instantiate_imp);
                                   effects = (uu___450_13483.effects);
                                   generalize = (uu___450_13483.generalize);
                                   letrecs = (uu___450_13483.letrecs);
                                   top_level = (uu___450_13483.top_level);
                                   check_uvars = (uu___450_13483.check_uvars);
                                   use_eq = (uu___450_13483.use_eq);
                                   is_iface = (uu___450_13483.is_iface);
                                   admit = (uu___450_13483.admit);
                                   lax = (uu___450_13483.lax);
                                   lax_universes =
                                     (uu___450_13483.lax_universes);
                                   phase1 = (uu___450_13483.phase1);
                                   failhard = (uu___450_13483.failhard);
                                   nosynth = (uu___450_13483.nosynth);
                                   uvar_subtyping =
                                     (uu___450_13483.uvar_subtyping);
                                   tc_term = (uu___450_13483.tc_term);
                                   type_of = (uu___450_13483.type_of);
                                   universe_of = (uu___450_13483.universe_of);
                                   check_type_of =
                                     (uu___450_13483.check_type_of);
                                   use_bv_sorts =
                                     (uu___450_13483.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___450_13483.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___450_13483.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___450_13483.fv_delta_depths);
                                   proof_ns = (uu___450_13483.proof_ns);
                                   synth_hook = (uu___450_13483.synth_hook);
                                   splice = (uu___450_13483.splice);
                                   postprocess = (uu___450_13483.postprocess);
                                   is_native_tactic =
                                     (uu___450_13483.is_native_tactic);
                                   identifier_info =
                                     (uu___450_13483.identifier_info);
                                   tc_hooks = (uu___450_13483.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___450_13483.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13517  ->
             let uu____13518 =
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
             match uu____13518 with
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
                             ((let uu____13698 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13698
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13714 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13714
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____13746,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____13788 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____13818  ->
                  match uu____13818 with
                  | (m,uu____13826) -> FStar_Ident.lid_equals l m))
           in
        (match uu____13788 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___495_13841 = env  in
               {
                 solver = (uu___495_13841.solver);
                 range = (uu___495_13841.range);
                 curmodule = (uu___495_13841.curmodule);
                 gamma = (uu___495_13841.gamma);
                 gamma_sig = (uu___495_13841.gamma_sig);
                 gamma_cache = (uu___495_13841.gamma_cache);
                 modules = (uu___495_13841.modules);
                 expected_typ = (uu___495_13841.expected_typ);
                 sigtab = (uu___495_13841.sigtab);
                 attrtab = (uu___495_13841.attrtab);
                 is_pattern = (uu___495_13841.is_pattern);
                 instantiate_imp = (uu___495_13841.instantiate_imp);
                 effects = (uu___495_13841.effects);
                 generalize = (uu___495_13841.generalize);
                 letrecs = (uu___495_13841.letrecs);
                 top_level = (uu___495_13841.top_level);
                 check_uvars = (uu___495_13841.check_uvars);
                 use_eq = (uu___495_13841.use_eq);
                 is_iface = (uu___495_13841.is_iface);
                 admit = (uu___495_13841.admit);
                 lax = (uu___495_13841.lax);
                 lax_universes = (uu___495_13841.lax_universes);
                 phase1 = (uu___495_13841.phase1);
                 failhard = (uu___495_13841.failhard);
                 nosynth = (uu___495_13841.nosynth);
                 uvar_subtyping = (uu___495_13841.uvar_subtyping);
                 tc_term = (uu___495_13841.tc_term);
                 type_of = (uu___495_13841.type_of);
                 universe_of = (uu___495_13841.universe_of);
                 check_type_of = (uu___495_13841.check_type_of);
                 use_bv_sorts = (uu___495_13841.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___495_13841.normalized_eff_names);
                 fv_delta_depths = (uu___495_13841.fv_delta_depths);
                 proof_ns = (uu___495_13841.proof_ns);
                 synth_hook = (uu___495_13841.synth_hook);
                 splice = (uu___495_13841.splice);
                 postprocess = (uu___495_13841.postprocess);
                 is_native_tactic = (uu___495_13841.is_native_tactic);
                 identifier_info = (uu___495_13841.identifier_info);
                 tc_hooks = (uu___495_13841.tc_hooks);
                 dsenv = (uu___495_13841.dsenv);
                 nbe = (uu___495_13841.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____13858,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___504_13874 = env  in
               {
                 solver = (uu___504_13874.solver);
                 range = (uu___504_13874.range);
                 curmodule = (uu___504_13874.curmodule);
                 gamma = (uu___504_13874.gamma);
                 gamma_sig = (uu___504_13874.gamma_sig);
                 gamma_cache = (uu___504_13874.gamma_cache);
                 modules = (uu___504_13874.modules);
                 expected_typ = (uu___504_13874.expected_typ);
                 sigtab = (uu___504_13874.sigtab);
                 attrtab = (uu___504_13874.attrtab);
                 is_pattern = (uu___504_13874.is_pattern);
                 instantiate_imp = (uu___504_13874.instantiate_imp);
                 effects = (uu___504_13874.effects);
                 generalize = (uu___504_13874.generalize);
                 letrecs = (uu___504_13874.letrecs);
                 top_level = (uu___504_13874.top_level);
                 check_uvars = (uu___504_13874.check_uvars);
                 use_eq = (uu___504_13874.use_eq);
                 is_iface = (uu___504_13874.is_iface);
                 admit = (uu___504_13874.admit);
                 lax = (uu___504_13874.lax);
                 lax_universes = (uu___504_13874.lax_universes);
                 phase1 = (uu___504_13874.phase1);
                 failhard = (uu___504_13874.failhard);
                 nosynth = (uu___504_13874.nosynth);
                 uvar_subtyping = (uu___504_13874.uvar_subtyping);
                 tc_term = (uu___504_13874.tc_term);
                 type_of = (uu___504_13874.type_of);
                 universe_of = (uu___504_13874.universe_of);
                 check_type_of = (uu___504_13874.check_type_of);
                 use_bv_sorts = (uu___504_13874.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___504_13874.normalized_eff_names);
                 fv_delta_depths = (uu___504_13874.fv_delta_depths);
                 proof_ns = (uu___504_13874.proof_ns);
                 synth_hook = (uu___504_13874.synth_hook);
                 splice = (uu___504_13874.splice);
                 postprocess = (uu___504_13874.postprocess);
                 is_native_tactic = (uu___504_13874.is_native_tactic);
                 identifier_info = (uu___504_13874.identifier_info);
                 tc_hooks = (uu___504_13874.tc_hooks);
                 dsenv = (uu___504_13874.dsenv);
                 nbe = (uu___504_13874.nbe)
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
        (let uu___511_13917 = e  in
         {
           solver = (uu___511_13917.solver);
           range = r;
           curmodule = (uu___511_13917.curmodule);
           gamma = (uu___511_13917.gamma);
           gamma_sig = (uu___511_13917.gamma_sig);
           gamma_cache = (uu___511_13917.gamma_cache);
           modules = (uu___511_13917.modules);
           expected_typ = (uu___511_13917.expected_typ);
           sigtab = (uu___511_13917.sigtab);
           attrtab = (uu___511_13917.attrtab);
           is_pattern = (uu___511_13917.is_pattern);
           instantiate_imp = (uu___511_13917.instantiate_imp);
           effects = (uu___511_13917.effects);
           generalize = (uu___511_13917.generalize);
           letrecs = (uu___511_13917.letrecs);
           top_level = (uu___511_13917.top_level);
           check_uvars = (uu___511_13917.check_uvars);
           use_eq = (uu___511_13917.use_eq);
           is_iface = (uu___511_13917.is_iface);
           admit = (uu___511_13917.admit);
           lax = (uu___511_13917.lax);
           lax_universes = (uu___511_13917.lax_universes);
           phase1 = (uu___511_13917.phase1);
           failhard = (uu___511_13917.failhard);
           nosynth = (uu___511_13917.nosynth);
           uvar_subtyping = (uu___511_13917.uvar_subtyping);
           tc_term = (uu___511_13917.tc_term);
           type_of = (uu___511_13917.type_of);
           universe_of = (uu___511_13917.universe_of);
           check_type_of = (uu___511_13917.check_type_of);
           use_bv_sorts = (uu___511_13917.use_bv_sorts);
           qtbl_name_and_index = (uu___511_13917.qtbl_name_and_index);
           normalized_eff_names = (uu___511_13917.normalized_eff_names);
           fv_delta_depths = (uu___511_13917.fv_delta_depths);
           proof_ns = (uu___511_13917.proof_ns);
           synth_hook = (uu___511_13917.synth_hook);
           splice = (uu___511_13917.splice);
           postprocess = (uu___511_13917.postprocess);
           is_native_tactic = (uu___511_13917.is_native_tactic);
           identifier_info = (uu___511_13917.identifier_info);
           tc_hooks = (uu___511_13917.tc_hooks);
           dsenv = (uu___511_13917.dsenv);
           nbe = (uu___511_13917.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____13937 =
        let uu____13938 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____13938 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____13937
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____13993 =
          let uu____13994 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____13994 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____13993
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14049 =
          let uu____14050 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14050 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14049
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14105 =
        let uu____14106 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14106 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14105
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___528_14170 = env  in
      {
        solver = (uu___528_14170.solver);
        range = (uu___528_14170.range);
        curmodule = lid;
        gamma = (uu___528_14170.gamma);
        gamma_sig = (uu___528_14170.gamma_sig);
        gamma_cache = (uu___528_14170.gamma_cache);
        modules = (uu___528_14170.modules);
        expected_typ = (uu___528_14170.expected_typ);
        sigtab = (uu___528_14170.sigtab);
        attrtab = (uu___528_14170.attrtab);
        is_pattern = (uu___528_14170.is_pattern);
        instantiate_imp = (uu___528_14170.instantiate_imp);
        effects = (uu___528_14170.effects);
        generalize = (uu___528_14170.generalize);
        letrecs = (uu___528_14170.letrecs);
        top_level = (uu___528_14170.top_level);
        check_uvars = (uu___528_14170.check_uvars);
        use_eq = (uu___528_14170.use_eq);
        is_iface = (uu___528_14170.is_iface);
        admit = (uu___528_14170.admit);
        lax = (uu___528_14170.lax);
        lax_universes = (uu___528_14170.lax_universes);
        phase1 = (uu___528_14170.phase1);
        failhard = (uu___528_14170.failhard);
        nosynth = (uu___528_14170.nosynth);
        uvar_subtyping = (uu___528_14170.uvar_subtyping);
        tc_term = (uu___528_14170.tc_term);
        type_of = (uu___528_14170.type_of);
        universe_of = (uu___528_14170.universe_of);
        check_type_of = (uu___528_14170.check_type_of);
        use_bv_sorts = (uu___528_14170.use_bv_sorts);
        qtbl_name_and_index = (uu___528_14170.qtbl_name_and_index);
        normalized_eff_names = (uu___528_14170.normalized_eff_names);
        fv_delta_depths = (uu___528_14170.fv_delta_depths);
        proof_ns = (uu___528_14170.proof_ns);
        synth_hook = (uu___528_14170.synth_hook);
        splice = (uu___528_14170.splice);
        postprocess = (uu___528_14170.postprocess);
        is_native_tactic = (uu___528_14170.is_native_tactic);
        identifier_info = (uu___528_14170.identifier_info);
        tc_hooks = (uu___528_14170.tc_hooks);
        dsenv = (uu___528_14170.dsenv);
        nbe = (uu___528_14170.nbe)
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
      let uu____14201 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14201
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14214 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14214)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14229 =
      let uu____14231 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14231  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14229)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14240  ->
    let uu____14241 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14241
  
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
      | ((formals,t),uu____14341) ->
          let vs = mk_univ_subst formals us  in
          let uu____14365 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14365)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14382  ->
    match uu___1_14382 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14408  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14428 = inst_tscheme t  in
      match uu____14428 with
      | (us,t1) ->
          let uu____14439 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14439)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14460  ->
          match uu____14460 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____14482 =
                         let uu____14484 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____14488 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____14492 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____14494 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____14484 uu____14488 uu____14492 uu____14494
                          in
                       failwith uu____14482)
                    else ();
                    (let uu____14499 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____14499))
               | uu____14508 ->
                   let uu____14509 =
                     let uu____14511 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____14511
                      in
                   failwith uu____14509)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14523 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14534 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14545 -> false
  
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
             | ([],uu____14593) -> Maybe
             | (uu____14600,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14620 -> No  in
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
          let uu____14714 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14714 with
          | FStar_Pervasives_Native.None  ->
              let uu____14737 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_14781  ->
                     match uu___2_14781 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____14820 = FStar_Ident.lid_equals lid l  in
                         if uu____14820
                         then
                           let uu____14843 =
                             let uu____14862 =
                               let uu____14877 = inst_tscheme t  in
                               FStar_Util.Inl uu____14877  in
                             let uu____14892 = FStar_Ident.range_of_lid l  in
                             (uu____14862, uu____14892)  in
                           FStar_Pervasives_Native.Some uu____14843
                         else FStar_Pervasives_Native.None
                     | uu____14945 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____14737
                (fun uu____14983  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_14992  ->
                        match uu___3_14992 with
                        | (uu____14995,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____14997);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____14998;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____14999;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15000;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15001;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15021 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15021
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
                                  uu____15073 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15080 -> cache t  in
                            let uu____15081 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15081 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15087 =
                                   let uu____15088 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15088)
                                    in
                                 maybe_cache uu____15087)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15159 = find_in_sigtab env lid  in
         match uu____15159 with
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
      let uu____15240 = lookup_qname env lid  in
      match uu____15240 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15261,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15375 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15375 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15420 =
          let uu____15423 = lookup_attr env1 attr  in se1 :: uu____15423  in
        FStar_Util.smap_add (attrtab env1) attr uu____15420  in
      FStar_List.iter
        (fun attr  ->
           let uu____15433 =
             let uu____15434 = FStar_Syntax_Subst.compress attr  in
             uu____15434.FStar_Syntax_Syntax.n  in
           match uu____15433 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15438 =
                 let uu____15440 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15440.FStar_Ident.str  in
               add_one1 env se uu____15438
           | uu____15441 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15464) ->
          add_sigelts env ses
      | uu____15473 ->
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
            | uu____15488 -> ()))

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
        (fun uu___4_15520  ->
           match uu___4_15520 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15538 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____15600,lb::[]),uu____15602) ->
            let uu____15611 =
              let uu____15620 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15629 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15620, uu____15629)  in
            FStar_Pervasives_Native.Some uu____15611
        | FStar_Syntax_Syntax.Sig_let ((uu____15642,lbs),uu____15644) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15676 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15689 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15689
                     then
                       let uu____15702 =
                         let uu____15711 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____15720 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15711, uu____15720)  in
                       FStar_Pervasives_Native.Some uu____15702
                     else FStar_Pervasives_Native.None)
        | uu____15743 -> FStar_Pervasives_Native.None
  
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
          let uu____15803 =
            let uu____15812 =
              let uu____15817 =
                let uu____15818 =
                  let uu____15821 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____15821
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____15818)  in
              inst_tscheme1 uu____15817  in
            (uu____15812, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15803
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____15843,uu____15844) ->
          let uu____15849 =
            let uu____15858 =
              let uu____15863 =
                let uu____15864 =
                  let uu____15867 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____15867  in
                (us, uu____15864)  in
              inst_tscheme1 uu____15863  in
            (uu____15858, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15849
      | uu____15886 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____15975 =
          match uu____15975 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16071,uvs,t,uu____16074,uu____16075,uu____16076);
                      FStar_Syntax_Syntax.sigrng = uu____16077;
                      FStar_Syntax_Syntax.sigquals = uu____16078;
                      FStar_Syntax_Syntax.sigmeta = uu____16079;
                      FStar_Syntax_Syntax.sigattrs = uu____16080;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16103 =
                     let uu____16112 = inst_tscheme1 (uvs, t)  in
                     (uu____16112, rng)  in
                   FStar_Pervasives_Native.Some uu____16103
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16136;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16138;
                      FStar_Syntax_Syntax.sigattrs = uu____16139;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16156 =
                     let uu____16158 = in_cur_mod env l  in uu____16158 = Yes
                      in
                   if uu____16156
                   then
                     let uu____16170 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16170
                      then
                        let uu____16186 =
                          let uu____16195 = inst_tscheme1 (uvs, t)  in
                          (uu____16195, rng)  in
                        FStar_Pervasives_Native.Some uu____16186
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16228 =
                        let uu____16237 = inst_tscheme1 (uvs, t)  in
                        (uu____16237, rng)  in
                      FStar_Pervasives_Native.Some uu____16228)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16262,uu____16263);
                      FStar_Syntax_Syntax.sigrng = uu____16264;
                      FStar_Syntax_Syntax.sigquals = uu____16265;
                      FStar_Syntax_Syntax.sigmeta = uu____16266;
                      FStar_Syntax_Syntax.sigattrs = uu____16267;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16308 =
                          let uu____16317 = inst_tscheme1 (uvs, k)  in
                          (uu____16317, rng)  in
                        FStar_Pervasives_Native.Some uu____16308
                    | uu____16338 ->
                        let uu____16339 =
                          let uu____16348 =
                            let uu____16353 =
                              let uu____16354 =
                                let uu____16357 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16357
                                 in
                              (uvs, uu____16354)  in
                            inst_tscheme1 uu____16353  in
                          (uu____16348, rng)  in
                        FStar_Pervasives_Native.Some uu____16339)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16380,uu____16381);
                      FStar_Syntax_Syntax.sigrng = uu____16382;
                      FStar_Syntax_Syntax.sigquals = uu____16383;
                      FStar_Syntax_Syntax.sigmeta = uu____16384;
                      FStar_Syntax_Syntax.sigattrs = uu____16385;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16427 =
                          let uu____16436 = inst_tscheme_with (uvs, k) us  in
                          (uu____16436, rng)  in
                        FStar_Pervasives_Native.Some uu____16427
                    | uu____16457 ->
                        let uu____16458 =
                          let uu____16467 =
                            let uu____16472 =
                              let uu____16473 =
                                let uu____16476 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16476
                                 in
                              (uvs, uu____16473)  in
                            inst_tscheme_with uu____16472 us  in
                          (uu____16467, rng)  in
                        FStar_Pervasives_Native.Some uu____16458)
               | FStar_Util.Inr se ->
                   let uu____16512 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16533;
                          FStar_Syntax_Syntax.sigrng = uu____16534;
                          FStar_Syntax_Syntax.sigquals = uu____16535;
                          FStar_Syntax_Syntax.sigmeta = uu____16536;
                          FStar_Syntax_Syntax.sigattrs = uu____16537;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16552 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____16512
                     (FStar_Util.map_option
                        (fun uu____16600  ->
                           match uu____16600 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16631 =
          let uu____16642 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16642 mapper  in
        match uu____16631 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____16716 =
              let uu____16727 =
                let uu____16734 =
                  let uu___855_16737 = t  in
                  let uu____16738 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_16737.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____16738;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_16737.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____16734)  in
              (uu____16727, r)  in
            FStar_Pervasives_Native.Some uu____16716
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16787 = lookup_qname env l  in
      match uu____16787 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____16808 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____16862 = try_lookup_bv env bv  in
      match uu____16862 with
      | FStar_Pervasives_Native.None  ->
          let uu____16877 = variable_not_found bv  in
          FStar_Errors.raise_error uu____16877 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____16893 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____16894 =
            let uu____16895 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____16895  in
          (uu____16893, uu____16894)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____16917 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____16917 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____16983 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____16983  in
          let uu____16984 =
            let uu____16993 =
              let uu____16998 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____16998)  in
            (uu____16993, r1)  in
          FStar_Pervasives_Native.Some uu____16984
  
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
        let uu____17033 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17033 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17066,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17091 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17091  in
            let uu____17092 =
              let uu____17097 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17097, r1)  in
            FStar_Pervasives_Native.Some uu____17092
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17121 = try_lookup_lid env l  in
      match uu____17121 with
      | FStar_Pervasives_Native.None  ->
          let uu____17148 = name_not_found l  in
          let uu____17154 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17148 uu____17154
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17197  ->
              match uu___5_17197 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17201 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17222 = lookup_qname env lid  in
      match uu____17222 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17231,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17234;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17236;
              FStar_Syntax_Syntax.sigattrs = uu____17237;_},FStar_Pervasives_Native.None
            ),uu____17238)
          ->
          let uu____17287 =
            let uu____17294 =
              let uu____17295 =
                let uu____17298 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17298 t  in
              (uvs, uu____17295)  in
            (uu____17294, q)  in
          FStar_Pervasives_Native.Some uu____17287
      | uu____17311 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17333 = lookup_qname env lid  in
      match uu____17333 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17338,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17341;
              FStar_Syntax_Syntax.sigquals = uu____17342;
              FStar_Syntax_Syntax.sigmeta = uu____17343;
              FStar_Syntax_Syntax.sigattrs = uu____17344;_},FStar_Pervasives_Native.None
            ),uu____17345)
          ->
          let uu____17394 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17394 (uvs, t)
      | uu____17399 ->
          let uu____17400 = name_not_found lid  in
          let uu____17406 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17400 uu____17406
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17426 = lookup_qname env lid  in
      match uu____17426 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17431,uvs,t,uu____17434,uu____17435,uu____17436);
              FStar_Syntax_Syntax.sigrng = uu____17437;
              FStar_Syntax_Syntax.sigquals = uu____17438;
              FStar_Syntax_Syntax.sigmeta = uu____17439;
              FStar_Syntax_Syntax.sigattrs = uu____17440;_},FStar_Pervasives_Native.None
            ),uu____17441)
          ->
          let uu____17496 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17496 (uvs, t)
      | uu____17501 ->
          let uu____17502 = name_not_found lid  in
          let uu____17508 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17502 uu____17508
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17531 = lookup_qname env lid  in
      match uu____17531 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17539,uu____17540,uu____17541,uu____17542,uu____17543,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17545;
              FStar_Syntax_Syntax.sigquals = uu____17546;
              FStar_Syntax_Syntax.sigmeta = uu____17547;
              FStar_Syntax_Syntax.sigattrs = uu____17548;_},uu____17549),uu____17550)
          -> (true, dcs)
      | uu____17613 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17629 = lookup_qname env lid  in
      match uu____17629 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17630,uu____17631,uu____17632,l,uu____17634,uu____17635);
              FStar_Syntax_Syntax.sigrng = uu____17636;
              FStar_Syntax_Syntax.sigquals = uu____17637;
              FStar_Syntax_Syntax.sigmeta = uu____17638;
              FStar_Syntax_Syntax.sigattrs = uu____17639;_},uu____17640),uu____17641)
          -> l
      | uu____17698 ->
          let uu____17699 =
            let uu____17701 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____17701  in
          failwith uu____17699
  
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
                    (fun uu___6_17773  ->
                       match uu___6_17773 with
                       | Eager_unfolding_only (true ) ->
                           FStar_All.pipe_right attrs
                             (FStar_Util.for_some
                                (fun at  ->
                                   FStar_Syntax_Util.is_fvar
                                     FStar_Parser_Const.unfold_for_smt_attr
                                     at))
                       | uu____17781 -> false)))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____17794)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____17851) when
                   (visible se.FStar_Syntax_Syntax.sigquals
                      se.FStar_Syntax_Syntax.sigattrs)
                     && ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____17875 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____17875
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____17910 -> FStar_Pervasives_Native.None)
          | uu____17919 -> FStar_Pervasives_Native.None
  
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
        let uu____17981 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____17981
  
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
        let uu____18014 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18014
  
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
             (FStar_Util.Inl uu____18066,uu____18067) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18116),uu____18117) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18166 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18184 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18194 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18211 ->
                  let uu____18218 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18218
              | FStar_Syntax_Syntax.Sig_let ((uu____18219,lbs),uu____18221)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18237 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18237
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18244 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18252 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18253 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18260 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18261 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18262 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18263 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18276 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18294 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18294
           (fun d_opt  ->
              let uu____18307 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18307
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18317 =
                   let uu____18320 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18320  in
                 match uu____18317 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18321 =
                       let uu____18323 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18323
                        in
                     failwith uu____18321
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18328 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18328
                       then
                         let uu____18331 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18333 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18335 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18331 uu____18333 uu____18335
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
        (FStar_Util.Inr (se,uu____18360),uu____18361) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18410 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18432),uu____18433) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18482 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18504 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18504
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____18527 = lookup_attrs_of_lid env fv_lid1  in
        match uu____18527 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18551 =
                      let uu____18552 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18552.FStar_Syntax_Syntax.n  in
                    match uu____18551 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____18557 -> false))
  
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
      let uu____18591 = lookup_qname env ftv  in
      match uu____18591 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18595) ->
          let uu____18640 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____18640 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____18661,t),r) ->
               let uu____18676 =
                 let uu____18677 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____18677 t  in
               FStar_Pervasives_Native.Some uu____18676)
      | uu____18678 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____18690 = try_lookup_effect_lid env ftv  in
      match uu____18690 with
      | FStar_Pervasives_Native.None  ->
          let uu____18693 = name_not_found ftv  in
          let uu____18699 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____18693 uu____18699
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
        let uu____18723 = lookup_qname env lid0  in
        match uu____18723 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____18734);
                FStar_Syntax_Syntax.sigrng = uu____18735;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____18737;
                FStar_Syntax_Syntax.sigattrs = uu____18738;_},FStar_Pervasives_Native.None
              ),uu____18739)
            ->
            let lid1 =
              let uu____18793 =
                let uu____18794 = FStar_Ident.range_of_lid lid  in
                let uu____18795 =
                  let uu____18796 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____18796  in
                FStar_Range.set_use_range uu____18794 uu____18795  in
              FStar_Ident.set_lid_range lid uu____18793  in
            let uu____18797 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___7_18803  ->
                      match uu___7_18803 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____18806 -> false))
               in
            if uu____18797
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____18825 =
                      let uu____18827 =
                        let uu____18829 = get_range env  in
                        FStar_Range.string_of_range uu____18829  in
                      let uu____18830 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____18832 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____18827 uu____18830 uu____18832
                       in
                    failwith uu____18825)
                  in
               match (binders, univs1) with
               | ([],uu____18853) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____18879,uu____18880::uu____18881::uu____18882) ->
                   let uu____18903 =
                     let uu____18905 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____18907 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____18905 uu____18907
                      in
                   failwith uu____18903
               | uu____18918 ->
                   let uu____18933 =
                     let uu____18938 =
                       let uu____18939 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____18939)  in
                     inst_tscheme_with uu____18938 insts  in
                   (match uu____18933 with
                    | (uu____18952,t) ->
                        let t1 =
                          let uu____18955 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____18955 t  in
                        let uu____18956 =
                          let uu____18957 = FStar_Syntax_Subst.compress t1
                             in
                          uu____18957.FStar_Syntax_Syntax.n  in
                        (match uu____18956 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____18992 -> failwith "Impossible")))
        | uu____19000 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19024 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19024 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19037,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19044 = find1 l2  in
            (match uu____19044 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19051 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19051 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19055 = find1 l  in
            (match uu____19055 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19060 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19060
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19075 = lookup_qname env l1  in
      match uu____19075 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19078;
              FStar_Syntax_Syntax.sigrng = uu____19079;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19081;
              FStar_Syntax_Syntax.sigattrs = uu____19082;_},uu____19083),uu____19084)
          -> q
      | uu____19135 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19159 =
          let uu____19160 =
            let uu____19162 = FStar_Util.string_of_int i  in
            let uu____19164 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19162 uu____19164
             in
          failwith uu____19160  in
        let uu____19167 = lookup_datacon env lid  in
        match uu____19167 with
        | (uu____19172,t) ->
            let uu____19174 =
              let uu____19175 = FStar_Syntax_Subst.compress t  in
              uu____19175.FStar_Syntax_Syntax.n  in
            (match uu____19174 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19179) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19223 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19223
                      FStar_Pervasives_Native.fst)
             | uu____19234 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19248 = lookup_qname env l  in
      match uu____19248 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19250,uu____19251,uu____19252);
              FStar_Syntax_Syntax.sigrng = uu____19253;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19255;
              FStar_Syntax_Syntax.sigattrs = uu____19256;_},uu____19257),uu____19258)
          ->
          FStar_Util.for_some
            (fun uu___8_19311  ->
               match uu___8_19311 with
               | FStar_Syntax_Syntax.Projector uu____19313 -> true
               | uu____19319 -> false) quals
      | uu____19321 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19335 = lookup_qname env lid  in
      match uu____19335 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19337,uu____19338,uu____19339,uu____19340,uu____19341,uu____19342);
              FStar_Syntax_Syntax.sigrng = uu____19343;
              FStar_Syntax_Syntax.sigquals = uu____19344;
              FStar_Syntax_Syntax.sigmeta = uu____19345;
              FStar_Syntax_Syntax.sigattrs = uu____19346;_},uu____19347),uu____19348)
          -> true
      | uu____19406 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19420 = lookup_qname env lid  in
      match uu____19420 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19422,uu____19423,uu____19424,uu____19425,uu____19426,uu____19427);
              FStar_Syntax_Syntax.sigrng = uu____19428;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19430;
              FStar_Syntax_Syntax.sigattrs = uu____19431;_},uu____19432),uu____19433)
          ->
          FStar_Util.for_some
            (fun uu___9_19494  ->
               match uu___9_19494 with
               | FStar_Syntax_Syntax.RecordType uu____19496 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19506 -> true
               | uu____19516 -> false) quals
      | uu____19518 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19528,uu____19529);
            FStar_Syntax_Syntax.sigrng = uu____19530;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19532;
            FStar_Syntax_Syntax.sigattrs = uu____19533;_},uu____19534),uu____19535)
        ->
        FStar_Util.for_some
          (fun uu___10_19592  ->
             match uu___10_19592 with
             | FStar_Syntax_Syntax.Action uu____19594 -> true
             | uu____19596 -> false) quals
    | uu____19598 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19612 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____19612
  
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
      let uu____19629 =
        let uu____19630 = FStar_Syntax_Util.un_uinst head1  in
        uu____19630.FStar_Syntax_Syntax.n  in
      match uu____19629 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____19636 ->
               true
           | uu____19639 -> false)
      | uu____19641 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19655 = lookup_qname env l  in
      match uu____19655 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____19658),uu____19659) ->
          FStar_Util.for_some
            (fun uu___11_19707  ->
               match uu___11_19707 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____19710 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____19712 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____19788 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____19806) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____19824 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____19832 ->
                 FStar_Pervasives_Native.Some true
             | uu____19851 -> FStar_Pervasives_Native.Some false)
         in
      let uu____19854 =
        let uu____19858 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____19858 mapper  in
      match uu____19854 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____19918 = lookup_qname env lid  in
      match uu____19918 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19922,uu____19923,tps,uu____19925,uu____19926,uu____19927);
              FStar_Syntax_Syntax.sigrng = uu____19928;
              FStar_Syntax_Syntax.sigquals = uu____19929;
              FStar_Syntax_Syntax.sigmeta = uu____19930;
              FStar_Syntax_Syntax.sigattrs = uu____19931;_},uu____19932),uu____19933)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____19999 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20045  ->
              match uu____20045 with
              | (d,uu____20054) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20070 = effect_decl_opt env l  in
      match uu____20070 with
      | FStar_Pervasives_Native.None  ->
          let uu____20085 = name_not_found l  in
          let uu____20091 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20085 uu____20091
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20114  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20133  ->
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
        let uu____20165 = FStar_Ident.lid_equals l1 l2  in
        if uu____20165
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20176 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20176
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20187 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20240  ->
                        match uu____20240 with
                        | (m1,m2,uu____20254,uu____20255,uu____20256) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20187 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20273 =
                    let uu____20279 =
                      let uu____20281 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20283 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20281
                        uu____20283
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20279)
                     in
                  FStar_Errors.raise_error uu____20273 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20293,uu____20294,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20328 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20328
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
  'Auu____20348 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20348) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20377 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20403  ->
                match uu____20403 with
                | (d,uu____20410) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20377 with
      | FStar_Pervasives_Native.None  ->
          let uu____20421 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20421
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20436 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____20436 with
           | (uu____20451,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20469)::(wp,uu____20471)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20527 -> failwith "Impossible"))
  
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
          let uu____20585 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____20585
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____20590 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____20590
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
                  let uu____20601 = get_range env  in
                  let uu____20602 =
                    let uu____20609 =
                      let uu____20610 =
                        let uu____20627 =
                          let uu____20638 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____20638]  in
                        (null_wp, uu____20627)  in
                      FStar_Syntax_Syntax.Tm_app uu____20610  in
                    FStar_Syntax_Syntax.mk uu____20609  in
                  uu____20602 FStar_Pervasives_Native.None uu____20601  in
                let uu____20675 =
                  let uu____20676 =
                    let uu____20687 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____20687]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____20676;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____20675))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1515_20725 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1515_20725.order);
              joins = (uu___1515_20725.joins)
            }  in
          let uu___1518_20734 = env  in
          {
            solver = (uu___1518_20734.solver);
            range = (uu___1518_20734.range);
            curmodule = (uu___1518_20734.curmodule);
            gamma = (uu___1518_20734.gamma);
            gamma_sig = (uu___1518_20734.gamma_sig);
            gamma_cache = (uu___1518_20734.gamma_cache);
            modules = (uu___1518_20734.modules);
            expected_typ = (uu___1518_20734.expected_typ);
            sigtab = (uu___1518_20734.sigtab);
            attrtab = (uu___1518_20734.attrtab);
            is_pattern = (uu___1518_20734.is_pattern);
            instantiate_imp = (uu___1518_20734.instantiate_imp);
            effects;
            generalize = (uu___1518_20734.generalize);
            letrecs = (uu___1518_20734.letrecs);
            top_level = (uu___1518_20734.top_level);
            check_uvars = (uu___1518_20734.check_uvars);
            use_eq = (uu___1518_20734.use_eq);
            is_iface = (uu___1518_20734.is_iface);
            admit = (uu___1518_20734.admit);
            lax = (uu___1518_20734.lax);
            lax_universes = (uu___1518_20734.lax_universes);
            phase1 = (uu___1518_20734.phase1);
            failhard = (uu___1518_20734.failhard);
            nosynth = (uu___1518_20734.nosynth);
            uvar_subtyping = (uu___1518_20734.uvar_subtyping);
            tc_term = (uu___1518_20734.tc_term);
            type_of = (uu___1518_20734.type_of);
            universe_of = (uu___1518_20734.universe_of);
            check_type_of = (uu___1518_20734.check_type_of);
            use_bv_sorts = (uu___1518_20734.use_bv_sorts);
            qtbl_name_and_index = (uu___1518_20734.qtbl_name_and_index);
            normalized_eff_names = (uu___1518_20734.normalized_eff_names);
            fv_delta_depths = (uu___1518_20734.fv_delta_depths);
            proof_ns = (uu___1518_20734.proof_ns);
            synth_hook = (uu___1518_20734.synth_hook);
            splice = (uu___1518_20734.splice);
            postprocess = (uu___1518_20734.postprocess);
            is_native_tactic = (uu___1518_20734.is_native_tactic);
            identifier_info = (uu___1518_20734.identifier_info);
            tc_hooks = (uu___1518_20734.tc_hooks);
            dsenv = (uu___1518_20734.dsenv);
            nbe = (uu___1518_20734.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____20764 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____20764  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____20922 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____20923 = l1 u t wp e  in
                                l2 u t uu____20922 uu____20923))
                | uu____20924 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____20996 = inst_tscheme_with lift_t [u]  in
            match uu____20996 with
            | (uu____21003,lift_t1) ->
                let uu____21005 =
                  let uu____21012 =
                    let uu____21013 =
                      let uu____21030 =
                        let uu____21041 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21050 =
                          let uu____21061 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21061]  in
                        uu____21041 :: uu____21050  in
                      (lift_t1, uu____21030)  in
                    FStar_Syntax_Syntax.Tm_app uu____21013  in
                  FStar_Syntax_Syntax.mk uu____21012  in
                uu____21005 FStar_Pervasives_Native.None
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
            let uu____21171 = inst_tscheme_with lift_t [u]  in
            match uu____21171 with
            | (uu____21178,lift_t1) ->
                let uu____21180 =
                  let uu____21187 =
                    let uu____21188 =
                      let uu____21205 =
                        let uu____21216 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21225 =
                          let uu____21236 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21245 =
                            let uu____21256 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21256]  in
                          uu____21236 :: uu____21245  in
                        uu____21216 :: uu____21225  in
                      (lift_t1, uu____21205)  in
                    FStar_Syntax_Syntax.Tm_app uu____21188  in
                  FStar_Syntax_Syntax.mk uu____21187  in
                uu____21180 FStar_Pervasives_Native.None
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
              let uu____21358 =
                let uu____21359 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21359
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21358  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21368 =
              let uu____21370 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21370  in
            let uu____21371 =
              let uu____21373 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21401 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21401)
                 in
              FStar_Util.dflt "none" uu____21373  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21368
              uu____21371
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21430  ->
                    match uu____21430 with
                    | (e,uu____21438) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21461 =
            match uu____21461 with
            | (i,j) ->
                let uu____21472 = FStar_Ident.lid_equals i j  in
                if uu____21472
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _21479  -> FStar_Pervasives_Native.Some _21479)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____21508 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____21518 = FStar_Ident.lid_equals i k  in
                        if uu____21518
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____21532 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____21532
                                  then []
                                  else
                                    (let uu____21539 =
                                       let uu____21548 =
                                         find_edge order1 (i, k)  in
                                       let uu____21551 =
                                         find_edge order1 (k, j)  in
                                       (uu____21548, uu____21551)  in
                                     match uu____21539 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____21566 =
                                           compose_edges e1 e2  in
                                         [uu____21566]
                                     | uu____21567 -> [])))))
                 in
              FStar_List.append order1 uu____21508  in
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
                   let uu____21597 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____21600 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____21600
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____21597
                   then
                     let uu____21607 =
                       let uu____21613 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____21613)
                        in
                     let uu____21617 = get_range env  in
                     FStar_Errors.raise_error uu____21607 uu____21617
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____21695 = FStar_Ident.lid_equals i j
                                   in
                                if uu____21695
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____21747 =
                                              let uu____21756 =
                                                find_edge order2 (i, k)  in
                                              let uu____21759 =
                                                find_edge order2 (j, k)  in
                                              (uu____21756, uu____21759)  in
                                            match uu____21747 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____21801,uu____21802)
                                                     ->
                                                     let uu____21809 =
                                                       let uu____21816 =
                                                         let uu____21818 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21818
                                                          in
                                                       let uu____21821 =
                                                         let uu____21823 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21823
                                                          in
                                                       (uu____21816,
                                                         uu____21821)
                                                        in
                                                     (match uu____21809 with
                                                      | (true ,true ) ->
                                                          let uu____21840 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____21840
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
                                            | uu____21883 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1645_21956 = env.effects  in
              { decls = (uu___1645_21956.decls); order = order2; joins }  in
            let uu___1648_21957 = env  in
            {
              solver = (uu___1648_21957.solver);
              range = (uu___1648_21957.range);
              curmodule = (uu___1648_21957.curmodule);
              gamma = (uu___1648_21957.gamma);
              gamma_sig = (uu___1648_21957.gamma_sig);
              gamma_cache = (uu___1648_21957.gamma_cache);
              modules = (uu___1648_21957.modules);
              expected_typ = (uu___1648_21957.expected_typ);
              sigtab = (uu___1648_21957.sigtab);
              attrtab = (uu___1648_21957.attrtab);
              is_pattern = (uu___1648_21957.is_pattern);
              instantiate_imp = (uu___1648_21957.instantiate_imp);
              effects;
              generalize = (uu___1648_21957.generalize);
              letrecs = (uu___1648_21957.letrecs);
              top_level = (uu___1648_21957.top_level);
              check_uvars = (uu___1648_21957.check_uvars);
              use_eq = (uu___1648_21957.use_eq);
              is_iface = (uu___1648_21957.is_iface);
              admit = (uu___1648_21957.admit);
              lax = (uu___1648_21957.lax);
              lax_universes = (uu___1648_21957.lax_universes);
              phase1 = (uu___1648_21957.phase1);
              failhard = (uu___1648_21957.failhard);
              nosynth = (uu___1648_21957.nosynth);
              uvar_subtyping = (uu___1648_21957.uvar_subtyping);
              tc_term = (uu___1648_21957.tc_term);
              type_of = (uu___1648_21957.type_of);
              universe_of = (uu___1648_21957.universe_of);
              check_type_of = (uu___1648_21957.check_type_of);
              use_bv_sorts = (uu___1648_21957.use_bv_sorts);
              qtbl_name_and_index = (uu___1648_21957.qtbl_name_and_index);
              normalized_eff_names = (uu___1648_21957.normalized_eff_names);
              fv_delta_depths = (uu___1648_21957.fv_delta_depths);
              proof_ns = (uu___1648_21957.proof_ns);
              synth_hook = (uu___1648_21957.synth_hook);
              splice = (uu___1648_21957.splice);
              postprocess = (uu___1648_21957.postprocess);
              is_native_tactic = (uu___1648_21957.is_native_tactic);
              identifier_info = (uu___1648_21957.identifier_info);
              tc_hooks = (uu___1648_21957.tc_hooks);
              dsenv = (uu___1648_21957.dsenv);
              nbe = (uu___1648_21957.nbe)
            }))
      | uu____21958 -> env
  
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
        | uu____21987 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22000 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22000 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22017 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22017 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____22042 =
                     let uu____22048 =
                       let uu____22050 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22058 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22069 =
                         let uu____22071 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22071  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22050 uu____22058 uu____22069
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22048)
                      in
                   FStar_Errors.raise_error uu____22042
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22079 =
                     let uu____22090 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22090 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22127  ->
                        fun uu____22128  ->
                          match (uu____22127, uu____22128) with
                          | ((x,uu____22158),(t,uu____22160)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22079
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22191 =
                     let uu___1686_22192 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1686_22192.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1686_22192.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1686_22192.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1686_22192.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22191
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22204 .
    'Auu____22204 ->
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
          let uu____22234 = effect_decl_opt env effect_name  in
          match uu____22234 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22273 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22296 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22335 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22335
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22340 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22340
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22355 =
                     let uu____22358 = get_range env  in
                     let uu____22359 =
                       let uu____22366 =
                         let uu____22367 =
                           let uu____22384 =
                             let uu____22395 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22395; wp]  in
                           (repr, uu____22384)  in
                         FStar_Syntax_Syntax.Tm_app uu____22367  in
                       FStar_Syntax_Syntax.mk uu____22366  in
                     uu____22359 FStar_Pervasives_Native.None uu____22358  in
                   FStar_Pervasives_Native.Some uu____22355)
  
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
      | uu____22539 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22554 =
        let uu____22555 = FStar_Syntax_Subst.compress t  in
        uu____22555.FStar_Syntax_Syntax.n  in
      match uu____22554 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22559,c) ->
          is_reifiable_comp env c
      | uu____22581 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22601 =
           let uu____22603 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22603  in
         if uu____22601
         then
           let uu____22606 =
             let uu____22612 =
               let uu____22614 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22614
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22612)  in
           let uu____22618 = get_range env  in
           FStar_Errors.raise_error uu____22606 uu____22618
         else ());
        (let uu____22621 = effect_repr_aux true env c u_c  in
         match uu____22621 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1751_22657 = env  in
        {
          solver = (uu___1751_22657.solver);
          range = (uu___1751_22657.range);
          curmodule = (uu___1751_22657.curmodule);
          gamma = (uu___1751_22657.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1751_22657.gamma_cache);
          modules = (uu___1751_22657.modules);
          expected_typ = (uu___1751_22657.expected_typ);
          sigtab = (uu___1751_22657.sigtab);
          attrtab = (uu___1751_22657.attrtab);
          is_pattern = (uu___1751_22657.is_pattern);
          instantiate_imp = (uu___1751_22657.instantiate_imp);
          effects = (uu___1751_22657.effects);
          generalize = (uu___1751_22657.generalize);
          letrecs = (uu___1751_22657.letrecs);
          top_level = (uu___1751_22657.top_level);
          check_uvars = (uu___1751_22657.check_uvars);
          use_eq = (uu___1751_22657.use_eq);
          is_iface = (uu___1751_22657.is_iface);
          admit = (uu___1751_22657.admit);
          lax = (uu___1751_22657.lax);
          lax_universes = (uu___1751_22657.lax_universes);
          phase1 = (uu___1751_22657.phase1);
          failhard = (uu___1751_22657.failhard);
          nosynth = (uu___1751_22657.nosynth);
          uvar_subtyping = (uu___1751_22657.uvar_subtyping);
          tc_term = (uu___1751_22657.tc_term);
          type_of = (uu___1751_22657.type_of);
          universe_of = (uu___1751_22657.universe_of);
          check_type_of = (uu___1751_22657.check_type_of);
          use_bv_sorts = (uu___1751_22657.use_bv_sorts);
          qtbl_name_and_index = (uu___1751_22657.qtbl_name_and_index);
          normalized_eff_names = (uu___1751_22657.normalized_eff_names);
          fv_delta_depths = (uu___1751_22657.fv_delta_depths);
          proof_ns = (uu___1751_22657.proof_ns);
          synth_hook = (uu___1751_22657.synth_hook);
          splice = (uu___1751_22657.splice);
          postprocess = (uu___1751_22657.postprocess);
          is_native_tactic = (uu___1751_22657.is_native_tactic);
          identifier_info = (uu___1751_22657.identifier_info);
          tc_hooks = (uu___1751_22657.tc_hooks);
          dsenv = (uu___1751_22657.dsenv);
          nbe = (uu___1751_22657.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1758_22671 = env  in
      {
        solver = (uu___1758_22671.solver);
        range = (uu___1758_22671.range);
        curmodule = (uu___1758_22671.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1758_22671.gamma_sig);
        gamma_cache = (uu___1758_22671.gamma_cache);
        modules = (uu___1758_22671.modules);
        expected_typ = (uu___1758_22671.expected_typ);
        sigtab = (uu___1758_22671.sigtab);
        attrtab = (uu___1758_22671.attrtab);
        is_pattern = (uu___1758_22671.is_pattern);
        instantiate_imp = (uu___1758_22671.instantiate_imp);
        effects = (uu___1758_22671.effects);
        generalize = (uu___1758_22671.generalize);
        letrecs = (uu___1758_22671.letrecs);
        top_level = (uu___1758_22671.top_level);
        check_uvars = (uu___1758_22671.check_uvars);
        use_eq = (uu___1758_22671.use_eq);
        is_iface = (uu___1758_22671.is_iface);
        admit = (uu___1758_22671.admit);
        lax = (uu___1758_22671.lax);
        lax_universes = (uu___1758_22671.lax_universes);
        phase1 = (uu___1758_22671.phase1);
        failhard = (uu___1758_22671.failhard);
        nosynth = (uu___1758_22671.nosynth);
        uvar_subtyping = (uu___1758_22671.uvar_subtyping);
        tc_term = (uu___1758_22671.tc_term);
        type_of = (uu___1758_22671.type_of);
        universe_of = (uu___1758_22671.universe_of);
        check_type_of = (uu___1758_22671.check_type_of);
        use_bv_sorts = (uu___1758_22671.use_bv_sorts);
        qtbl_name_and_index = (uu___1758_22671.qtbl_name_and_index);
        normalized_eff_names = (uu___1758_22671.normalized_eff_names);
        fv_delta_depths = (uu___1758_22671.fv_delta_depths);
        proof_ns = (uu___1758_22671.proof_ns);
        synth_hook = (uu___1758_22671.synth_hook);
        splice = (uu___1758_22671.splice);
        postprocess = (uu___1758_22671.postprocess);
        is_native_tactic = (uu___1758_22671.is_native_tactic);
        identifier_info = (uu___1758_22671.identifier_info);
        tc_hooks = (uu___1758_22671.tc_hooks);
        dsenv = (uu___1758_22671.dsenv);
        nbe = (uu___1758_22671.nbe)
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
            (let uu___1771_22729 = env  in
             {
               solver = (uu___1771_22729.solver);
               range = (uu___1771_22729.range);
               curmodule = (uu___1771_22729.curmodule);
               gamma = rest;
               gamma_sig = (uu___1771_22729.gamma_sig);
               gamma_cache = (uu___1771_22729.gamma_cache);
               modules = (uu___1771_22729.modules);
               expected_typ = (uu___1771_22729.expected_typ);
               sigtab = (uu___1771_22729.sigtab);
               attrtab = (uu___1771_22729.attrtab);
               is_pattern = (uu___1771_22729.is_pattern);
               instantiate_imp = (uu___1771_22729.instantiate_imp);
               effects = (uu___1771_22729.effects);
               generalize = (uu___1771_22729.generalize);
               letrecs = (uu___1771_22729.letrecs);
               top_level = (uu___1771_22729.top_level);
               check_uvars = (uu___1771_22729.check_uvars);
               use_eq = (uu___1771_22729.use_eq);
               is_iface = (uu___1771_22729.is_iface);
               admit = (uu___1771_22729.admit);
               lax = (uu___1771_22729.lax);
               lax_universes = (uu___1771_22729.lax_universes);
               phase1 = (uu___1771_22729.phase1);
               failhard = (uu___1771_22729.failhard);
               nosynth = (uu___1771_22729.nosynth);
               uvar_subtyping = (uu___1771_22729.uvar_subtyping);
               tc_term = (uu___1771_22729.tc_term);
               type_of = (uu___1771_22729.type_of);
               universe_of = (uu___1771_22729.universe_of);
               check_type_of = (uu___1771_22729.check_type_of);
               use_bv_sorts = (uu___1771_22729.use_bv_sorts);
               qtbl_name_and_index = (uu___1771_22729.qtbl_name_and_index);
               normalized_eff_names = (uu___1771_22729.normalized_eff_names);
               fv_delta_depths = (uu___1771_22729.fv_delta_depths);
               proof_ns = (uu___1771_22729.proof_ns);
               synth_hook = (uu___1771_22729.synth_hook);
               splice = (uu___1771_22729.splice);
               postprocess = (uu___1771_22729.postprocess);
               is_native_tactic = (uu___1771_22729.is_native_tactic);
               identifier_info = (uu___1771_22729.identifier_info);
               tc_hooks = (uu___1771_22729.tc_hooks);
               dsenv = (uu___1771_22729.dsenv);
               nbe = (uu___1771_22729.nbe)
             }))
    | uu____22730 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____22759  ->
             match uu____22759 with | (x,uu____22767) -> push_bv env1 x) env
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
            let uu___1785_22802 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1785_22802.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1785_22802.FStar_Syntax_Syntax.index);
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
      (let uu___1796_22844 = env  in
       {
         solver = (uu___1796_22844.solver);
         range = (uu___1796_22844.range);
         curmodule = (uu___1796_22844.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1796_22844.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1796_22844.sigtab);
         attrtab = (uu___1796_22844.attrtab);
         is_pattern = (uu___1796_22844.is_pattern);
         instantiate_imp = (uu___1796_22844.instantiate_imp);
         effects = (uu___1796_22844.effects);
         generalize = (uu___1796_22844.generalize);
         letrecs = (uu___1796_22844.letrecs);
         top_level = (uu___1796_22844.top_level);
         check_uvars = (uu___1796_22844.check_uvars);
         use_eq = (uu___1796_22844.use_eq);
         is_iface = (uu___1796_22844.is_iface);
         admit = (uu___1796_22844.admit);
         lax = (uu___1796_22844.lax);
         lax_universes = (uu___1796_22844.lax_universes);
         phase1 = (uu___1796_22844.phase1);
         failhard = (uu___1796_22844.failhard);
         nosynth = (uu___1796_22844.nosynth);
         uvar_subtyping = (uu___1796_22844.uvar_subtyping);
         tc_term = (uu___1796_22844.tc_term);
         type_of = (uu___1796_22844.type_of);
         universe_of = (uu___1796_22844.universe_of);
         check_type_of = (uu___1796_22844.check_type_of);
         use_bv_sorts = (uu___1796_22844.use_bv_sorts);
         qtbl_name_and_index = (uu___1796_22844.qtbl_name_and_index);
         normalized_eff_names = (uu___1796_22844.normalized_eff_names);
         fv_delta_depths = (uu___1796_22844.fv_delta_depths);
         proof_ns = (uu___1796_22844.proof_ns);
         synth_hook = (uu___1796_22844.synth_hook);
         splice = (uu___1796_22844.splice);
         postprocess = (uu___1796_22844.postprocess);
         is_native_tactic = (uu___1796_22844.is_native_tactic);
         identifier_info = (uu___1796_22844.identifier_info);
         tc_hooks = (uu___1796_22844.tc_hooks);
         dsenv = (uu___1796_22844.dsenv);
         nbe = (uu___1796_22844.nbe)
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
        let uu____22888 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____22888 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____22916 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____22916)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1811_22932 = env  in
      {
        solver = (uu___1811_22932.solver);
        range = (uu___1811_22932.range);
        curmodule = (uu___1811_22932.curmodule);
        gamma = (uu___1811_22932.gamma);
        gamma_sig = (uu___1811_22932.gamma_sig);
        gamma_cache = (uu___1811_22932.gamma_cache);
        modules = (uu___1811_22932.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1811_22932.sigtab);
        attrtab = (uu___1811_22932.attrtab);
        is_pattern = (uu___1811_22932.is_pattern);
        instantiate_imp = (uu___1811_22932.instantiate_imp);
        effects = (uu___1811_22932.effects);
        generalize = (uu___1811_22932.generalize);
        letrecs = (uu___1811_22932.letrecs);
        top_level = (uu___1811_22932.top_level);
        check_uvars = (uu___1811_22932.check_uvars);
        use_eq = false;
        is_iface = (uu___1811_22932.is_iface);
        admit = (uu___1811_22932.admit);
        lax = (uu___1811_22932.lax);
        lax_universes = (uu___1811_22932.lax_universes);
        phase1 = (uu___1811_22932.phase1);
        failhard = (uu___1811_22932.failhard);
        nosynth = (uu___1811_22932.nosynth);
        uvar_subtyping = (uu___1811_22932.uvar_subtyping);
        tc_term = (uu___1811_22932.tc_term);
        type_of = (uu___1811_22932.type_of);
        universe_of = (uu___1811_22932.universe_of);
        check_type_of = (uu___1811_22932.check_type_of);
        use_bv_sorts = (uu___1811_22932.use_bv_sorts);
        qtbl_name_and_index = (uu___1811_22932.qtbl_name_and_index);
        normalized_eff_names = (uu___1811_22932.normalized_eff_names);
        fv_delta_depths = (uu___1811_22932.fv_delta_depths);
        proof_ns = (uu___1811_22932.proof_ns);
        synth_hook = (uu___1811_22932.synth_hook);
        splice = (uu___1811_22932.splice);
        postprocess = (uu___1811_22932.postprocess);
        is_native_tactic = (uu___1811_22932.is_native_tactic);
        identifier_info = (uu___1811_22932.identifier_info);
        tc_hooks = (uu___1811_22932.tc_hooks);
        dsenv = (uu___1811_22932.dsenv);
        nbe = (uu___1811_22932.nbe)
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
    let uu____22963 = expected_typ env_  in
    ((let uu___1818_22969 = env_  in
      {
        solver = (uu___1818_22969.solver);
        range = (uu___1818_22969.range);
        curmodule = (uu___1818_22969.curmodule);
        gamma = (uu___1818_22969.gamma);
        gamma_sig = (uu___1818_22969.gamma_sig);
        gamma_cache = (uu___1818_22969.gamma_cache);
        modules = (uu___1818_22969.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1818_22969.sigtab);
        attrtab = (uu___1818_22969.attrtab);
        is_pattern = (uu___1818_22969.is_pattern);
        instantiate_imp = (uu___1818_22969.instantiate_imp);
        effects = (uu___1818_22969.effects);
        generalize = (uu___1818_22969.generalize);
        letrecs = (uu___1818_22969.letrecs);
        top_level = (uu___1818_22969.top_level);
        check_uvars = (uu___1818_22969.check_uvars);
        use_eq = false;
        is_iface = (uu___1818_22969.is_iface);
        admit = (uu___1818_22969.admit);
        lax = (uu___1818_22969.lax);
        lax_universes = (uu___1818_22969.lax_universes);
        phase1 = (uu___1818_22969.phase1);
        failhard = (uu___1818_22969.failhard);
        nosynth = (uu___1818_22969.nosynth);
        uvar_subtyping = (uu___1818_22969.uvar_subtyping);
        tc_term = (uu___1818_22969.tc_term);
        type_of = (uu___1818_22969.type_of);
        universe_of = (uu___1818_22969.universe_of);
        check_type_of = (uu___1818_22969.check_type_of);
        use_bv_sorts = (uu___1818_22969.use_bv_sorts);
        qtbl_name_and_index = (uu___1818_22969.qtbl_name_and_index);
        normalized_eff_names = (uu___1818_22969.normalized_eff_names);
        fv_delta_depths = (uu___1818_22969.fv_delta_depths);
        proof_ns = (uu___1818_22969.proof_ns);
        synth_hook = (uu___1818_22969.synth_hook);
        splice = (uu___1818_22969.splice);
        postprocess = (uu___1818_22969.postprocess);
        is_native_tactic = (uu___1818_22969.is_native_tactic);
        identifier_info = (uu___1818_22969.identifier_info);
        tc_hooks = (uu___1818_22969.tc_hooks);
        dsenv = (uu___1818_22969.dsenv);
        nbe = (uu___1818_22969.nbe)
      }), uu____22963)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____22981 =
      let uu____22984 = FStar_Ident.id_of_text ""  in [uu____22984]  in
    FStar_Ident.lid_of_ids uu____22981  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____22991 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____22991
        then
          let uu____22996 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____22996 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1826_23024 = env  in
       {
         solver = (uu___1826_23024.solver);
         range = (uu___1826_23024.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1826_23024.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1826_23024.expected_typ);
         sigtab = (uu___1826_23024.sigtab);
         attrtab = (uu___1826_23024.attrtab);
         is_pattern = (uu___1826_23024.is_pattern);
         instantiate_imp = (uu___1826_23024.instantiate_imp);
         effects = (uu___1826_23024.effects);
         generalize = (uu___1826_23024.generalize);
         letrecs = (uu___1826_23024.letrecs);
         top_level = (uu___1826_23024.top_level);
         check_uvars = (uu___1826_23024.check_uvars);
         use_eq = (uu___1826_23024.use_eq);
         is_iface = (uu___1826_23024.is_iface);
         admit = (uu___1826_23024.admit);
         lax = (uu___1826_23024.lax);
         lax_universes = (uu___1826_23024.lax_universes);
         phase1 = (uu___1826_23024.phase1);
         failhard = (uu___1826_23024.failhard);
         nosynth = (uu___1826_23024.nosynth);
         uvar_subtyping = (uu___1826_23024.uvar_subtyping);
         tc_term = (uu___1826_23024.tc_term);
         type_of = (uu___1826_23024.type_of);
         universe_of = (uu___1826_23024.universe_of);
         check_type_of = (uu___1826_23024.check_type_of);
         use_bv_sorts = (uu___1826_23024.use_bv_sorts);
         qtbl_name_and_index = (uu___1826_23024.qtbl_name_and_index);
         normalized_eff_names = (uu___1826_23024.normalized_eff_names);
         fv_delta_depths = (uu___1826_23024.fv_delta_depths);
         proof_ns = (uu___1826_23024.proof_ns);
         synth_hook = (uu___1826_23024.synth_hook);
         splice = (uu___1826_23024.splice);
         postprocess = (uu___1826_23024.postprocess);
         is_native_tactic = (uu___1826_23024.is_native_tactic);
         identifier_info = (uu___1826_23024.identifier_info);
         tc_hooks = (uu___1826_23024.tc_hooks);
         dsenv = (uu___1826_23024.dsenv);
         nbe = (uu___1826_23024.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23076)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23080,(uu____23081,t)))::tl1
          ->
          let uu____23102 =
            let uu____23105 = FStar_Syntax_Free.uvars t  in
            ext out uu____23105  in
          aux uu____23102 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23108;
            FStar_Syntax_Syntax.index = uu____23109;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23117 =
            let uu____23120 = FStar_Syntax_Free.uvars t  in
            ext out uu____23120  in
          aux uu____23117 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23178)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23182,(uu____23183,t)))::tl1
          ->
          let uu____23204 =
            let uu____23207 = FStar_Syntax_Free.univs t  in
            ext out uu____23207  in
          aux uu____23204 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23210;
            FStar_Syntax_Syntax.index = uu____23211;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23219 =
            let uu____23222 = FStar_Syntax_Free.univs t  in
            ext out uu____23222  in
          aux uu____23219 tl1
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
          let uu____23284 = FStar_Util.set_add uname out  in
          aux uu____23284 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23287,(uu____23288,t)))::tl1
          ->
          let uu____23309 =
            let uu____23312 = FStar_Syntax_Free.univnames t  in
            ext out uu____23312  in
          aux uu____23309 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23315;
            FStar_Syntax_Syntax.index = uu____23316;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23324 =
            let uu____23327 = FStar_Syntax_Free.univnames t  in
            ext out uu____23327  in
          aux uu____23324 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_23348  ->
            match uu___12_23348 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23352 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23365 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23376 =
      let uu____23385 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23385
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23376 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23433 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_23446  ->
              match uu___13_23446 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23449 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____23449
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23455) ->
                  let uu____23472 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____23472))
       in
    FStar_All.pipe_right uu____23433 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_23486  ->
    match uu___14_23486 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only (true ) -> "Eager_unfolding_only true"
    | Eager_unfolding_only uu____23492 -> "Eager_unfolding_only false"
    | Unfold d ->
        let uu____23496 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____23496
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23519  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23574) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____23607,uu____23608) -> false  in
      let uu____23622 =
        FStar_List.tryFind
          (fun uu____23644  ->
             match uu____23644 with | (p,uu____23655) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____23622 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23674,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23704 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23704
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1972_23726 = e  in
        {
          solver = (uu___1972_23726.solver);
          range = (uu___1972_23726.range);
          curmodule = (uu___1972_23726.curmodule);
          gamma = (uu___1972_23726.gamma);
          gamma_sig = (uu___1972_23726.gamma_sig);
          gamma_cache = (uu___1972_23726.gamma_cache);
          modules = (uu___1972_23726.modules);
          expected_typ = (uu___1972_23726.expected_typ);
          sigtab = (uu___1972_23726.sigtab);
          attrtab = (uu___1972_23726.attrtab);
          is_pattern = (uu___1972_23726.is_pattern);
          instantiate_imp = (uu___1972_23726.instantiate_imp);
          effects = (uu___1972_23726.effects);
          generalize = (uu___1972_23726.generalize);
          letrecs = (uu___1972_23726.letrecs);
          top_level = (uu___1972_23726.top_level);
          check_uvars = (uu___1972_23726.check_uvars);
          use_eq = (uu___1972_23726.use_eq);
          is_iface = (uu___1972_23726.is_iface);
          admit = (uu___1972_23726.admit);
          lax = (uu___1972_23726.lax);
          lax_universes = (uu___1972_23726.lax_universes);
          phase1 = (uu___1972_23726.phase1);
          failhard = (uu___1972_23726.failhard);
          nosynth = (uu___1972_23726.nosynth);
          uvar_subtyping = (uu___1972_23726.uvar_subtyping);
          tc_term = (uu___1972_23726.tc_term);
          type_of = (uu___1972_23726.type_of);
          universe_of = (uu___1972_23726.universe_of);
          check_type_of = (uu___1972_23726.check_type_of);
          use_bv_sorts = (uu___1972_23726.use_bv_sorts);
          qtbl_name_and_index = (uu___1972_23726.qtbl_name_and_index);
          normalized_eff_names = (uu___1972_23726.normalized_eff_names);
          fv_delta_depths = (uu___1972_23726.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1972_23726.synth_hook);
          splice = (uu___1972_23726.splice);
          postprocess = (uu___1972_23726.postprocess);
          is_native_tactic = (uu___1972_23726.is_native_tactic);
          identifier_info = (uu___1972_23726.identifier_info);
          tc_hooks = (uu___1972_23726.tc_hooks);
          dsenv = (uu___1972_23726.dsenv);
          nbe = (uu___1972_23726.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1981_23774 = e  in
      {
        solver = (uu___1981_23774.solver);
        range = (uu___1981_23774.range);
        curmodule = (uu___1981_23774.curmodule);
        gamma = (uu___1981_23774.gamma);
        gamma_sig = (uu___1981_23774.gamma_sig);
        gamma_cache = (uu___1981_23774.gamma_cache);
        modules = (uu___1981_23774.modules);
        expected_typ = (uu___1981_23774.expected_typ);
        sigtab = (uu___1981_23774.sigtab);
        attrtab = (uu___1981_23774.attrtab);
        is_pattern = (uu___1981_23774.is_pattern);
        instantiate_imp = (uu___1981_23774.instantiate_imp);
        effects = (uu___1981_23774.effects);
        generalize = (uu___1981_23774.generalize);
        letrecs = (uu___1981_23774.letrecs);
        top_level = (uu___1981_23774.top_level);
        check_uvars = (uu___1981_23774.check_uvars);
        use_eq = (uu___1981_23774.use_eq);
        is_iface = (uu___1981_23774.is_iface);
        admit = (uu___1981_23774.admit);
        lax = (uu___1981_23774.lax);
        lax_universes = (uu___1981_23774.lax_universes);
        phase1 = (uu___1981_23774.phase1);
        failhard = (uu___1981_23774.failhard);
        nosynth = (uu___1981_23774.nosynth);
        uvar_subtyping = (uu___1981_23774.uvar_subtyping);
        tc_term = (uu___1981_23774.tc_term);
        type_of = (uu___1981_23774.type_of);
        universe_of = (uu___1981_23774.universe_of);
        check_type_of = (uu___1981_23774.check_type_of);
        use_bv_sorts = (uu___1981_23774.use_bv_sorts);
        qtbl_name_and_index = (uu___1981_23774.qtbl_name_and_index);
        normalized_eff_names = (uu___1981_23774.normalized_eff_names);
        fv_delta_depths = (uu___1981_23774.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1981_23774.synth_hook);
        splice = (uu___1981_23774.splice);
        postprocess = (uu___1981_23774.postprocess);
        is_native_tactic = (uu___1981_23774.is_native_tactic);
        identifier_info = (uu___1981_23774.identifier_info);
        tc_hooks = (uu___1981_23774.tc_hooks);
        dsenv = (uu___1981_23774.dsenv);
        nbe = (uu___1981_23774.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____23790 = FStar_Syntax_Free.names t  in
      let uu____23793 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____23790 uu____23793
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____23816 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____23816
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____23826 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____23826
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____23847 =
      match uu____23847 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____23867 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____23867)
       in
    let uu____23875 =
      let uu____23879 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____23879 FStar_List.rev  in
    FStar_All.pipe_right uu____23875 (FStar_String.concat " ")
  
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
                  (let uu____23949 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____23949 with
                   | FStar_Pervasives_Native.Some uu____23953 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____23956 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____23966;
        univ_ineqs = uu____23967; implicits = uu____23968;_} -> true
    | uu____23980 -> false
  
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
          let uu___2025_24011 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2025_24011.deferred);
            univ_ineqs = (uu___2025_24011.univ_ineqs);
            implicits = (uu___2025_24011.implicits)
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
          let uu____24050 = FStar_Options.defensive ()  in
          if uu____24050
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24056 =
              let uu____24058 =
                let uu____24060 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24060  in
              Prims.op_Negation uu____24058  in
            (if uu____24056
             then
               let uu____24067 =
                 let uu____24073 =
                   let uu____24075 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24077 =
                     let uu____24079 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24079
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24075 uu____24077
                    in
                 (FStar_Errors.Warning_Defensive, uu____24073)  in
               FStar_Errors.log_issue rng uu____24067
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
          let uu____24119 =
            let uu____24121 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24121  in
          if uu____24119
          then ()
          else
            (let uu____24126 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24126 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24152 =
            let uu____24154 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24154  in
          if uu____24152
          then ()
          else
            (let uu____24159 = bound_vars e  in
             def_check_closed_in rng msg uu____24159 t)
  
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
          let uu___2062_24198 = g  in
          let uu____24199 =
            let uu____24200 =
              let uu____24201 =
                let uu____24208 =
                  let uu____24209 =
                    let uu____24226 =
                      let uu____24237 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24237]  in
                    (f, uu____24226)  in
                  FStar_Syntax_Syntax.Tm_app uu____24209  in
                FStar_Syntax_Syntax.mk uu____24208  in
              uu____24201 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24274  -> FStar_TypeChecker_Common.NonTrivial _24274)
              uu____24200
             in
          {
            guard_f = uu____24199;
            deferred = (uu___2062_24198.deferred);
            univ_ineqs = (uu___2062_24198.univ_ineqs);
            implicits = (uu___2062_24198.implicits)
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
          let uu___2069_24292 = g  in
          let uu____24293 =
            let uu____24294 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24294  in
          {
            guard_f = uu____24293;
            deferred = (uu___2069_24292.deferred);
            univ_ineqs = (uu___2069_24292.univ_ineqs);
            implicits = (uu___2069_24292.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2074_24311 = g  in
          let uu____24312 =
            let uu____24313 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24313  in
          {
            guard_f = uu____24312;
            deferred = (uu___2074_24311.deferred);
            univ_ineqs = (uu___2074_24311.univ_ineqs);
            implicits = (uu___2074_24311.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2078_24315 = g  in
          let uu____24316 =
            let uu____24317 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24317  in
          {
            guard_f = uu____24316;
            deferred = (uu___2078_24315.deferred);
            univ_ineqs = (uu___2078_24315.univ_ineqs);
            implicits = (uu___2078_24315.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24324 ->
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
          let uu____24341 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24341
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24348 =
      let uu____24349 = FStar_Syntax_Util.unmeta t  in
      uu____24349.FStar_Syntax_Syntax.n  in
    match uu____24348 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24353 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24396 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24396;
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
                       let uu____24491 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24491
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2133_24498 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2133_24498.deferred);
              univ_ineqs = (uu___2133_24498.univ_ineqs);
              implicits = (uu___2133_24498.implicits)
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
               let uu____24532 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24532
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
            let uu___2148_24559 = g  in
            let uu____24560 =
              let uu____24561 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24561  in
            {
              guard_f = uu____24560;
              deferred = (uu___2148_24559.deferred);
              univ_ineqs = (uu___2148_24559.univ_ineqs);
              implicits = (uu___2148_24559.implicits)
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
              let uu____24619 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____24619 with
              | FStar_Pervasives_Native.Some
                  (uu____24644::(tm,uu____24646)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____24710 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____24728 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____24728;
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
                      let uu___2170_24760 = trivial_guard  in
                      {
                        guard_f = (uu___2170_24760.guard_f);
                        deferred = (uu___2170_24760.deferred);
                        univ_ineqs = (uu___2170_24760.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____24778  -> ());
    push = (fun uu____24780  -> ());
    pop = (fun uu____24783  -> ());
    snapshot =
      (fun uu____24786  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____24805  -> fun uu____24806  -> ());
    encode_sig = (fun uu____24821  -> fun uu____24822  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____24828 =
             let uu____24835 = FStar_Options.peek ()  in (e, g, uu____24835)
              in
           [uu____24828]);
    solve = (fun uu____24851  -> fun uu____24852  -> fun uu____24853  -> ());
    finish = (fun uu____24860  -> ());
    refresh = (fun uu____24862  -> ())
  } 