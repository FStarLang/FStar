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
  fun projectee  -> match projectee with | Beta  -> true | uu____116 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____127 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____138 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____150 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____168 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____179 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____190 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding _0 -> true | uu____203 -> false
  
let (__proj__Eager_unfolding__item___0 : step -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding _0 -> _0 
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____224 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____235 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____247 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____268 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____295 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____322 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____346 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____357 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____368 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____379 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____390 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____401 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____412 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____423 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____434 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____445 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____456 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____467 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____478 -> false
  
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
      | uu____543 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only of Prims.bool 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____575 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____586 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only _0 -> true
    | uu____599 -> false
  
let (__proj__Eager_unfolding_only__item___0 : delta_level -> Prims.bool) =
  fun projectee  -> match projectee with | Eager_unfolding_only _0 -> _0 
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____621 -> false
  
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
           (fun uu___0_12411  ->
              match uu___0_12411 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12414 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12414  in
                  let uu____12415 =
                    let uu____12416 = FStar_Syntax_Subst.compress y  in
                    uu____12416.FStar_Syntax_Syntax.n  in
                  (match uu____12415 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12420 =
                         let uu___342_12421 = y1  in
                         let uu____12422 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___342_12421.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___342_12421.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12422
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12420
                   | uu____12425 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___348_12439 = env  in
      let uu____12440 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___348_12439.solver);
        range = (uu___348_12439.range);
        curmodule = (uu___348_12439.curmodule);
        gamma = uu____12440;
        gamma_sig = (uu___348_12439.gamma_sig);
        gamma_cache = (uu___348_12439.gamma_cache);
        modules = (uu___348_12439.modules);
        expected_typ = (uu___348_12439.expected_typ);
        sigtab = (uu___348_12439.sigtab);
        attrtab = (uu___348_12439.attrtab);
        is_pattern = (uu___348_12439.is_pattern);
        instantiate_imp = (uu___348_12439.instantiate_imp);
        effects = (uu___348_12439.effects);
        generalize = (uu___348_12439.generalize);
        letrecs = (uu___348_12439.letrecs);
        top_level = (uu___348_12439.top_level);
        check_uvars = (uu___348_12439.check_uvars);
        use_eq = (uu___348_12439.use_eq);
        is_iface = (uu___348_12439.is_iface);
        admit = (uu___348_12439.admit);
        lax = (uu___348_12439.lax);
        lax_universes = (uu___348_12439.lax_universes);
        phase1 = (uu___348_12439.phase1);
        failhard = (uu___348_12439.failhard);
        nosynth = (uu___348_12439.nosynth);
        uvar_subtyping = (uu___348_12439.uvar_subtyping);
        tc_term = (uu___348_12439.tc_term);
        type_of = (uu___348_12439.type_of);
        universe_of = (uu___348_12439.universe_of);
        check_type_of = (uu___348_12439.check_type_of);
        use_bv_sorts = (uu___348_12439.use_bv_sorts);
        qtbl_name_and_index = (uu___348_12439.qtbl_name_and_index);
        normalized_eff_names = (uu___348_12439.normalized_eff_names);
        fv_delta_depths = (uu___348_12439.fv_delta_depths);
        proof_ns = (uu___348_12439.proof_ns);
        synth_hook = (uu___348_12439.synth_hook);
        splice = (uu___348_12439.splice);
        postprocess = (uu___348_12439.postprocess);
        is_native_tactic = (uu___348_12439.is_native_tactic);
        identifier_info = (uu___348_12439.identifier_info);
        tc_hooks = (uu___348_12439.tc_hooks);
        dsenv = (uu___348_12439.dsenv);
        nbe = (uu___348_12439.nbe);
        strict_args_tab = (uu___348_12439.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12448  -> fun uu____12449  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___355_12471 = env  in
      {
        solver = (uu___355_12471.solver);
        range = (uu___355_12471.range);
        curmodule = (uu___355_12471.curmodule);
        gamma = (uu___355_12471.gamma);
        gamma_sig = (uu___355_12471.gamma_sig);
        gamma_cache = (uu___355_12471.gamma_cache);
        modules = (uu___355_12471.modules);
        expected_typ = (uu___355_12471.expected_typ);
        sigtab = (uu___355_12471.sigtab);
        attrtab = (uu___355_12471.attrtab);
        is_pattern = (uu___355_12471.is_pattern);
        instantiate_imp = (uu___355_12471.instantiate_imp);
        effects = (uu___355_12471.effects);
        generalize = (uu___355_12471.generalize);
        letrecs = (uu___355_12471.letrecs);
        top_level = (uu___355_12471.top_level);
        check_uvars = (uu___355_12471.check_uvars);
        use_eq = (uu___355_12471.use_eq);
        is_iface = (uu___355_12471.is_iface);
        admit = (uu___355_12471.admit);
        lax = (uu___355_12471.lax);
        lax_universes = (uu___355_12471.lax_universes);
        phase1 = (uu___355_12471.phase1);
        failhard = (uu___355_12471.failhard);
        nosynth = (uu___355_12471.nosynth);
        uvar_subtyping = (uu___355_12471.uvar_subtyping);
        tc_term = (uu___355_12471.tc_term);
        type_of = (uu___355_12471.type_of);
        universe_of = (uu___355_12471.universe_of);
        check_type_of = (uu___355_12471.check_type_of);
        use_bv_sorts = (uu___355_12471.use_bv_sorts);
        qtbl_name_and_index = (uu___355_12471.qtbl_name_and_index);
        normalized_eff_names = (uu___355_12471.normalized_eff_names);
        fv_delta_depths = (uu___355_12471.fv_delta_depths);
        proof_ns = (uu___355_12471.proof_ns);
        synth_hook = (uu___355_12471.synth_hook);
        splice = (uu___355_12471.splice);
        postprocess = (uu___355_12471.postprocess);
        is_native_tactic = (uu___355_12471.is_native_tactic);
        identifier_info = (uu___355_12471.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___355_12471.dsenv);
        nbe = (uu___355_12471.nbe);
        strict_args_tab = (uu___355_12471.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___359_12483 = e  in
      let uu____12484 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___359_12483.solver);
        range = (uu___359_12483.range);
        curmodule = (uu___359_12483.curmodule);
        gamma = (uu___359_12483.gamma);
        gamma_sig = (uu___359_12483.gamma_sig);
        gamma_cache = (uu___359_12483.gamma_cache);
        modules = (uu___359_12483.modules);
        expected_typ = (uu___359_12483.expected_typ);
        sigtab = (uu___359_12483.sigtab);
        attrtab = (uu___359_12483.attrtab);
        is_pattern = (uu___359_12483.is_pattern);
        instantiate_imp = (uu___359_12483.instantiate_imp);
        effects = (uu___359_12483.effects);
        generalize = (uu___359_12483.generalize);
        letrecs = (uu___359_12483.letrecs);
        top_level = (uu___359_12483.top_level);
        check_uvars = (uu___359_12483.check_uvars);
        use_eq = (uu___359_12483.use_eq);
        is_iface = (uu___359_12483.is_iface);
        admit = (uu___359_12483.admit);
        lax = (uu___359_12483.lax);
        lax_universes = (uu___359_12483.lax_universes);
        phase1 = (uu___359_12483.phase1);
        failhard = (uu___359_12483.failhard);
        nosynth = (uu___359_12483.nosynth);
        uvar_subtyping = (uu___359_12483.uvar_subtyping);
        tc_term = (uu___359_12483.tc_term);
        type_of = (uu___359_12483.type_of);
        universe_of = (uu___359_12483.universe_of);
        check_type_of = (uu___359_12483.check_type_of);
        use_bv_sorts = (uu___359_12483.use_bv_sorts);
        qtbl_name_and_index = (uu___359_12483.qtbl_name_and_index);
        normalized_eff_names = (uu___359_12483.normalized_eff_names);
        fv_delta_depths = (uu___359_12483.fv_delta_depths);
        proof_ns = (uu___359_12483.proof_ns);
        synth_hook = (uu___359_12483.synth_hook);
        splice = (uu___359_12483.splice);
        postprocess = (uu___359_12483.postprocess);
        is_native_tactic = (uu___359_12483.is_native_tactic);
        identifier_info = (uu___359_12483.identifier_info);
        tc_hooks = (uu___359_12483.tc_hooks);
        dsenv = uu____12484;
        nbe = (uu___359_12483.nbe);
        strict_args_tab = (uu___359_12483.strict_args_tab)
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
      | (NoDelta ,uu____12513) -> true
      | (Eager_unfolding_only
         uu____12515,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold
         uu____12518,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12520,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12523 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12537 . unit -> 'Auu____12537 FStar_Util.smap =
  fun uu____12544  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12550 . unit -> 'Auu____12550 FStar_Util.smap =
  fun uu____12557  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____12695 = new_gamma_cache ()  in
                  let uu____12698 = new_sigtab ()  in
                  let uu____12701 = new_sigtab ()  in
                  let uu____12708 =
                    let uu____12723 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____12723, FStar_Pervasives_Native.None)  in
                  let uu____12744 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12748 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____12752 = FStar_Options.using_facts_from ()  in
                  let uu____12753 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12756 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____12757 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12695;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12698;
                    attrtab = uu____12701;
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
                    qtbl_name_and_index = uu____12708;
                    normalized_eff_names = uu____12744;
                    fv_delta_depths = uu____12748;
                    proof_ns = uu____12752;
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
                    is_native_tactic = (fun uu____12832  -> false);
                    identifier_info = uu____12753;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12756;
                    nbe = nbe1;
                    strict_args_tab = uu____12757
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
  fun uu____12911  ->
    let uu____12912 = FStar_ST.op_Bang query_indices  in
    match uu____12912 with
    | [] -> failwith "Empty query indices!"
    | uu____12967 ->
        let uu____12977 =
          let uu____12987 =
            let uu____12995 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12995  in
          let uu____13049 = FStar_ST.op_Bang query_indices  in uu____12987 ::
            uu____13049
           in
        FStar_ST.op_Colon_Equals query_indices uu____12977
  
let (pop_query_indices : unit -> unit) =
  fun uu____13145  ->
    let uu____13146 = FStar_ST.op_Bang query_indices  in
    match uu____13146 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13273  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13310  ->
    match uu____13310 with
    | (l,n1) ->
        let uu____13320 = FStar_ST.op_Bang query_indices  in
        (match uu____13320 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13442 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13465  ->
    let uu____13466 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13466
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13534 =
       let uu____13537 = FStar_ST.op_Bang stack  in env :: uu____13537  in
     FStar_ST.op_Colon_Equals stack uu____13534);
    (let uu___428_13586 = env  in
     let uu____13587 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13590 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13593 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13600 =
       let uu____13615 =
         let uu____13619 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13619  in
       let uu____13651 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13615, uu____13651)  in
     let uu____13700 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13703 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13706 =
       let uu____13709 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13709  in
     let uu____13729 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___428_13586.solver);
       range = (uu___428_13586.range);
       curmodule = (uu___428_13586.curmodule);
       gamma = (uu___428_13586.gamma);
       gamma_sig = (uu___428_13586.gamma_sig);
       gamma_cache = uu____13587;
       modules = (uu___428_13586.modules);
       expected_typ = (uu___428_13586.expected_typ);
       sigtab = uu____13590;
       attrtab = uu____13593;
       is_pattern = (uu___428_13586.is_pattern);
       instantiate_imp = (uu___428_13586.instantiate_imp);
       effects = (uu___428_13586.effects);
       generalize = (uu___428_13586.generalize);
       letrecs = (uu___428_13586.letrecs);
       top_level = (uu___428_13586.top_level);
       check_uvars = (uu___428_13586.check_uvars);
       use_eq = (uu___428_13586.use_eq);
       is_iface = (uu___428_13586.is_iface);
       admit = (uu___428_13586.admit);
       lax = (uu___428_13586.lax);
       lax_universes = (uu___428_13586.lax_universes);
       phase1 = (uu___428_13586.phase1);
       failhard = (uu___428_13586.failhard);
       nosynth = (uu___428_13586.nosynth);
       uvar_subtyping = (uu___428_13586.uvar_subtyping);
       tc_term = (uu___428_13586.tc_term);
       type_of = (uu___428_13586.type_of);
       universe_of = (uu___428_13586.universe_of);
       check_type_of = (uu___428_13586.check_type_of);
       use_bv_sorts = (uu___428_13586.use_bv_sorts);
       qtbl_name_and_index = uu____13600;
       normalized_eff_names = uu____13700;
       fv_delta_depths = uu____13703;
       proof_ns = (uu___428_13586.proof_ns);
       synth_hook = (uu___428_13586.synth_hook);
       splice = (uu___428_13586.splice);
       postprocess = (uu___428_13586.postprocess);
       is_native_tactic = (uu___428_13586.is_native_tactic);
       identifier_info = uu____13706;
       tc_hooks = (uu___428_13586.tc_hooks);
       dsenv = (uu___428_13586.dsenv);
       nbe = (uu___428_13586.nbe);
       strict_args_tab = uu____13729
     })
  
let (pop_stack : unit -> env) =
  fun uu____13747  ->
    let uu____13748 = FStar_ST.op_Bang stack  in
    match uu____13748 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13802 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13892  ->
           let uu____13893 = snapshot_stack env  in
           match uu____13893 with
           | (stack_depth,env1) ->
               let uu____13927 = snapshot_query_indices ()  in
               (match uu____13927 with
                | (query_indices_depth,()) ->
                    let uu____13960 = (env1.solver).snapshot msg  in
                    (match uu____13960 with
                     | (solver_depth,()) ->
                         let uu____14017 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14017 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___453_14084 = env1  in
                                 {
                                   solver = (uu___453_14084.solver);
                                   range = (uu___453_14084.range);
                                   curmodule = (uu___453_14084.curmodule);
                                   gamma = (uu___453_14084.gamma);
                                   gamma_sig = (uu___453_14084.gamma_sig);
                                   gamma_cache = (uu___453_14084.gamma_cache);
                                   modules = (uu___453_14084.modules);
                                   expected_typ =
                                     (uu___453_14084.expected_typ);
                                   sigtab = (uu___453_14084.sigtab);
                                   attrtab = (uu___453_14084.attrtab);
                                   is_pattern = (uu___453_14084.is_pattern);
                                   instantiate_imp =
                                     (uu___453_14084.instantiate_imp);
                                   effects = (uu___453_14084.effects);
                                   generalize = (uu___453_14084.generalize);
                                   letrecs = (uu___453_14084.letrecs);
                                   top_level = (uu___453_14084.top_level);
                                   check_uvars = (uu___453_14084.check_uvars);
                                   use_eq = (uu___453_14084.use_eq);
                                   is_iface = (uu___453_14084.is_iface);
                                   admit = (uu___453_14084.admit);
                                   lax = (uu___453_14084.lax);
                                   lax_universes =
                                     (uu___453_14084.lax_universes);
                                   phase1 = (uu___453_14084.phase1);
                                   failhard = (uu___453_14084.failhard);
                                   nosynth = (uu___453_14084.nosynth);
                                   uvar_subtyping =
                                     (uu___453_14084.uvar_subtyping);
                                   tc_term = (uu___453_14084.tc_term);
                                   type_of = (uu___453_14084.type_of);
                                   universe_of = (uu___453_14084.universe_of);
                                   check_type_of =
                                     (uu___453_14084.check_type_of);
                                   use_bv_sorts =
                                     (uu___453_14084.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___453_14084.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___453_14084.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___453_14084.fv_delta_depths);
                                   proof_ns = (uu___453_14084.proof_ns);
                                   synth_hook = (uu___453_14084.synth_hook);
                                   splice = (uu___453_14084.splice);
                                   postprocess = (uu___453_14084.postprocess);
                                   is_native_tactic =
                                     (uu___453_14084.is_native_tactic);
                                   identifier_info =
                                     (uu___453_14084.identifier_info);
                                   tc_hooks = (uu___453_14084.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___453_14084.nbe);
                                   strict_args_tab =
                                     (uu___453_14084.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14118  ->
             let uu____14119 =
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
             match uu____14119 with
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
                             ((let uu____14299 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14299
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14315 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14315
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14347,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14389 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14419  ->
                  match uu____14419 with
                  | (m,uu____14427) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14389 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___498_14442 = env  in
               {
                 solver = (uu___498_14442.solver);
                 range = (uu___498_14442.range);
                 curmodule = (uu___498_14442.curmodule);
                 gamma = (uu___498_14442.gamma);
                 gamma_sig = (uu___498_14442.gamma_sig);
                 gamma_cache = (uu___498_14442.gamma_cache);
                 modules = (uu___498_14442.modules);
                 expected_typ = (uu___498_14442.expected_typ);
                 sigtab = (uu___498_14442.sigtab);
                 attrtab = (uu___498_14442.attrtab);
                 is_pattern = (uu___498_14442.is_pattern);
                 instantiate_imp = (uu___498_14442.instantiate_imp);
                 effects = (uu___498_14442.effects);
                 generalize = (uu___498_14442.generalize);
                 letrecs = (uu___498_14442.letrecs);
                 top_level = (uu___498_14442.top_level);
                 check_uvars = (uu___498_14442.check_uvars);
                 use_eq = (uu___498_14442.use_eq);
                 is_iface = (uu___498_14442.is_iface);
                 admit = (uu___498_14442.admit);
                 lax = (uu___498_14442.lax);
                 lax_universes = (uu___498_14442.lax_universes);
                 phase1 = (uu___498_14442.phase1);
                 failhard = (uu___498_14442.failhard);
                 nosynth = (uu___498_14442.nosynth);
                 uvar_subtyping = (uu___498_14442.uvar_subtyping);
                 tc_term = (uu___498_14442.tc_term);
                 type_of = (uu___498_14442.type_of);
                 universe_of = (uu___498_14442.universe_of);
                 check_type_of = (uu___498_14442.check_type_of);
                 use_bv_sorts = (uu___498_14442.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___498_14442.normalized_eff_names);
                 fv_delta_depths = (uu___498_14442.fv_delta_depths);
                 proof_ns = (uu___498_14442.proof_ns);
                 synth_hook = (uu___498_14442.synth_hook);
                 splice = (uu___498_14442.splice);
                 postprocess = (uu___498_14442.postprocess);
                 is_native_tactic = (uu___498_14442.is_native_tactic);
                 identifier_info = (uu___498_14442.identifier_info);
                 tc_hooks = (uu___498_14442.tc_hooks);
                 dsenv = (uu___498_14442.dsenv);
                 nbe = (uu___498_14442.nbe);
                 strict_args_tab = (uu___498_14442.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14459,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___507_14475 = env  in
               {
                 solver = (uu___507_14475.solver);
                 range = (uu___507_14475.range);
                 curmodule = (uu___507_14475.curmodule);
                 gamma = (uu___507_14475.gamma);
                 gamma_sig = (uu___507_14475.gamma_sig);
                 gamma_cache = (uu___507_14475.gamma_cache);
                 modules = (uu___507_14475.modules);
                 expected_typ = (uu___507_14475.expected_typ);
                 sigtab = (uu___507_14475.sigtab);
                 attrtab = (uu___507_14475.attrtab);
                 is_pattern = (uu___507_14475.is_pattern);
                 instantiate_imp = (uu___507_14475.instantiate_imp);
                 effects = (uu___507_14475.effects);
                 generalize = (uu___507_14475.generalize);
                 letrecs = (uu___507_14475.letrecs);
                 top_level = (uu___507_14475.top_level);
                 check_uvars = (uu___507_14475.check_uvars);
                 use_eq = (uu___507_14475.use_eq);
                 is_iface = (uu___507_14475.is_iface);
                 admit = (uu___507_14475.admit);
                 lax = (uu___507_14475.lax);
                 lax_universes = (uu___507_14475.lax_universes);
                 phase1 = (uu___507_14475.phase1);
                 failhard = (uu___507_14475.failhard);
                 nosynth = (uu___507_14475.nosynth);
                 uvar_subtyping = (uu___507_14475.uvar_subtyping);
                 tc_term = (uu___507_14475.tc_term);
                 type_of = (uu___507_14475.type_of);
                 universe_of = (uu___507_14475.universe_of);
                 check_type_of = (uu___507_14475.check_type_of);
                 use_bv_sorts = (uu___507_14475.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___507_14475.normalized_eff_names);
                 fv_delta_depths = (uu___507_14475.fv_delta_depths);
                 proof_ns = (uu___507_14475.proof_ns);
                 synth_hook = (uu___507_14475.synth_hook);
                 splice = (uu___507_14475.splice);
                 postprocess = (uu___507_14475.postprocess);
                 is_native_tactic = (uu___507_14475.is_native_tactic);
                 identifier_info = (uu___507_14475.identifier_info);
                 tc_hooks = (uu___507_14475.tc_hooks);
                 dsenv = (uu___507_14475.dsenv);
                 nbe = (uu___507_14475.nbe);
                 strict_args_tab = (uu___507_14475.strict_args_tab)
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
        (let uu___514_14518 = e  in
         {
           solver = (uu___514_14518.solver);
           range = r;
           curmodule = (uu___514_14518.curmodule);
           gamma = (uu___514_14518.gamma);
           gamma_sig = (uu___514_14518.gamma_sig);
           gamma_cache = (uu___514_14518.gamma_cache);
           modules = (uu___514_14518.modules);
           expected_typ = (uu___514_14518.expected_typ);
           sigtab = (uu___514_14518.sigtab);
           attrtab = (uu___514_14518.attrtab);
           is_pattern = (uu___514_14518.is_pattern);
           instantiate_imp = (uu___514_14518.instantiate_imp);
           effects = (uu___514_14518.effects);
           generalize = (uu___514_14518.generalize);
           letrecs = (uu___514_14518.letrecs);
           top_level = (uu___514_14518.top_level);
           check_uvars = (uu___514_14518.check_uvars);
           use_eq = (uu___514_14518.use_eq);
           is_iface = (uu___514_14518.is_iface);
           admit = (uu___514_14518.admit);
           lax = (uu___514_14518.lax);
           lax_universes = (uu___514_14518.lax_universes);
           phase1 = (uu___514_14518.phase1);
           failhard = (uu___514_14518.failhard);
           nosynth = (uu___514_14518.nosynth);
           uvar_subtyping = (uu___514_14518.uvar_subtyping);
           tc_term = (uu___514_14518.tc_term);
           type_of = (uu___514_14518.type_of);
           universe_of = (uu___514_14518.universe_of);
           check_type_of = (uu___514_14518.check_type_of);
           use_bv_sorts = (uu___514_14518.use_bv_sorts);
           qtbl_name_and_index = (uu___514_14518.qtbl_name_and_index);
           normalized_eff_names = (uu___514_14518.normalized_eff_names);
           fv_delta_depths = (uu___514_14518.fv_delta_depths);
           proof_ns = (uu___514_14518.proof_ns);
           synth_hook = (uu___514_14518.synth_hook);
           splice = (uu___514_14518.splice);
           postprocess = (uu___514_14518.postprocess);
           is_native_tactic = (uu___514_14518.is_native_tactic);
           identifier_info = (uu___514_14518.identifier_info);
           tc_hooks = (uu___514_14518.tc_hooks);
           dsenv = (uu___514_14518.dsenv);
           nbe = (uu___514_14518.nbe);
           strict_args_tab = (uu___514_14518.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14538 =
        let uu____14539 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14539 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14538
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14594 =
          let uu____14595 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14595 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14594
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14650 =
          let uu____14651 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14651 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14650
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14706 =
        let uu____14707 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14707 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14706
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___531_14771 = env  in
      {
        solver = (uu___531_14771.solver);
        range = (uu___531_14771.range);
        curmodule = lid;
        gamma = (uu___531_14771.gamma);
        gamma_sig = (uu___531_14771.gamma_sig);
        gamma_cache = (uu___531_14771.gamma_cache);
        modules = (uu___531_14771.modules);
        expected_typ = (uu___531_14771.expected_typ);
        sigtab = (uu___531_14771.sigtab);
        attrtab = (uu___531_14771.attrtab);
        is_pattern = (uu___531_14771.is_pattern);
        instantiate_imp = (uu___531_14771.instantiate_imp);
        effects = (uu___531_14771.effects);
        generalize = (uu___531_14771.generalize);
        letrecs = (uu___531_14771.letrecs);
        top_level = (uu___531_14771.top_level);
        check_uvars = (uu___531_14771.check_uvars);
        use_eq = (uu___531_14771.use_eq);
        is_iface = (uu___531_14771.is_iface);
        admit = (uu___531_14771.admit);
        lax = (uu___531_14771.lax);
        lax_universes = (uu___531_14771.lax_universes);
        phase1 = (uu___531_14771.phase1);
        failhard = (uu___531_14771.failhard);
        nosynth = (uu___531_14771.nosynth);
        uvar_subtyping = (uu___531_14771.uvar_subtyping);
        tc_term = (uu___531_14771.tc_term);
        type_of = (uu___531_14771.type_of);
        universe_of = (uu___531_14771.universe_of);
        check_type_of = (uu___531_14771.check_type_of);
        use_bv_sorts = (uu___531_14771.use_bv_sorts);
        qtbl_name_and_index = (uu___531_14771.qtbl_name_and_index);
        normalized_eff_names = (uu___531_14771.normalized_eff_names);
        fv_delta_depths = (uu___531_14771.fv_delta_depths);
        proof_ns = (uu___531_14771.proof_ns);
        synth_hook = (uu___531_14771.synth_hook);
        splice = (uu___531_14771.splice);
        postprocess = (uu___531_14771.postprocess);
        is_native_tactic = (uu___531_14771.is_native_tactic);
        identifier_info = (uu___531_14771.identifier_info);
        tc_hooks = (uu___531_14771.tc_hooks);
        dsenv = (uu___531_14771.dsenv);
        nbe = (uu___531_14771.nbe);
        strict_args_tab = (uu___531_14771.strict_args_tab)
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
      let uu____14802 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14802
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14815 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14815)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14830 =
      let uu____14832 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14832  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14830)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14841  ->
    let uu____14842 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14842
  
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
      | ((formals,t),uu____14942) ->
          let vs = mk_univ_subst formals us  in
          let uu____14966 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14966)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14983  ->
    match uu___1_14983 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15009  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15029 = inst_tscheme t  in
      match uu____15029 with
      | (us,t1) ->
          let uu____15040 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15040)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____15061  ->
          match uu____15061 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____15083 =
                         let uu____15085 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____15089 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____15093 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____15095 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____15085 uu____15089 uu____15093 uu____15095
                          in
                       failwith uu____15083)
                    else ();
                    (let uu____15100 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____15100))
               | uu____15109 ->
                   let uu____15110 =
                     let uu____15112 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____15112
                      in
                   failwith uu____15110)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15124 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15135 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15146 -> false
  
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
             | ([],uu____15194) -> Maybe
             | (uu____15201,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15221 -> No  in
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
          let uu____15315 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15315 with
          | FStar_Pervasives_Native.None  ->
              let uu____15338 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15382  ->
                     match uu___2_15382 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15421 = FStar_Ident.lid_equals lid l  in
                         if uu____15421
                         then
                           let uu____15444 =
                             let uu____15463 =
                               let uu____15478 = inst_tscheme t  in
                               FStar_Util.Inl uu____15478  in
                             let uu____15493 = FStar_Ident.range_of_lid l  in
                             (uu____15463, uu____15493)  in
                           FStar_Pervasives_Native.Some uu____15444
                         else FStar_Pervasives_Native.None
                     | uu____15546 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15338
                (fun uu____15584  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15593  ->
                        match uu___3_15593 with
                        | (uu____15596,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15598);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15599;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15600;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15601;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15602;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15622 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15622
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
                                  uu____15674 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15681 -> cache t  in
                            let uu____15682 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15682 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15688 =
                                   let uu____15689 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15689)
                                    in
                                 maybe_cache uu____15688)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15760 = find_in_sigtab env lid  in
         match uu____15760 with
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
      let uu____15841 = lookup_qname env lid  in
      match uu____15841 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15862,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15976 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15976 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16021 =
          let uu____16024 = lookup_attr env1 attr  in se1 :: uu____16024  in
        FStar_Util.smap_add (attrtab env1) attr uu____16021  in
      FStar_List.iter
        (fun attr  ->
           let uu____16034 =
             let uu____16035 = FStar_Syntax_Subst.compress attr  in
             uu____16035.FStar_Syntax_Syntax.n  in
           match uu____16034 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16039 =
                 let uu____16041 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16041.FStar_Ident.str  in
               add_one1 env se uu____16039
           | uu____16042 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16065) ->
          add_sigelts env ses
      | uu____16074 ->
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
            | uu____16089 -> ()))

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
        (fun uu___4_16121  ->
           match uu___4_16121 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16139 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16201,lb::[]),uu____16203) ->
            let uu____16212 =
              let uu____16221 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16230 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16221, uu____16230)  in
            FStar_Pervasives_Native.Some uu____16212
        | FStar_Syntax_Syntax.Sig_let ((uu____16243,lbs),uu____16245) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16277 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16290 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16290
                     then
                       let uu____16303 =
                         let uu____16312 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16321 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16312, uu____16321)  in
                       FStar_Pervasives_Native.Some uu____16303
                     else FStar_Pervasives_Native.None)
        | uu____16344 -> FStar_Pervasives_Native.None
  
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
          let uu____16404 =
            let uu____16413 =
              let uu____16418 =
                let uu____16419 =
                  let uu____16422 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____16422
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____16419)  in
              inst_tscheme1 uu____16418  in
            (uu____16413, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16404
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16444,uu____16445) ->
          let uu____16450 =
            let uu____16459 =
              let uu____16464 =
                let uu____16465 =
                  let uu____16468 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16468  in
                (us, uu____16465)  in
              inst_tscheme1 uu____16464  in
            (uu____16459, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16450
      | uu____16487 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16576 =
          match uu____16576 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16672,uvs,t,uu____16675,uu____16676,uu____16677);
                      FStar_Syntax_Syntax.sigrng = uu____16678;
                      FStar_Syntax_Syntax.sigquals = uu____16679;
                      FStar_Syntax_Syntax.sigmeta = uu____16680;
                      FStar_Syntax_Syntax.sigattrs = uu____16681;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16704 =
                     let uu____16713 = inst_tscheme1 (uvs, t)  in
                     (uu____16713, rng)  in
                   FStar_Pervasives_Native.Some uu____16704
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16737;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16739;
                      FStar_Syntax_Syntax.sigattrs = uu____16740;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16757 =
                     let uu____16759 = in_cur_mod env l  in uu____16759 = Yes
                      in
                   if uu____16757
                   then
                     let uu____16771 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16771
                      then
                        let uu____16787 =
                          let uu____16796 = inst_tscheme1 (uvs, t)  in
                          (uu____16796, rng)  in
                        FStar_Pervasives_Native.Some uu____16787
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16829 =
                        let uu____16838 = inst_tscheme1 (uvs, t)  in
                        (uu____16838, rng)  in
                      FStar_Pervasives_Native.Some uu____16829)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16863,uu____16864);
                      FStar_Syntax_Syntax.sigrng = uu____16865;
                      FStar_Syntax_Syntax.sigquals = uu____16866;
                      FStar_Syntax_Syntax.sigmeta = uu____16867;
                      FStar_Syntax_Syntax.sigattrs = uu____16868;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16909 =
                          let uu____16918 = inst_tscheme1 (uvs, k)  in
                          (uu____16918, rng)  in
                        FStar_Pervasives_Native.Some uu____16909
                    | uu____16939 ->
                        let uu____16940 =
                          let uu____16949 =
                            let uu____16954 =
                              let uu____16955 =
                                let uu____16958 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16958
                                 in
                              (uvs, uu____16955)  in
                            inst_tscheme1 uu____16954  in
                          (uu____16949, rng)  in
                        FStar_Pervasives_Native.Some uu____16940)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16981,uu____16982);
                      FStar_Syntax_Syntax.sigrng = uu____16983;
                      FStar_Syntax_Syntax.sigquals = uu____16984;
                      FStar_Syntax_Syntax.sigmeta = uu____16985;
                      FStar_Syntax_Syntax.sigattrs = uu____16986;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17028 =
                          let uu____17037 = inst_tscheme_with (uvs, k) us  in
                          (uu____17037, rng)  in
                        FStar_Pervasives_Native.Some uu____17028
                    | uu____17058 ->
                        let uu____17059 =
                          let uu____17068 =
                            let uu____17073 =
                              let uu____17074 =
                                let uu____17077 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17077
                                 in
                              (uvs, uu____17074)  in
                            inst_tscheme_with uu____17073 us  in
                          (uu____17068, rng)  in
                        FStar_Pervasives_Native.Some uu____17059)
               | FStar_Util.Inr se ->
                   let uu____17113 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17134;
                          FStar_Syntax_Syntax.sigrng = uu____17135;
                          FStar_Syntax_Syntax.sigquals = uu____17136;
                          FStar_Syntax_Syntax.sigmeta = uu____17137;
                          FStar_Syntax_Syntax.sigattrs = uu____17138;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17153 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____17113
                     (FStar_Util.map_option
                        (fun uu____17201  ->
                           match uu____17201 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17232 =
          let uu____17243 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17243 mapper  in
        match uu____17232 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17317 =
              let uu____17328 =
                let uu____17335 =
                  let uu___858_17338 = t  in
                  let uu____17339 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_17338.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17339;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_17338.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17335)  in
              (uu____17328, r)  in
            FStar_Pervasives_Native.Some uu____17317
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17388 = lookup_qname env l  in
      match uu____17388 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17409 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17463 = try_lookup_bv env bv  in
      match uu____17463 with
      | FStar_Pervasives_Native.None  ->
          let uu____17478 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17478 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17494 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17495 =
            let uu____17496 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17496  in
          (uu____17494, uu____17495)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17518 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17518 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17584 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17584  in
          let uu____17585 =
            let uu____17594 =
              let uu____17599 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17599)  in
            (uu____17594, r1)  in
          FStar_Pervasives_Native.Some uu____17585
  
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
        let uu____17634 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17634 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17667,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17692 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17692  in
            let uu____17693 =
              let uu____17698 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17698, r1)  in
            FStar_Pervasives_Native.Some uu____17693
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17722 = try_lookup_lid env l  in
      match uu____17722 with
      | FStar_Pervasives_Native.None  ->
          let uu____17749 = name_not_found l  in
          let uu____17755 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17749 uu____17755
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17798  ->
              match uu___5_17798 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17802 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17823 = lookup_qname env lid  in
      match uu____17823 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17832,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17835;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17837;
              FStar_Syntax_Syntax.sigattrs = uu____17838;_},FStar_Pervasives_Native.None
            ),uu____17839)
          ->
          let uu____17888 =
            let uu____17895 =
              let uu____17896 =
                let uu____17899 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17899 t  in
              (uvs, uu____17896)  in
            (uu____17895, q)  in
          FStar_Pervasives_Native.Some uu____17888
      | uu____17912 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17934 = lookup_qname env lid  in
      match uu____17934 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17939,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17942;
              FStar_Syntax_Syntax.sigquals = uu____17943;
              FStar_Syntax_Syntax.sigmeta = uu____17944;
              FStar_Syntax_Syntax.sigattrs = uu____17945;_},FStar_Pervasives_Native.None
            ),uu____17946)
          ->
          let uu____17995 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17995 (uvs, t)
      | uu____18000 ->
          let uu____18001 = name_not_found lid  in
          let uu____18007 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18001 uu____18007
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18027 = lookup_qname env lid  in
      match uu____18027 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18032,uvs,t,uu____18035,uu____18036,uu____18037);
              FStar_Syntax_Syntax.sigrng = uu____18038;
              FStar_Syntax_Syntax.sigquals = uu____18039;
              FStar_Syntax_Syntax.sigmeta = uu____18040;
              FStar_Syntax_Syntax.sigattrs = uu____18041;_},FStar_Pervasives_Native.None
            ),uu____18042)
          ->
          let uu____18097 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18097 (uvs, t)
      | uu____18102 ->
          let uu____18103 = name_not_found lid  in
          let uu____18109 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18103 uu____18109
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18132 = lookup_qname env lid  in
      match uu____18132 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18140,uu____18141,uu____18142,uu____18143,uu____18144,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18146;
              FStar_Syntax_Syntax.sigquals = uu____18147;
              FStar_Syntax_Syntax.sigmeta = uu____18148;
              FStar_Syntax_Syntax.sigattrs = uu____18149;_},uu____18150),uu____18151)
          -> (true, dcs)
      | uu____18214 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18230 = lookup_qname env lid  in
      match uu____18230 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18231,uu____18232,uu____18233,l,uu____18235,uu____18236);
              FStar_Syntax_Syntax.sigrng = uu____18237;
              FStar_Syntax_Syntax.sigquals = uu____18238;
              FStar_Syntax_Syntax.sigmeta = uu____18239;
              FStar_Syntax_Syntax.sigattrs = uu____18240;_},uu____18241),uu____18242)
          -> l
      | uu____18299 ->
          let uu____18300 =
            let uu____18302 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18302  in
          failwith uu____18300
  
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
                    (fun uu___6_18374  ->
                       match uu___6_18374 with
                       | Eager_unfolding_only (true ) ->
                           FStar_All.pipe_right attrs
                             (FStar_Util.for_some
                                (fun at  ->
                                   FStar_Syntax_Util.is_fvar
                                     FStar_Parser_Const.unfold_for_smt_attr
                                     at))
                       | uu____18382 -> false)))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18395)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18452) when
                   (visible se.FStar_Syntax_Syntax.sigquals
                      se.FStar_Syntax_Syntax.sigattrs)
                     && ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18476 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18476
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18511 -> FStar_Pervasives_Native.None)
          | uu____18520 -> FStar_Pervasives_Native.None
  
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
        let uu____18582 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18582
  
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
        let uu____18615 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18615
  
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
             (FStar_Util.Inl uu____18667,uu____18668) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18717),uu____18718) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18767 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18785 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18795 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18812 ->
                  let uu____18819 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18819
              | FStar_Syntax_Syntax.Sig_let ((uu____18820,lbs),uu____18822)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18838 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18838
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18845 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18853 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18854 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18861 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18862 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18863 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18864 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18877 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18895 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18895
           (fun d_opt  ->
              let uu____18908 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18908
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18918 =
                   let uu____18921 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18921  in
                 match uu____18918 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18922 =
                       let uu____18924 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18924
                        in
                     failwith uu____18922
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18929 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18929
                       then
                         let uu____18932 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18934 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18936 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18932 uu____18934 uu____18936
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
        (FStar_Util.Inr (se,uu____18961),uu____18962) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19011 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19033),uu____19034) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19083 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19105 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19105
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19128 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19128 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19152 =
                      let uu____19153 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19153.FStar_Syntax_Syntax.n  in
                    match uu____19152 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19158 -> false))
  
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
        let uu____19195 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19195.FStar_Ident.str  in
      let uu____19196 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19196 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19224 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19224  in
          let res =
            match attrs with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some attrs1 ->
                FStar_Util.find_map attrs1
                  (fun x  ->
                     let uu____19252 =
                       FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                         FStar_Parser_Const.strict_on_arguments_attr
                        in
                     FStar_Pervasives_Native.fst uu____19252)
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
      let uu____19302 = lookup_qname env ftv  in
      match uu____19302 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19306) ->
          let uu____19351 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____19351 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19372,t),r) ->
               let uu____19387 =
                 let uu____19388 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19388 t  in
               FStar_Pervasives_Native.Some uu____19387)
      | uu____19389 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19401 = try_lookup_effect_lid env ftv  in
      match uu____19401 with
      | FStar_Pervasives_Native.None  ->
          let uu____19404 = name_not_found ftv  in
          let uu____19410 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19404 uu____19410
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
        let uu____19434 = lookup_qname env lid0  in
        match uu____19434 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19445);
                FStar_Syntax_Syntax.sigrng = uu____19446;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19448;
                FStar_Syntax_Syntax.sigattrs = uu____19449;_},FStar_Pervasives_Native.None
              ),uu____19450)
            ->
            let lid1 =
              let uu____19504 =
                let uu____19505 = FStar_Ident.range_of_lid lid  in
                let uu____19506 =
                  let uu____19507 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19507  in
                FStar_Range.set_use_range uu____19505 uu____19506  in
              FStar_Ident.set_lid_range lid uu____19504  in
            let uu____19508 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___7_19514  ->
                      match uu___7_19514 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19517 -> false))
               in
            if uu____19508
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19536 =
                      let uu____19538 =
                        let uu____19540 = get_range env  in
                        FStar_Range.string_of_range uu____19540  in
                      let uu____19541 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19543 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19538 uu____19541 uu____19543
                       in
                    failwith uu____19536)
                  in
               match (binders, univs1) with
               | ([],uu____19564) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19590,uu____19591::uu____19592::uu____19593) ->
                   let uu____19614 =
                     let uu____19616 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19618 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19616 uu____19618
                      in
                   failwith uu____19614
               | uu____19629 ->
                   let uu____19644 =
                     let uu____19649 =
                       let uu____19650 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19650)  in
                     inst_tscheme_with uu____19649 insts  in
                   (match uu____19644 with
                    | (uu____19663,t) ->
                        let t1 =
                          let uu____19666 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19666 t  in
                        let uu____19667 =
                          let uu____19668 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19668.FStar_Syntax_Syntax.n  in
                        (match uu____19667 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19703 -> failwith "Impossible")))
        | uu____19711 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19735 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19735 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19748,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19755 = find1 l2  in
            (match uu____19755 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19762 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19762 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19766 = find1 l  in
            (match uu____19766 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19771 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19771
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19786 = lookup_qname env l1  in
      match uu____19786 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19789;
              FStar_Syntax_Syntax.sigrng = uu____19790;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19792;
              FStar_Syntax_Syntax.sigattrs = uu____19793;_},uu____19794),uu____19795)
          -> q
      | uu____19846 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19870 =
          let uu____19871 =
            let uu____19873 = FStar_Util.string_of_int i  in
            let uu____19875 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19873 uu____19875
             in
          failwith uu____19871  in
        let uu____19878 = lookup_datacon env lid  in
        match uu____19878 with
        | (uu____19883,t) ->
            let uu____19885 =
              let uu____19886 = FStar_Syntax_Subst.compress t  in
              uu____19886.FStar_Syntax_Syntax.n  in
            (match uu____19885 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19890) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19934 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19934
                      FStar_Pervasives_Native.fst)
             | uu____19945 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19959 = lookup_qname env l  in
      match uu____19959 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19961,uu____19962,uu____19963);
              FStar_Syntax_Syntax.sigrng = uu____19964;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19966;
              FStar_Syntax_Syntax.sigattrs = uu____19967;_},uu____19968),uu____19969)
          ->
          FStar_Util.for_some
            (fun uu___8_20022  ->
               match uu___8_20022 with
               | FStar_Syntax_Syntax.Projector uu____20024 -> true
               | uu____20030 -> false) quals
      | uu____20032 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20046 = lookup_qname env lid  in
      match uu____20046 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20048,uu____20049,uu____20050,uu____20051,uu____20052,uu____20053);
              FStar_Syntax_Syntax.sigrng = uu____20054;
              FStar_Syntax_Syntax.sigquals = uu____20055;
              FStar_Syntax_Syntax.sigmeta = uu____20056;
              FStar_Syntax_Syntax.sigattrs = uu____20057;_},uu____20058),uu____20059)
          -> true
      | uu____20117 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20131 = lookup_qname env lid  in
      match uu____20131 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20133,uu____20134,uu____20135,uu____20136,uu____20137,uu____20138);
              FStar_Syntax_Syntax.sigrng = uu____20139;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20141;
              FStar_Syntax_Syntax.sigattrs = uu____20142;_},uu____20143),uu____20144)
          ->
          FStar_Util.for_some
            (fun uu___9_20205  ->
               match uu___9_20205 with
               | FStar_Syntax_Syntax.RecordType uu____20207 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20217 -> true
               | uu____20227 -> false) quals
      | uu____20229 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20239,uu____20240);
            FStar_Syntax_Syntax.sigrng = uu____20241;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20243;
            FStar_Syntax_Syntax.sigattrs = uu____20244;_},uu____20245),uu____20246)
        ->
        FStar_Util.for_some
          (fun uu___10_20303  ->
             match uu___10_20303 with
             | FStar_Syntax_Syntax.Action uu____20305 -> true
             | uu____20307 -> false) quals
    | uu____20309 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20323 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20323
  
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
      let uu____20340 =
        let uu____20341 = FStar_Syntax_Util.un_uinst head1  in
        uu____20341.FStar_Syntax_Syntax.n  in
      match uu____20340 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20347 ->
               true
           | uu____20350 -> false)
      | uu____20352 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20366 = lookup_qname env l  in
      match uu____20366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20369),uu____20370) ->
          FStar_Util.for_some
            (fun uu___11_20418  ->
               match uu___11_20418 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20421 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20423 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20499 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20517) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20535 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20543 ->
                 FStar_Pervasives_Native.Some true
             | uu____20562 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20565 =
        let uu____20569 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20569 mapper  in
      match uu____20565 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20629 = lookup_qname env lid  in
      match uu____20629 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20633,uu____20634,tps,uu____20636,uu____20637,uu____20638);
              FStar_Syntax_Syntax.sigrng = uu____20639;
              FStar_Syntax_Syntax.sigquals = uu____20640;
              FStar_Syntax_Syntax.sigmeta = uu____20641;
              FStar_Syntax_Syntax.sigattrs = uu____20642;_},uu____20643),uu____20644)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20710 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20756  ->
              match uu____20756 with
              | (d,uu____20765) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20781 = effect_decl_opt env l  in
      match uu____20781 with
      | FStar_Pervasives_Native.None  ->
          let uu____20796 = name_not_found l  in
          let uu____20802 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20796 uu____20802
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20825  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20844  ->
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
        let uu____20876 = FStar_Ident.lid_equals l1 l2  in
        if uu____20876
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20887 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20887
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20898 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20951  ->
                        match uu____20951 with
                        | (m1,m2,uu____20965,uu____20966,uu____20967) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20898 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20984 =
                    let uu____20990 =
                      let uu____20992 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20994 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20992
                        uu____20994
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20990)
                     in
                  FStar_Errors.raise_error uu____20984 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21004,uu____21005,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21039 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21039
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
  'Auu____21059 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21059) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21088 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21114  ->
                match uu____21114 with
                | (d,uu____21121) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21088 with
      | FStar_Pervasives_Native.None  ->
          let uu____21132 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21132
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21147 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____21147 with
           | (uu____21162,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21180)::(wp,uu____21182)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21238 -> failwith "Impossible"))
  
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
            let uu___1521_21288 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1521_21288.order);
              joins = (uu___1521_21288.joins)
            }  in
          let uu___1524_21297 = env  in
          {
            solver = (uu___1524_21297.solver);
            range = (uu___1524_21297.range);
            curmodule = (uu___1524_21297.curmodule);
            gamma = (uu___1524_21297.gamma);
            gamma_sig = (uu___1524_21297.gamma_sig);
            gamma_cache = (uu___1524_21297.gamma_cache);
            modules = (uu___1524_21297.modules);
            expected_typ = (uu___1524_21297.expected_typ);
            sigtab = (uu___1524_21297.sigtab);
            attrtab = (uu___1524_21297.attrtab);
            is_pattern = (uu___1524_21297.is_pattern);
            instantiate_imp = (uu___1524_21297.instantiate_imp);
            effects;
            generalize = (uu___1524_21297.generalize);
            letrecs = (uu___1524_21297.letrecs);
            top_level = (uu___1524_21297.top_level);
            check_uvars = (uu___1524_21297.check_uvars);
            use_eq = (uu___1524_21297.use_eq);
            is_iface = (uu___1524_21297.is_iface);
            admit = (uu___1524_21297.admit);
            lax = (uu___1524_21297.lax);
            lax_universes = (uu___1524_21297.lax_universes);
            phase1 = (uu___1524_21297.phase1);
            failhard = (uu___1524_21297.failhard);
            nosynth = (uu___1524_21297.nosynth);
            uvar_subtyping = (uu___1524_21297.uvar_subtyping);
            tc_term = (uu___1524_21297.tc_term);
            type_of = (uu___1524_21297.type_of);
            universe_of = (uu___1524_21297.universe_of);
            check_type_of = (uu___1524_21297.check_type_of);
            use_bv_sorts = (uu___1524_21297.use_bv_sorts);
            qtbl_name_and_index = (uu___1524_21297.qtbl_name_and_index);
            normalized_eff_names = (uu___1524_21297.normalized_eff_names);
            fv_delta_depths = (uu___1524_21297.fv_delta_depths);
            proof_ns = (uu___1524_21297.proof_ns);
            synth_hook = (uu___1524_21297.synth_hook);
            splice = (uu___1524_21297.splice);
            postprocess = (uu___1524_21297.postprocess);
            is_native_tactic = (uu___1524_21297.is_native_tactic);
            identifier_info = (uu___1524_21297.identifier_info);
            tc_hooks = (uu___1524_21297.tc_hooks);
            dsenv = (uu___1524_21297.dsenv);
            nbe = (uu___1524_21297.nbe);
            strict_args_tab = (uu___1524_21297.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____21327 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____21327  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____21485 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____21486 = l1 u t wp e  in
                                l2 u t uu____21485 uu____21486))
                | uu____21487 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21559 = inst_tscheme_with lift_t [u]  in
            match uu____21559 with
            | (uu____21566,lift_t1) ->
                let uu____21568 =
                  let uu____21575 =
                    let uu____21576 =
                      let uu____21593 =
                        let uu____21604 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21613 =
                          let uu____21624 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21624]  in
                        uu____21604 :: uu____21613  in
                      (lift_t1, uu____21593)  in
                    FStar_Syntax_Syntax.Tm_app uu____21576  in
                  FStar_Syntax_Syntax.mk uu____21575  in
                uu____21568 FStar_Pervasives_Native.None
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
            let uu____21734 = inst_tscheme_with lift_t [u]  in
            match uu____21734 with
            | (uu____21741,lift_t1) ->
                let uu____21743 =
                  let uu____21750 =
                    let uu____21751 =
                      let uu____21768 =
                        let uu____21779 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21788 =
                          let uu____21799 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21808 =
                            let uu____21819 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21819]  in
                          uu____21799 :: uu____21808  in
                        uu____21779 :: uu____21788  in
                      (lift_t1, uu____21768)  in
                    FStar_Syntax_Syntax.Tm_app uu____21751  in
                  FStar_Syntax_Syntax.mk uu____21750  in
                uu____21743 FStar_Pervasives_Native.None
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
              let uu____21921 =
                let uu____21922 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21922
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21921  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21931 =
              let uu____21933 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21933  in
            let uu____21934 =
              let uu____21936 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21964 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21964)
                 in
              FStar_Util.dflt "none" uu____21936  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21931
              uu____21934
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21993  ->
                    match uu____21993 with
                    | (e,uu____22001) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____22024 =
            match uu____22024 with
            | (i,j) ->
                let uu____22035 = FStar_Ident.lid_equals i j  in
                if uu____22035
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _22042  -> FStar_Pervasives_Native.Some _22042)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____22071 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____22081 = FStar_Ident.lid_equals i k  in
                        if uu____22081
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____22095 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____22095
                                  then []
                                  else
                                    (let uu____22102 =
                                       let uu____22111 =
                                         find_edge order1 (i, k)  in
                                       let uu____22114 =
                                         find_edge order1 (k, j)  in
                                       (uu____22111, uu____22114)  in
                                     match uu____22102 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____22129 =
                                           compose_edges e1 e2  in
                                         [uu____22129]
                                     | uu____22130 -> [])))))
                 in
              FStar_List.append order1 uu____22071  in
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
                   let uu____22160 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____22163 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____22163
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____22160
                   then
                     let uu____22170 =
                       let uu____22176 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____22176)
                        in
                     let uu____22180 = get_range env  in
                     FStar_Errors.raise_error uu____22170 uu____22180
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____22258 = FStar_Ident.lid_equals i j
                                   in
                                if uu____22258
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____22310 =
                                              let uu____22319 =
                                                find_edge order2 (i, k)  in
                                              let uu____22322 =
                                                find_edge order2 (j, k)  in
                                              (uu____22319, uu____22322)  in
                                            match uu____22310 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____22364,uu____22365)
                                                     ->
                                                     let uu____22372 =
                                                       let uu____22379 =
                                                         let uu____22381 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22381
                                                          in
                                                       let uu____22384 =
                                                         let uu____22386 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22386
                                                          in
                                                       (uu____22379,
                                                         uu____22384)
                                                        in
                                                     (match uu____22372 with
                                                      | (true ,true ) ->
                                                          let uu____22403 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____22403
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
                                            | uu____22446 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1651_22519 = env.effects  in
              { decls = (uu___1651_22519.decls); order = order2; joins }  in
            let uu___1654_22520 = env  in
            {
              solver = (uu___1654_22520.solver);
              range = (uu___1654_22520.range);
              curmodule = (uu___1654_22520.curmodule);
              gamma = (uu___1654_22520.gamma);
              gamma_sig = (uu___1654_22520.gamma_sig);
              gamma_cache = (uu___1654_22520.gamma_cache);
              modules = (uu___1654_22520.modules);
              expected_typ = (uu___1654_22520.expected_typ);
              sigtab = (uu___1654_22520.sigtab);
              attrtab = (uu___1654_22520.attrtab);
              is_pattern = (uu___1654_22520.is_pattern);
              instantiate_imp = (uu___1654_22520.instantiate_imp);
              effects;
              generalize = (uu___1654_22520.generalize);
              letrecs = (uu___1654_22520.letrecs);
              top_level = (uu___1654_22520.top_level);
              check_uvars = (uu___1654_22520.check_uvars);
              use_eq = (uu___1654_22520.use_eq);
              is_iface = (uu___1654_22520.is_iface);
              admit = (uu___1654_22520.admit);
              lax = (uu___1654_22520.lax);
              lax_universes = (uu___1654_22520.lax_universes);
              phase1 = (uu___1654_22520.phase1);
              failhard = (uu___1654_22520.failhard);
              nosynth = (uu___1654_22520.nosynth);
              uvar_subtyping = (uu___1654_22520.uvar_subtyping);
              tc_term = (uu___1654_22520.tc_term);
              type_of = (uu___1654_22520.type_of);
              universe_of = (uu___1654_22520.universe_of);
              check_type_of = (uu___1654_22520.check_type_of);
              use_bv_sorts = (uu___1654_22520.use_bv_sorts);
              qtbl_name_and_index = (uu___1654_22520.qtbl_name_and_index);
              normalized_eff_names = (uu___1654_22520.normalized_eff_names);
              fv_delta_depths = (uu___1654_22520.fv_delta_depths);
              proof_ns = (uu___1654_22520.proof_ns);
              synth_hook = (uu___1654_22520.synth_hook);
              splice = (uu___1654_22520.splice);
              postprocess = (uu___1654_22520.postprocess);
              is_native_tactic = (uu___1654_22520.is_native_tactic);
              identifier_info = (uu___1654_22520.identifier_info);
              tc_hooks = (uu___1654_22520.tc_hooks);
              dsenv = (uu___1654_22520.dsenv);
              nbe = (uu___1654_22520.nbe);
              strict_args_tab = (uu___1654_22520.strict_args_tab)
            }))
      | uu____22521 -> env
  
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
        | uu____22550 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22563 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22563 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22580 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22580 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22605 =
                     let uu____22611 =
                       let uu____22613 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22621 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22632 =
                         let uu____22634 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22634  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22613 uu____22621 uu____22632
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22611)
                      in
                   FStar_Errors.raise_error uu____22605
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22642 =
                     let uu____22653 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22653 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22690  ->
                        fun uu____22691  ->
                          match (uu____22690, uu____22691) with
                          | ((x,uu____22721),(t,uu____22723)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22642
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22754 =
                     let uu___1692_22755 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1692_22755.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1692_22755.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1692_22755.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1692_22755.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22754
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22767 .
    'Auu____22767 ->
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
          let uu____22797 = effect_decl_opt env effect_name  in
          match uu____22797 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22836 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22859 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22898 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22898
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22903 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22903
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22918 =
                     let uu____22921 = get_range env  in
                     let uu____22922 =
                       let uu____22929 =
                         let uu____22930 =
                           let uu____22947 =
                             let uu____22958 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22958; wp]  in
                           (repr, uu____22947)  in
                         FStar_Syntax_Syntax.Tm_app uu____22930  in
                       FStar_Syntax_Syntax.mk uu____22929  in
                     uu____22922 FStar_Pervasives_Native.None uu____22921  in
                   FStar_Pervasives_Native.Some uu____22918)
  
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
      | uu____23102 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23117 =
        let uu____23118 = FStar_Syntax_Subst.compress t  in
        uu____23118.FStar_Syntax_Syntax.n  in
      match uu____23117 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23122,c) ->
          is_reifiable_comp env c
      | uu____23144 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23164 =
           let uu____23166 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23166  in
         if uu____23164
         then
           let uu____23169 =
             let uu____23175 =
               let uu____23177 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23177
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23175)  in
           let uu____23181 = get_range env  in
           FStar_Errors.raise_error uu____23169 uu____23181
         else ());
        (let uu____23184 = effect_repr_aux true env c u_c  in
         match uu____23184 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1757_23220 = env  in
        {
          solver = (uu___1757_23220.solver);
          range = (uu___1757_23220.range);
          curmodule = (uu___1757_23220.curmodule);
          gamma = (uu___1757_23220.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1757_23220.gamma_cache);
          modules = (uu___1757_23220.modules);
          expected_typ = (uu___1757_23220.expected_typ);
          sigtab = (uu___1757_23220.sigtab);
          attrtab = (uu___1757_23220.attrtab);
          is_pattern = (uu___1757_23220.is_pattern);
          instantiate_imp = (uu___1757_23220.instantiate_imp);
          effects = (uu___1757_23220.effects);
          generalize = (uu___1757_23220.generalize);
          letrecs = (uu___1757_23220.letrecs);
          top_level = (uu___1757_23220.top_level);
          check_uvars = (uu___1757_23220.check_uvars);
          use_eq = (uu___1757_23220.use_eq);
          is_iface = (uu___1757_23220.is_iface);
          admit = (uu___1757_23220.admit);
          lax = (uu___1757_23220.lax);
          lax_universes = (uu___1757_23220.lax_universes);
          phase1 = (uu___1757_23220.phase1);
          failhard = (uu___1757_23220.failhard);
          nosynth = (uu___1757_23220.nosynth);
          uvar_subtyping = (uu___1757_23220.uvar_subtyping);
          tc_term = (uu___1757_23220.tc_term);
          type_of = (uu___1757_23220.type_of);
          universe_of = (uu___1757_23220.universe_of);
          check_type_of = (uu___1757_23220.check_type_of);
          use_bv_sorts = (uu___1757_23220.use_bv_sorts);
          qtbl_name_and_index = (uu___1757_23220.qtbl_name_and_index);
          normalized_eff_names = (uu___1757_23220.normalized_eff_names);
          fv_delta_depths = (uu___1757_23220.fv_delta_depths);
          proof_ns = (uu___1757_23220.proof_ns);
          synth_hook = (uu___1757_23220.synth_hook);
          splice = (uu___1757_23220.splice);
          postprocess = (uu___1757_23220.postprocess);
          is_native_tactic = (uu___1757_23220.is_native_tactic);
          identifier_info = (uu___1757_23220.identifier_info);
          tc_hooks = (uu___1757_23220.tc_hooks);
          dsenv = (uu___1757_23220.dsenv);
          nbe = (uu___1757_23220.nbe);
          strict_args_tab = (uu___1757_23220.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1764_23234 = env  in
      {
        solver = (uu___1764_23234.solver);
        range = (uu___1764_23234.range);
        curmodule = (uu___1764_23234.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1764_23234.gamma_sig);
        gamma_cache = (uu___1764_23234.gamma_cache);
        modules = (uu___1764_23234.modules);
        expected_typ = (uu___1764_23234.expected_typ);
        sigtab = (uu___1764_23234.sigtab);
        attrtab = (uu___1764_23234.attrtab);
        is_pattern = (uu___1764_23234.is_pattern);
        instantiate_imp = (uu___1764_23234.instantiate_imp);
        effects = (uu___1764_23234.effects);
        generalize = (uu___1764_23234.generalize);
        letrecs = (uu___1764_23234.letrecs);
        top_level = (uu___1764_23234.top_level);
        check_uvars = (uu___1764_23234.check_uvars);
        use_eq = (uu___1764_23234.use_eq);
        is_iface = (uu___1764_23234.is_iface);
        admit = (uu___1764_23234.admit);
        lax = (uu___1764_23234.lax);
        lax_universes = (uu___1764_23234.lax_universes);
        phase1 = (uu___1764_23234.phase1);
        failhard = (uu___1764_23234.failhard);
        nosynth = (uu___1764_23234.nosynth);
        uvar_subtyping = (uu___1764_23234.uvar_subtyping);
        tc_term = (uu___1764_23234.tc_term);
        type_of = (uu___1764_23234.type_of);
        universe_of = (uu___1764_23234.universe_of);
        check_type_of = (uu___1764_23234.check_type_of);
        use_bv_sorts = (uu___1764_23234.use_bv_sorts);
        qtbl_name_and_index = (uu___1764_23234.qtbl_name_and_index);
        normalized_eff_names = (uu___1764_23234.normalized_eff_names);
        fv_delta_depths = (uu___1764_23234.fv_delta_depths);
        proof_ns = (uu___1764_23234.proof_ns);
        synth_hook = (uu___1764_23234.synth_hook);
        splice = (uu___1764_23234.splice);
        postprocess = (uu___1764_23234.postprocess);
        is_native_tactic = (uu___1764_23234.is_native_tactic);
        identifier_info = (uu___1764_23234.identifier_info);
        tc_hooks = (uu___1764_23234.tc_hooks);
        dsenv = (uu___1764_23234.dsenv);
        nbe = (uu___1764_23234.nbe);
        strict_args_tab = (uu___1764_23234.strict_args_tab)
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
            (let uu___1777_23292 = env  in
             {
               solver = (uu___1777_23292.solver);
               range = (uu___1777_23292.range);
               curmodule = (uu___1777_23292.curmodule);
               gamma = rest;
               gamma_sig = (uu___1777_23292.gamma_sig);
               gamma_cache = (uu___1777_23292.gamma_cache);
               modules = (uu___1777_23292.modules);
               expected_typ = (uu___1777_23292.expected_typ);
               sigtab = (uu___1777_23292.sigtab);
               attrtab = (uu___1777_23292.attrtab);
               is_pattern = (uu___1777_23292.is_pattern);
               instantiate_imp = (uu___1777_23292.instantiate_imp);
               effects = (uu___1777_23292.effects);
               generalize = (uu___1777_23292.generalize);
               letrecs = (uu___1777_23292.letrecs);
               top_level = (uu___1777_23292.top_level);
               check_uvars = (uu___1777_23292.check_uvars);
               use_eq = (uu___1777_23292.use_eq);
               is_iface = (uu___1777_23292.is_iface);
               admit = (uu___1777_23292.admit);
               lax = (uu___1777_23292.lax);
               lax_universes = (uu___1777_23292.lax_universes);
               phase1 = (uu___1777_23292.phase1);
               failhard = (uu___1777_23292.failhard);
               nosynth = (uu___1777_23292.nosynth);
               uvar_subtyping = (uu___1777_23292.uvar_subtyping);
               tc_term = (uu___1777_23292.tc_term);
               type_of = (uu___1777_23292.type_of);
               universe_of = (uu___1777_23292.universe_of);
               check_type_of = (uu___1777_23292.check_type_of);
               use_bv_sorts = (uu___1777_23292.use_bv_sorts);
               qtbl_name_and_index = (uu___1777_23292.qtbl_name_and_index);
               normalized_eff_names = (uu___1777_23292.normalized_eff_names);
               fv_delta_depths = (uu___1777_23292.fv_delta_depths);
               proof_ns = (uu___1777_23292.proof_ns);
               synth_hook = (uu___1777_23292.synth_hook);
               splice = (uu___1777_23292.splice);
               postprocess = (uu___1777_23292.postprocess);
               is_native_tactic = (uu___1777_23292.is_native_tactic);
               identifier_info = (uu___1777_23292.identifier_info);
               tc_hooks = (uu___1777_23292.tc_hooks);
               dsenv = (uu___1777_23292.dsenv);
               nbe = (uu___1777_23292.nbe);
               strict_args_tab = (uu___1777_23292.strict_args_tab)
             }))
    | uu____23293 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23322  ->
             match uu____23322 with | (x,uu____23330) -> push_bv env1 x) env
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
            let uu___1791_23365 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1791_23365.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1791_23365.FStar_Syntax_Syntax.index);
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
      (let uu___1802_23407 = env  in
       {
         solver = (uu___1802_23407.solver);
         range = (uu___1802_23407.range);
         curmodule = (uu___1802_23407.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1802_23407.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1802_23407.sigtab);
         attrtab = (uu___1802_23407.attrtab);
         is_pattern = (uu___1802_23407.is_pattern);
         instantiate_imp = (uu___1802_23407.instantiate_imp);
         effects = (uu___1802_23407.effects);
         generalize = (uu___1802_23407.generalize);
         letrecs = (uu___1802_23407.letrecs);
         top_level = (uu___1802_23407.top_level);
         check_uvars = (uu___1802_23407.check_uvars);
         use_eq = (uu___1802_23407.use_eq);
         is_iface = (uu___1802_23407.is_iface);
         admit = (uu___1802_23407.admit);
         lax = (uu___1802_23407.lax);
         lax_universes = (uu___1802_23407.lax_universes);
         phase1 = (uu___1802_23407.phase1);
         failhard = (uu___1802_23407.failhard);
         nosynth = (uu___1802_23407.nosynth);
         uvar_subtyping = (uu___1802_23407.uvar_subtyping);
         tc_term = (uu___1802_23407.tc_term);
         type_of = (uu___1802_23407.type_of);
         universe_of = (uu___1802_23407.universe_of);
         check_type_of = (uu___1802_23407.check_type_of);
         use_bv_sorts = (uu___1802_23407.use_bv_sorts);
         qtbl_name_and_index = (uu___1802_23407.qtbl_name_and_index);
         normalized_eff_names = (uu___1802_23407.normalized_eff_names);
         fv_delta_depths = (uu___1802_23407.fv_delta_depths);
         proof_ns = (uu___1802_23407.proof_ns);
         synth_hook = (uu___1802_23407.synth_hook);
         splice = (uu___1802_23407.splice);
         postprocess = (uu___1802_23407.postprocess);
         is_native_tactic = (uu___1802_23407.is_native_tactic);
         identifier_info = (uu___1802_23407.identifier_info);
         tc_hooks = (uu___1802_23407.tc_hooks);
         dsenv = (uu___1802_23407.dsenv);
         nbe = (uu___1802_23407.nbe);
         strict_args_tab = (uu___1802_23407.strict_args_tab)
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
        let uu____23451 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23451 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23479 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23479)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1817_23495 = env  in
      {
        solver = (uu___1817_23495.solver);
        range = (uu___1817_23495.range);
        curmodule = (uu___1817_23495.curmodule);
        gamma = (uu___1817_23495.gamma);
        gamma_sig = (uu___1817_23495.gamma_sig);
        gamma_cache = (uu___1817_23495.gamma_cache);
        modules = (uu___1817_23495.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1817_23495.sigtab);
        attrtab = (uu___1817_23495.attrtab);
        is_pattern = (uu___1817_23495.is_pattern);
        instantiate_imp = (uu___1817_23495.instantiate_imp);
        effects = (uu___1817_23495.effects);
        generalize = (uu___1817_23495.generalize);
        letrecs = (uu___1817_23495.letrecs);
        top_level = (uu___1817_23495.top_level);
        check_uvars = (uu___1817_23495.check_uvars);
        use_eq = false;
        is_iface = (uu___1817_23495.is_iface);
        admit = (uu___1817_23495.admit);
        lax = (uu___1817_23495.lax);
        lax_universes = (uu___1817_23495.lax_universes);
        phase1 = (uu___1817_23495.phase1);
        failhard = (uu___1817_23495.failhard);
        nosynth = (uu___1817_23495.nosynth);
        uvar_subtyping = (uu___1817_23495.uvar_subtyping);
        tc_term = (uu___1817_23495.tc_term);
        type_of = (uu___1817_23495.type_of);
        universe_of = (uu___1817_23495.universe_of);
        check_type_of = (uu___1817_23495.check_type_of);
        use_bv_sorts = (uu___1817_23495.use_bv_sorts);
        qtbl_name_and_index = (uu___1817_23495.qtbl_name_and_index);
        normalized_eff_names = (uu___1817_23495.normalized_eff_names);
        fv_delta_depths = (uu___1817_23495.fv_delta_depths);
        proof_ns = (uu___1817_23495.proof_ns);
        synth_hook = (uu___1817_23495.synth_hook);
        splice = (uu___1817_23495.splice);
        postprocess = (uu___1817_23495.postprocess);
        is_native_tactic = (uu___1817_23495.is_native_tactic);
        identifier_info = (uu___1817_23495.identifier_info);
        tc_hooks = (uu___1817_23495.tc_hooks);
        dsenv = (uu___1817_23495.dsenv);
        nbe = (uu___1817_23495.nbe);
        strict_args_tab = (uu___1817_23495.strict_args_tab)
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
    let uu____23526 = expected_typ env_  in
    ((let uu___1824_23532 = env_  in
      {
        solver = (uu___1824_23532.solver);
        range = (uu___1824_23532.range);
        curmodule = (uu___1824_23532.curmodule);
        gamma = (uu___1824_23532.gamma);
        gamma_sig = (uu___1824_23532.gamma_sig);
        gamma_cache = (uu___1824_23532.gamma_cache);
        modules = (uu___1824_23532.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1824_23532.sigtab);
        attrtab = (uu___1824_23532.attrtab);
        is_pattern = (uu___1824_23532.is_pattern);
        instantiate_imp = (uu___1824_23532.instantiate_imp);
        effects = (uu___1824_23532.effects);
        generalize = (uu___1824_23532.generalize);
        letrecs = (uu___1824_23532.letrecs);
        top_level = (uu___1824_23532.top_level);
        check_uvars = (uu___1824_23532.check_uvars);
        use_eq = false;
        is_iface = (uu___1824_23532.is_iface);
        admit = (uu___1824_23532.admit);
        lax = (uu___1824_23532.lax);
        lax_universes = (uu___1824_23532.lax_universes);
        phase1 = (uu___1824_23532.phase1);
        failhard = (uu___1824_23532.failhard);
        nosynth = (uu___1824_23532.nosynth);
        uvar_subtyping = (uu___1824_23532.uvar_subtyping);
        tc_term = (uu___1824_23532.tc_term);
        type_of = (uu___1824_23532.type_of);
        universe_of = (uu___1824_23532.universe_of);
        check_type_of = (uu___1824_23532.check_type_of);
        use_bv_sorts = (uu___1824_23532.use_bv_sorts);
        qtbl_name_and_index = (uu___1824_23532.qtbl_name_and_index);
        normalized_eff_names = (uu___1824_23532.normalized_eff_names);
        fv_delta_depths = (uu___1824_23532.fv_delta_depths);
        proof_ns = (uu___1824_23532.proof_ns);
        synth_hook = (uu___1824_23532.synth_hook);
        splice = (uu___1824_23532.splice);
        postprocess = (uu___1824_23532.postprocess);
        is_native_tactic = (uu___1824_23532.is_native_tactic);
        identifier_info = (uu___1824_23532.identifier_info);
        tc_hooks = (uu___1824_23532.tc_hooks);
        dsenv = (uu___1824_23532.dsenv);
        nbe = (uu___1824_23532.nbe);
        strict_args_tab = (uu___1824_23532.strict_args_tab)
      }), uu____23526)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23544 =
      let uu____23547 = FStar_Ident.id_of_text ""  in [uu____23547]  in
    FStar_Ident.lid_of_ids uu____23544  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23554 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23554
        then
          let uu____23559 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23559 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1832_23587 = env  in
       {
         solver = (uu___1832_23587.solver);
         range = (uu___1832_23587.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1832_23587.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1832_23587.expected_typ);
         sigtab = (uu___1832_23587.sigtab);
         attrtab = (uu___1832_23587.attrtab);
         is_pattern = (uu___1832_23587.is_pattern);
         instantiate_imp = (uu___1832_23587.instantiate_imp);
         effects = (uu___1832_23587.effects);
         generalize = (uu___1832_23587.generalize);
         letrecs = (uu___1832_23587.letrecs);
         top_level = (uu___1832_23587.top_level);
         check_uvars = (uu___1832_23587.check_uvars);
         use_eq = (uu___1832_23587.use_eq);
         is_iface = (uu___1832_23587.is_iface);
         admit = (uu___1832_23587.admit);
         lax = (uu___1832_23587.lax);
         lax_universes = (uu___1832_23587.lax_universes);
         phase1 = (uu___1832_23587.phase1);
         failhard = (uu___1832_23587.failhard);
         nosynth = (uu___1832_23587.nosynth);
         uvar_subtyping = (uu___1832_23587.uvar_subtyping);
         tc_term = (uu___1832_23587.tc_term);
         type_of = (uu___1832_23587.type_of);
         universe_of = (uu___1832_23587.universe_of);
         check_type_of = (uu___1832_23587.check_type_of);
         use_bv_sorts = (uu___1832_23587.use_bv_sorts);
         qtbl_name_and_index = (uu___1832_23587.qtbl_name_and_index);
         normalized_eff_names = (uu___1832_23587.normalized_eff_names);
         fv_delta_depths = (uu___1832_23587.fv_delta_depths);
         proof_ns = (uu___1832_23587.proof_ns);
         synth_hook = (uu___1832_23587.synth_hook);
         splice = (uu___1832_23587.splice);
         postprocess = (uu___1832_23587.postprocess);
         is_native_tactic = (uu___1832_23587.is_native_tactic);
         identifier_info = (uu___1832_23587.identifier_info);
         tc_hooks = (uu___1832_23587.tc_hooks);
         dsenv = (uu___1832_23587.dsenv);
         nbe = (uu___1832_23587.nbe);
         strict_args_tab = (uu___1832_23587.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23639)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23643,(uu____23644,t)))::tl1
          ->
          let uu____23665 =
            let uu____23668 = FStar_Syntax_Free.uvars t  in
            ext out uu____23668  in
          aux uu____23665 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23671;
            FStar_Syntax_Syntax.index = uu____23672;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23680 =
            let uu____23683 = FStar_Syntax_Free.uvars t  in
            ext out uu____23683  in
          aux uu____23680 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23741)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23745,(uu____23746,t)))::tl1
          ->
          let uu____23767 =
            let uu____23770 = FStar_Syntax_Free.univs t  in
            ext out uu____23770  in
          aux uu____23767 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23773;
            FStar_Syntax_Syntax.index = uu____23774;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23782 =
            let uu____23785 = FStar_Syntax_Free.univs t  in
            ext out uu____23785  in
          aux uu____23782 tl1
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
          let uu____23847 = FStar_Util.set_add uname out  in
          aux uu____23847 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23850,(uu____23851,t)))::tl1
          ->
          let uu____23872 =
            let uu____23875 = FStar_Syntax_Free.univnames t  in
            ext out uu____23875  in
          aux uu____23872 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23878;
            FStar_Syntax_Syntax.index = uu____23879;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23887 =
            let uu____23890 = FStar_Syntax_Free.univnames t  in
            ext out uu____23890  in
          aux uu____23887 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_23911  ->
            match uu___12_23911 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23915 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23928 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23939 =
      let uu____23948 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23948
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23939 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23996 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24009  ->
              match uu___13_24009 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24012 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24012
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24018) ->
                  let uu____24035 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24035))
       in
    FStar_All.pipe_right uu____23996 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24049  ->
    match uu___14_24049 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only (true ) -> "Eager_unfolding_only true"
    | Eager_unfolding_only uu____24055 -> "Eager_unfolding_only false"
    | Unfold d ->
        let uu____24059 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24059
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24082  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24137) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24170,uu____24171) -> false  in
      let uu____24185 =
        FStar_List.tryFind
          (fun uu____24207  ->
             match uu____24207 with | (p,uu____24218) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24185 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24237,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24267 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24267
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1978_24289 = e  in
        {
          solver = (uu___1978_24289.solver);
          range = (uu___1978_24289.range);
          curmodule = (uu___1978_24289.curmodule);
          gamma = (uu___1978_24289.gamma);
          gamma_sig = (uu___1978_24289.gamma_sig);
          gamma_cache = (uu___1978_24289.gamma_cache);
          modules = (uu___1978_24289.modules);
          expected_typ = (uu___1978_24289.expected_typ);
          sigtab = (uu___1978_24289.sigtab);
          attrtab = (uu___1978_24289.attrtab);
          is_pattern = (uu___1978_24289.is_pattern);
          instantiate_imp = (uu___1978_24289.instantiate_imp);
          effects = (uu___1978_24289.effects);
          generalize = (uu___1978_24289.generalize);
          letrecs = (uu___1978_24289.letrecs);
          top_level = (uu___1978_24289.top_level);
          check_uvars = (uu___1978_24289.check_uvars);
          use_eq = (uu___1978_24289.use_eq);
          is_iface = (uu___1978_24289.is_iface);
          admit = (uu___1978_24289.admit);
          lax = (uu___1978_24289.lax);
          lax_universes = (uu___1978_24289.lax_universes);
          phase1 = (uu___1978_24289.phase1);
          failhard = (uu___1978_24289.failhard);
          nosynth = (uu___1978_24289.nosynth);
          uvar_subtyping = (uu___1978_24289.uvar_subtyping);
          tc_term = (uu___1978_24289.tc_term);
          type_of = (uu___1978_24289.type_of);
          universe_of = (uu___1978_24289.universe_of);
          check_type_of = (uu___1978_24289.check_type_of);
          use_bv_sorts = (uu___1978_24289.use_bv_sorts);
          qtbl_name_and_index = (uu___1978_24289.qtbl_name_and_index);
          normalized_eff_names = (uu___1978_24289.normalized_eff_names);
          fv_delta_depths = (uu___1978_24289.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1978_24289.synth_hook);
          splice = (uu___1978_24289.splice);
          postprocess = (uu___1978_24289.postprocess);
          is_native_tactic = (uu___1978_24289.is_native_tactic);
          identifier_info = (uu___1978_24289.identifier_info);
          tc_hooks = (uu___1978_24289.tc_hooks);
          dsenv = (uu___1978_24289.dsenv);
          nbe = (uu___1978_24289.nbe);
          strict_args_tab = (uu___1978_24289.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1987_24337 = e  in
      {
        solver = (uu___1987_24337.solver);
        range = (uu___1987_24337.range);
        curmodule = (uu___1987_24337.curmodule);
        gamma = (uu___1987_24337.gamma);
        gamma_sig = (uu___1987_24337.gamma_sig);
        gamma_cache = (uu___1987_24337.gamma_cache);
        modules = (uu___1987_24337.modules);
        expected_typ = (uu___1987_24337.expected_typ);
        sigtab = (uu___1987_24337.sigtab);
        attrtab = (uu___1987_24337.attrtab);
        is_pattern = (uu___1987_24337.is_pattern);
        instantiate_imp = (uu___1987_24337.instantiate_imp);
        effects = (uu___1987_24337.effects);
        generalize = (uu___1987_24337.generalize);
        letrecs = (uu___1987_24337.letrecs);
        top_level = (uu___1987_24337.top_level);
        check_uvars = (uu___1987_24337.check_uvars);
        use_eq = (uu___1987_24337.use_eq);
        is_iface = (uu___1987_24337.is_iface);
        admit = (uu___1987_24337.admit);
        lax = (uu___1987_24337.lax);
        lax_universes = (uu___1987_24337.lax_universes);
        phase1 = (uu___1987_24337.phase1);
        failhard = (uu___1987_24337.failhard);
        nosynth = (uu___1987_24337.nosynth);
        uvar_subtyping = (uu___1987_24337.uvar_subtyping);
        tc_term = (uu___1987_24337.tc_term);
        type_of = (uu___1987_24337.type_of);
        universe_of = (uu___1987_24337.universe_of);
        check_type_of = (uu___1987_24337.check_type_of);
        use_bv_sorts = (uu___1987_24337.use_bv_sorts);
        qtbl_name_and_index = (uu___1987_24337.qtbl_name_and_index);
        normalized_eff_names = (uu___1987_24337.normalized_eff_names);
        fv_delta_depths = (uu___1987_24337.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1987_24337.synth_hook);
        splice = (uu___1987_24337.splice);
        postprocess = (uu___1987_24337.postprocess);
        is_native_tactic = (uu___1987_24337.is_native_tactic);
        identifier_info = (uu___1987_24337.identifier_info);
        tc_hooks = (uu___1987_24337.tc_hooks);
        dsenv = (uu___1987_24337.dsenv);
        nbe = (uu___1987_24337.nbe);
        strict_args_tab = (uu___1987_24337.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24353 = FStar_Syntax_Free.names t  in
      let uu____24356 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24353 uu____24356
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24379 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24379
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24389 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24389
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24410 =
      match uu____24410 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24430 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24430)
       in
    let uu____24438 =
      let uu____24442 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24442 FStar_List.rev  in
    FStar_All.pipe_right uu____24438 (FStar_String.concat " ")
  
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
                  (let uu____24512 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24512 with
                   | FStar_Pervasives_Native.Some uu____24516 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24519 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24529;
        univ_ineqs = uu____24530; implicits = uu____24531;_} -> true
    | uu____24543 -> false
  
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
          let uu___2031_24574 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2031_24574.deferred);
            univ_ineqs = (uu___2031_24574.univ_ineqs);
            implicits = (uu___2031_24574.implicits)
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
          let uu____24613 = FStar_Options.defensive ()  in
          if uu____24613
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24619 =
              let uu____24621 =
                let uu____24623 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24623  in
              Prims.op_Negation uu____24621  in
            (if uu____24619
             then
               let uu____24630 =
                 let uu____24636 =
                   let uu____24638 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24640 =
                     let uu____24642 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24642
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24638 uu____24640
                    in
                 (FStar_Errors.Warning_Defensive, uu____24636)  in
               FStar_Errors.log_issue rng uu____24630
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
          let uu____24682 =
            let uu____24684 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24684  in
          if uu____24682
          then ()
          else
            (let uu____24689 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24689 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24715 =
            let uu____24717 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24717  in
          if uu____24715
          then ()
          else
            (let uu____24722 = bound_vars e  in
             def_check_closed_in rng msg uu____24722 t)
  
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
          let uu___2068_24761 = g  in
          let uu____24762 =
            let uu____24763 =
              let uu____24764 =
                let uu____24771 =
                  let uu____24772 =
                    let uu____24789 =
                      let uu____24800 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24800]  in
                    (f, uu____24789)  in
                  FStar_Syntax_Syntax.Tm_app uu____24772  in
                FStar_Syntax_Syntax.mk uu____24771  in
              uu____24764 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24837  -> FStar_TypeChecker_Common.NonTrivial _24837)
              uu____24763
             in
          {
            guard_f = uu____24762;
            deferred = (uu___2068_24761.deferred);
            univ_ineqs = (uu___2068_24761.univ_ineqs);
            implicits = (uu___2068_24761.implicits)
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
          let uu___2075_24855 = g  in
          let uu____24856 =
            let uu____24857 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24857  in
          {
            guard_f = uu____24856;
            deferred = (uu___2075_24855.deferred);
            univ_ineqs = (uu___2075_24855.univ_ineqs);
            implicits = (uu___2075_24855.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2080_24874 = g  in
          let uu____24875 =
            let uu____24876 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24876  in
          {
            guard_f = uu____24875;
            deferred = (uu___2080_24874.deferred);
            univ_ineqs = (uu___2080_24874.univ_ineqs);
            implicits = (uu___2080_24874.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2084_24878 = g  in
          let uu____24879 =
            let uu____24880 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24880  in
          {
            guard_f = uu____24879;
            deferred = (uu___2084_24878.deferred);
            univ_ineqs = (uu___2084_24878.univ_ineqs);
            implicits = (uu___2084_24878.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24887 ->
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
          let uu____24904 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24904
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24911 =
      let uu____24912 = FStar_Syntax_Util.unmeta t  in
      uu____24912.FStar_Syntax_Syntax.n  in
    match uu____24911 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24916 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24959 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24959;
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
                       let uu____25054 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25054
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2139_25061 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2139_25061.deferred);
              univ_ineqs = (uu___2139_25061.univ_ineqs);
              implicits = (uu___2139_25061.implicits)
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
               let uu____25095 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25095
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
            let uu___2154_25122 = g  in
            let uu____25123 =
              let uu____25124 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25124  in
            {
              guard_f = uu____25123;
              deferred = (uu___2154_25122.deferred);
              univ_ineqs = (uu___2154_25122.univ_ineqs);
              implicits = (uu___2154_25122.implicits)
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
              let uu____25182 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25182 with
              | FStar_Pervasives_Native.Some
                  (uu____25207::(tm,uu____25209)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25273 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25291 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25291;
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
                      let uu___2176_25323 = trivial_guard  in
                      {
                        guard_f = (uu___2176_25323.guard_f);
                        deferred = (uu___2176_25323.deferred);
                        univ_ineqs = (uu___2176_25323.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25341  -> ());
    push = (fun uu____25343  -> ());
    pop = (fun uu____25346  -> ());
    snapshot =
      (fun uu____25349  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25368  -> fun uu____25369  -> ());
    encode_sig = (fun uu____25384  -> fun uu____25385  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25391 =
             let uu____25398 = FStar_Options.peek ()  in (e, g, uu____25398)
              in
           [uu____25391]);
    solve = (fun uu____25414  -> fun uu____25415  -> fun uu____25416  -> ());
    finish = (fun uu____25423  -> ());
    refresh = (fun uu____25425  -> ())
  } 