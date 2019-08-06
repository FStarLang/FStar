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
  fun projectee  -> match projectee with | Beta  -> true | uu____110 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____121 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____132 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____144 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____162 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____173 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____184 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____195 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____206 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____217 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____229 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____250 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____277 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____304 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____328 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____339 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____350 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____361 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____372 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____383 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____394 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____405 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____416 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____427 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____438 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____449 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____460 -> false
  
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
      | uu____520 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____546 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____557 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____568 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____580 -> false
  
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
           (fun uu___0_12370  ->
              match uu___0_12370 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12373 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12373  in
                  let uu____12374 =
                    let uu____12375 = FStar_Syntax_Subst.compress y  in
                    uu____12375.FStar_Syntax_Syntax.n  in
                  (match uu____12374 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12379 =
                         let uu___332_12380 = y1  in
                         let uu____12381 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___332_12380.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___332_12380.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12381
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12379
                   | uu____12384 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___338_12398 = env  in
      let uu____12399 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___338_12398.solver);
        range = (uu___338_12398.range);
        curmodule = (uu___338_12398.curmodule);
        gamma = uu____12399;
        gamma_sig = (uu___338_12398.gamma_sig);
        gamma_cache = (uu___338_12398.gamma_cache);
        modules = (uu___338_12398.modules);
        expected_typ = (uu___338_12398.expected_typ);
        sigtab = (uu___338_12398.sigtab);
        attrtab = (uu___338_12398.attrtab);
        is_pattern = (uu___338_12398.is_pattern);
        instantiate_imp = (uu___338_12398.instantiate_imp);
        effects = (uu___338_12398.effects);
        generalize = (uu___338_12398.generalize);
        letrecs = (uu___338_12398.letrecs);
        top_level = (uu___338_12398.top_level);
        check_uvars = (uu___338_12398.check_uvars);
        use_eq = (uu___338_12398.use_eq);
        is_iface = (uu___338_12398.is_iface);
        admit = (uu___338_12398.admit);
        lax = (uu___338_12398.lax);
        lax_universes = (uu___338_12398.lax_universes);
        phase1 = (uu___338_12398.phase1);
        failhard = (uu___338_12398.failhard);
        nosynth = (uu___338_12398.nosynth);
        uvar_subtyping = (uu___338_12398.uvar_subtyping);
        tc_term = (uu___338_12398.tc_term);
        type_of = (uu___338_12398.type_of);
        universe_of = (uu___338_12398.universe_of);
        check_type_of = (uu___338_12398.check_type_of);
        use_bv_sorts = (uu___338_12398.use_bv_sorts);
        qtbl_name_and_index = (uu___338_12398.qtbl_name_and_index);
        normalized_eff_names = (uu___338_12398.normalized_eff_names);
        fv_delta_depths = (uu___338_12398.fv_delta_depths);
        proof_ns = (uu___338_12398.proof_ns);
        synth_hook = (uu___338_12398.synth_hook);
        splice = (uu___338_12398.splice);
        postprocess = (uu___338_12398.postprocess);
        is_native_tactic = (uu___338_12398.is_native_tactic);
        identifier_info = (uu___338_12398.identifier_info);
        tc_hooks = (uu___338_12398.tc_hooks);
        dsenv = (uu___338_12398.dsenv);
        nbe = (uu___338_12398.nbe);
        strict_args_tab = (uu___338_12398.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12407  -> fun uu____12408  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___345_12430 = env  in
      {
        solver = (uu___345_12430.solver);
        range = (uu___345_12430.range);
        curmodule = (uu___345_12430.curmodule);
        gamma = (uu___345_12430.gamma);
        gamma_sig = (uu___345_12430.gamma_sig);
        gamma_cache = (uu___345_12430.gamma_cache);
        modules = (uu___345_12430.modules);
        expected_typ = (uu___345_12430.expected_typ);
        sigtab = (uu___345_12430.sigtab);
        attrtab = (uu___345_12430.attrtab);
        is_pattern = (uu___345_12430.is_pattern);
        instantiate_imp = (uu___345_12430.instantiate_imp);
        effects = (uu___345_12430.effects);
        generalize = (uu___345_12430.generalize);
        letrecs = (uu___345_12430.letrecs);
        top_level = (uu___345_12430.top_level);
        check_uvars = (uu___345_12430.check_uvars);
        use_eq = (uu___345_12430.use_eq);
        is_iface = (uu___345_12430.is_iface);
        admit = (uu___345_12430.admit);
        lax = (uu___345_12430.lax);
        lax_universes = (uu___345_12430.lax_universes);
        phase1 = (uu___345_12430.phase1);
        failhard = (uu___345_12430.failhard);
        nosynth = (uu___345_12430.nosynth);
        uvar_subtyping = (uu___345_12430.uvar_subtyping);
        tc_term = (uu___345_12430.tc_term);
        type_of = (uu___345_12430.type_of);
        universe_of = (uu___345_12430.universe_of);
        check_type_of = (uu___345_12430.check_type_of);
        use_bv_sorts = (uu___345_12430.use_bv_sorts);
        qtbl_name_and_index = (uu___345_12430.qtbl_name_and_index);
        normalized_eff_names = (uu___345_12430.normalized_eff_names);
        fv_delta_depths = (uu___345_12430.fv_delta_depths);
        proof_ns = (uu___345_12430.proof_ns);
        synth_hook = (uu___345_12430.synth_hook);
        splice = (uu___345_12430.splice);
        postprocess = (uu___345_12430.postprocess);
        is_native_tactic = (uu___345_12430.is_native_tactic);
        identifier_info = (uu___345_12430.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___345_12430.dsenv);
        nbe = (uu___345_12430.nbe);
        strict_args_tab = (uu___345_12430.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___349_12442 = e  in
      let uu____12443 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___349_12442.solver);
        range = (uu___349_12442.range);
        curmodule = (uu___349_12442.curmodule);
        gamma = (uu___349_12442.gamma);
        gamma_sig = (uu___349_12442.gamma_sig);
        gamma_cache = (uu___349_12442.gamma_cache);
        modules = (uu___349_12442.modules);
        expected_typ = (uu___349_12442.expected_typ);
        sigtab = (uu___349_12442.sigtab);
        attrtab = (uu___349_12442.attrtab);
        is_pattern = (uu___349_12442.is_pattern);
        instantiate_imp = (uu___349_12442.instantiate_imp);
        effects = (uu___349_12442.effects);
        generalize = (uu___349_12442.generalize);
        letrecs = (uu___349_12442.letrecs);
        top_level = (uu___349_12442.top_level);
        check_uvars = (uu___349_12442.check_uvars);
        use_eq = (uu___349_12442.use_eq);
        is_iface = (uu___349_12442.is_iface);
        admit = (uu___349_12442.admit);
        lax = (uu___349_12442.lax);
        lax_universes = (uu___349_12442.lax_universes);
        phase1 = (uu___349_12442.phase1);
        failhard = (uu___349_12442.failhard);
        nosynth = (uu___349_12442.nosynth);
        uvar_subtyping = (uu___349_12442.uvar_subtyping);
        tc_term = (uu___349_12442.tc_term);
        type_of = (uu___349_12442.type_of);
        universe_of = (uu___349_12442.universe_of);
        check_type_of = (uu___349_12442.check_type_of);
        use_bv_sorts = (uu___349_12442.use_bv_sorts);
        qtbl_name_and_index = (uu___349_12442.qtbl_name_and_index);
        normalized_eff_names = (uu___349_12442.normalized_eff_names);
        fv_delta_depths = (uu___349_12442.fv_delta_depths);
        proof_ns = (uu___349_12442.proof_ns);
        synth_hook = (uu___349_12442.synth_hook);
        splice = (uu___349_12442.splice);
        postprocess = (uu___349_12442.postprocess);
        is_native_tactic = (uu___349_12442.is_native_tactic);
        identifier_info = (uu___349_12442.identifier_info);
        tc_hooks = (uu___349_12442.tc_hooks);
        dsenv = uu____12443;
        nbe = (uu___349_12442.nbe);
        strict_args_tab = (uu___349_12442.strict_args_tab)
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
      | (NoDelta ,uu____12472) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12475,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12477,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12480 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12494 . unit -> 'Auu____12494 FStar_Util.smap =
  fun uu____12501  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12507 . unit -> 'Auu____12507 FStar_Util.smap =
  fun uu____12514  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____12652 = new_gamma_cache ()  in
                  let uu____12655 = new_sigtab ()  in
                  let uu____12658 = new_sigtab ()  in
                  let uu____12665 =
                    let uu____12680 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____12680, FStar_Pervasives_Native.None)  in
                  let uu____12701 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12705 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____12709 = FStar_Options.using_facts_from ()  in
                  let uu____12710 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12713 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____12714 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12652;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12655;
                    attrtab = uu____12658;
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
                    qtbl_name_and_index = uu____12665;
                    normalized_eff_names = uu____12701;
                    fv_delta_depths = uu____12705;
                    proof_ns = uu____12709;
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
                    is_native_tactic = (fun uu____12789  -> false);
                    identifier_info = uu____12710;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12713;
                    nbe = nbe1;
                    strict_args_tab = uu____12714
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
  fun uu____12868  ->
    let uu____12869 = FStar_ST.op_Bang query_indices  in
    match uu____12869 with
    | [] -> failwith "Empty query indices!"
    | uu____12924 ->
        let uu____12934 =
          let uu____12944 =
            let uu____12952 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12952  in
          let uu____13006 = FStar_ST.op_Bang query_indices  in uu____12944 ::
            uu____13006
           in
        FStar_ST.op_Colon_Equals query_indices uu____12934
  
let (pop_query_indices : unit -> unit) =
  fun uu____13102  ->
    let uu____13103 = FStar_ST.op_Bang query_indices  in
    match uu____13103 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13230  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13267  ->
    match uu____13267 with
    | (l,n1) ->
        let uu____13277 = FStar_ST.op_Bang query_indices  in
        (match uu____13277 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13399 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13422  ->
    let uu____13423 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13423
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13491 =
       let uu____13494 = FStar_ST.op_Bang stack  in env :: uu____13494  in
     FStar_ST.op_Colon_Equals stack uu____13491);
    (let uu___417_13543 = env  in
     let uu____13544 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13547 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13550 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13557 =
       let uu____13572 =
         let uu____13576 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13576  in
       let uu____13608 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13572, uu____13608)  in
     let uu____13657 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13660 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13663 =
       let uu____13666 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13666  in
     let uu____13686 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___417_13543.solver);
       range = (uu___417_13543.range);
       curmodule = (uu___417_13543.curmodule);
       gamma = (uu___417_13543.gamma);
       gamma_sig = (uu___417_13543.gamma_sig);
       gamma_cache = uu____13544;
       modules = (uu___417_13543.modules);
       expected_typ = (uu___417_13543.expected_typ);
       sigtab = uu____13547;
       attrtab = uu____13550;
       is_pattern = (uu___417_13543.is_pattern);
       instantiate_imp = (uu___417_13543.instantiate_imp);
       effects = (uu___417_13543.effects);
       generalize = (uu___417_13543.generalize);
       letrecs = (uu___417_13543.letrecs);
       top_level = (uu___417_13543.top_level);
       check_uvars = (uu___417_13543.check_uvars);
       use_eq = (uu___417_13543.use_eq);
       is_iface = (uu___417_13543.is_iface);
       admit = (uu___417_13543.admit);
       lax = (uu___417_13543.lax);
       lax_universes = (uu___417_13543.lax_universes);
       phase1 = (uu___417_13543.phase1);
       failhard = (uu___417_13543.failhard);
       nosynth = (uu___417_13543.nosynth);
       uvar_subtyping = (uu___417_13543.uvar_subtyping);
       tc_term = (uu___417_13543.tc_term);
       type_of = (uu___417_13543.type_of);
       universe_of = (uu___417_13543.universe_of);
       check_type_of = (uu___417_13543.check_type_of);
       use_bv_sorts = (uu___417_13543.use_bv_sorts);
       qtbl_name_and_index = uu____13557;
       normalized_eff_names = uu____13657;
       fv_delta_depths = uu____13660;
       proof_ns = (uu___417_13543.proof_ns);
       synth_hook = (uu___417_13543.synth_hook);
       splice = (uu___417_13543.splice);
       postprocess = (uu___417_13543.postprocess);
       is_native_tactic = (uu___417_13543.is_native_tactic);
       identifier_info = uu____13663;
       tc_hooks = (uu___417_13543.tc_hooks);
       dsenv = (uu___417_13543.dsenv);
       nbe = (uu___417_13543.nbe);
       strict_args_tab = uu____13686
     })
  
let (pop_stack : unit -> env) =
  fun uu____13704  ->
    let uu____13705 = FStar_ST.op_Bang stack  in
    match uu____13705 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13759 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13849  ->
           let uu____13850 = snapshot_stack env  in
           match uu____13850 with
           | (stack_depth,env1) ->
               let uu____13884 = snapshot_query_indices ()  in
               (match uu____13884 with
                | (query_indices_depth,()) ->
                    let uu____13917 = (env1.solver).snapshot msg  in
                    (match uu____13917 with
                     | (solver_depth,()) ->
                         let uu____13974 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13974 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___442_14041 = env1  in
                                 {
                                   solver = (uu___442_14041.solver);
                                   range = (uu___442_14041.range);
                                   curmodule = (uu___442_14041.curmodule);
                                   gamma = (uu___442_14041.gamma);
                                   gamma_sig = (uu___442_14041.gamma_sig);
                                   gamma_cache = (uu___442_14041.gamma_cache);
                                   modules = (uu___442_14041.modules);
                                   expected_typ =
                                     (uu___442_14041.expected_typ);
                                   sigtab = (uu___442_14041.sigtab);
                                   attrtab = (uu___442_14041.attrtab);
                                   is_pattern = (uu___442_14041.is_pattern);
                                   instantiate_imp =
                                     (uu___442_14041.instantiate_imp);
                                   effects = (uu___442_14041.effects);
                                   generalize = (uu___442_14041.generalize);
                                   letrecs = (uu___442_14041.letrecs);
                                   top_level = (uu___442_14041.top_level);
                                   check_uvars = (uu___442_14041.check_uvars);
                                   use_eq = (uu___442_14041.use_eq);
                                   is_iface = (uu___442_14041.is_iface);
                                   admit = (uu___442_14041.admit);
                                   lax = (uu___442_14041.lax);
                                   lax_universes =
                                     (uu___442_14041.lax_universes);
                                   phase1 = (uu___442_14041.phase1);
                                   failhard = (uu___442_14041.failhard);
                                   nosynth = (uu___442_14041.nosynth);
                                   uvar_subtyping =
                                     (uu___442_14041.uvar_subtyping);
                                   tc_term = (uu___442_14041.tc_term);
                                   type_of = (uu___442_14041.type_of);
                                   universe_of = (uu___442_14041.universe_of);
                                   check_type_of =
                                     (uu___442_14041.check_type_of);
                                   use_bv_sorts =
                                     (uu___442_14041.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___442_14041.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___442_14041.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___442_14041.fv_delta_depths);
                                   proof_ns = (uu___442_14041.proof_ns);
                                   synth_hook = (uu___442_14041.synth_hook);
                                   splice = (uu___442_14041.splice);
                                   postprocess = (uu___442_14041.postprocess);
                                   is_native_tactic =
                                     (uu___442_14041.is_native_tactic);
                                   identifier_info =
                                     (uu___442_14041.identifier_info);
                                   tc_hooks = (uu___442_14041.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___442_14041.nbe);
                                   strict_args_tab =
                                     (uu___442_14041.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14075  ->
             let uu____14076 =
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
             match uu____14076 with
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
                             ((let uu____14256 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14256
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14272 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14272
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14304,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14346 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14376  ->
                  match uu____14376 with
                  | (m,uu____14384) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14346 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___487_14399 = env  in
               {
                 solver = (uu___487_14399.solver);
                 range = (uu___487_14399.range);
                 curmodule = (uu___487_14399.curmodule);
                 gamma = (uu___487_14399.gamma);
                 gamma_sig = (uu___487_14399.gamma_sig);
                 gamma_cache = (uu___487_14399.gamma_cache);
                 modules = (uu___487_14399.modules);
                 expected_typ = (uu___487_14399.expected_typ);
                 sigtab = (uu___487_14399.sigtab);
                 attrtab = (uu___487_14399.attrtab);
                 is_pattern = (uu___487_14399.is_pattern);
                 instantiate_imp = (uu___487_14399.instantiate_imp);
                 effects = (uu___487_14399.effects);
                 generalize = (uu___487_14399.generalize);
                 letrecs = (uu___487_14399.letrecs);
                 top_level = (uu___487_14399.top_level);
                 check_uvars = (uu___487_14399.check_uvars);
                 use_eq = (uu___487_14399.use_eq);
                 is_iface = (uu___487_14399.is_iface);
                 admit = (uu___487_14399.admit);
                 lax = (uu___487_14399.lax);
                 lax_universes = (uu___487_14399.lax_universes);
                 phase1 = (uu___487_14399.phase1);
                 failhard = (uu___487_14399.failhard);
                 nosynth = (uu___487_14399.nosynth);
                 uvar_subtyping = (uu___487_14399.uvar_subtyping);
                 tc_term = (uu___487_14399.tc_term);
                 type_of = (uu___487_14399.type_of);
                 universe_of = (uu___487_14399.universe_of);
                 check_type_of = (uu___487_14399.check_type_of);
                 use_bv_sorts = (uu___487_14399.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___487_14399.normalized_eff_names);
                 fv_delta_depths = (uu___487_14399.fv_delta_depths);
                 proof_ns = (uu___487_14399.proof_ns);
                 synth_hook = (uu___487_14399.synth_hook);
                 splice = (uu___487_14399.splice);
                 postprocess = (uu___487_14399.postprocess);
                 is_native_tactic = (uu___487_14399.is_native_tactic);
                 identifier_info = (uu___487_14399.identifier_info);
                 tc_hooks = (uu___487_14399.tc_hooks);
                 dsenv = (uu___487_14399.dsenv);
                 nbe = (uu___487_14399.nbe);
                 strict_args_tab = (uu___487_14399.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14416,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___496_14432 = env  in
               {
                 solver = (uu___496_14432.solver);
                 range = (uu___496_14432.range);
                 curmodule = (uu___496_14432.curmodule);
                 gamma = (uu___496_14432.gamma);
                 gamma_sig = (uu___496_14432.gamma_sig);
                 gamma_cache = (uu___496_14432.gamma_cache);
                 modules = (uu___496_14432.modules);
                 expected_typ = (uu___496_14432.expected_typ);
                 sigtab = (uu___496_14432.sigtab);
                 attrtab = (uu___496_14432.attrtab);
                 is_pattern = (uu___496_14432.is_pattern);
                 instantiate_imp = (uu___496_14432.instantiate_imp);
                 effects = (uu___496_14432.effects);
                 generalize = (uu___496_14432.generalize);
                 letrecs = (uu___496_14432.letrecs);
                 top_level = (uu___496_14432.top_level);
                 check_uvars = (uu___496_14432.check_uvars);
                 use_eq = (uu___496_14432.use_eq);
                 is_iface = (uu___496_14432.is_iface);
                 admit = (uu___496_14432.admit);
                 lax = (uu___496_14432.lax);
                 lax_universes = (uu___496_14432.lax_universes);
                 phase1 = (uu___496_14432.phase1);
                 failhard = (uu___496_14432.failhard);
                 nosynth = (uu___496_14432.nosynth);
                 uvar_subtyping = (uu___496_14432.uvar_subtyping);
                 tc_term = (uu___496_14432.tc_term);
                 type_of = (uu___496_14432.type_of);
                 universe_of = (uu___496_14432.universe_of);
                 check_type_of = (uu___496_14432.check_type_of);
                 use_bv_sorts = (uu___496_14432.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___496_14432.normalized_eff_names);
                 fv_delta_depths = (uu___496_14432.fv_delta_depths);
                 proof_ns = (uu___496_14432.proof_ns);
                 synth_hook = (uu___496_14432.synth_hook);
                 splice = (uu___496_14432.splice);
                 postprocess = (uu___496_14432.postprocess);
                 is_native_tactic = (uu___496_14432.is_native_tactic);
                 identifier_info = (uu___496_14432.identifier_info);
                 tc_hooks = (uu___496_14432.tc_hooks);
                 dsenv = (uu___496_14432.dsenv);
                 nbe = (uu___496_14432.nbe);
                 strict_args_tab = (uu___496_14432.strict_args_tab)
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
        (let uu___503_14475 = e  in
         {
           solver = (uu___503_14475.solver);
           range = r;
           curmodule = (uu___503_14475.curmodule);
           gamma = (uu___503_14475.gamma);
           gamma_sig = (uu___503_14475.gamma_sig);
           gamma_cache = (uu___503_14475.gamma_cache);
           modules = (uu___503_14475.modules);
           expected_typ = (uu___503_14475.expected_typ);
           sigtab = (uu___503_14475.sigtab);
           attrtab = (uu___503_14475.attrtab);
           is_pattern = (uu___503_14475.is_pattern);
           instantiate_imp = (uu___503_14475.instantiate_imp);
           effects = (uu___503_14475.effects);
           generalize = (uu___503_14475.generalize);
           letrecs = (uu___503_14475.letrecs);
           top_level = (uu___503_14475.top_level);
           check_uvars = (uu___503_14475.check_uvars);
           use_eq = (uu___503_14475.use_eq);
           is_iface = (uu___503_14475.is_iface);
           admit = (uu___503_14475.admit);
           lax = (uu___503_14475.lax);
           lax_universes = (uu___503_14475.lax_universes);
           phase1 = (uu___503_14475.phase1);
           failhard = (uu___503_14475.failhard);
           nosynth = (uu___503_14475.nosynth);
           uvar_subtyping = (uu___503_14475.uvar_subtyping);
           tc_term = (uu___503_14475.tc_term);
           type_of = (uu___503_14475.type_of);
           universe_of = (uu___503_14475.universe_of);
           check_type_of = (uu___503_14475.check_type_of);
           use_bv_sorts = (uu___503_14475.use_bv_sorts);
           qtbl_name_and_index = (uu___503_14475.qtbl_name_and_index);
           normalized_eff_names = (uu___503_14475.normalized_eff_names);
           fv_delta_depths = (uu___503_14475.fv_delta_depths);
           proof_ns = (uu___503_14475.proof_ns);
           synth_hook = (uu___503_14475.synth_hook);
           splice = (uu___503_14475.splice);
           postprocess = (uu___503_14475.postprocess);
           is_native_tactic = (uu___503_14475.is_native_tactic);
           identifier_info = (uu___503_14475.identifier_info);
           tc_hooks = (uu___503_14475.tc_hooks);
           dsenv = (uu___503_14475.dsenv);
           nbe = (uu___503_14475.nbe);
           strict_args_tab = (uu___503_14475.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14495 =
        let uu____14496 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14496 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14495
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14551 =
          let uu____14552 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14552 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14551
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14607 =
          let uu____14608 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14608 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14607
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14663 =
        let uu____14664 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14664 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14663
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___520_14728 = env  in
      {
        solver = (uu___520_14728.solver);
        range = (uu___520_14728.range);
        curmodule = lid;
        gamma = (uu___520_14728.gamma);
        gamma_sig = (uu___520_14728.gamma_sig);
        gamma_cache = (uu___520_14728.gamma_cache);
        modules = (uu___520_14728.modules);
        expected_typ = (uu___520_14728.expected_typ);
        sigtab = (uu___520_14728.sigtab);
        attrtab = (uu___520_14728.attrtab);
        is_pattern = (uu___520_14728.is_pattern);
        instantiate_imp = (uu___520_14728.instantiate_imp);
        effects = (uu___520_14728.effects);
        generalize = (uu___520_14728.generalize);
        letrecs = (uu___520_14728.letrecs);
        top_level = (uu___520_14728.top_level);
        check_uvars = (uu___520_14728.check_uvars);
        use_eq = (uu___520_14728.use_eq);
        is_iface = (uu___520_14728.is_iface);
        admit = (uu___520_14728.admit);
        lax = (uu___520_14728.lax);
        lax_universes = (uu___520_14728.lax_universes);
        phase1 = (uu___520_14728.phase1);
        failhard = (uu___520_14728.failhard);
        nosynth = (uu___520_14728.nosynth);
        uvar_subtyping = (uu___520_14728.uvar_subtyping);
        tc_term = (uu___520_14728.tc_term);
        type_of = (uu___520_14728.type_of);
        universe_of = (uu___520_14728.universe_of);
        check_type_of = (uu___520_14728.check_type_of);
        use_bv_sorts = (uu___520_14728.use_bv_sorts);
        qtbl_name_and_index = (uu___520_14728.qtbl_name_and_index);
        normalized_eff_names = (uu___520_14728.normalized_eff_names);
        fv_delta_depths = (uu___520_14728.fv_delta_depths);
        proof_ns = (uu___520_14728.proof_ns);
        synth_hook = (uu___520_14728.synth_hook);
        splice = (uu___520_14728.splice);
        postprocess = (uu___520_14728.postprocess);
        is_native_tactic = (uu___520_14728.is_native_tactic);
        identifier_info = (uu___520_14728.identifier_info);
        tc_hooks = (uu___520_14728.tc_hooks);
        dsenv = (uu___520_14728.dsenv);
        nbe = (uu___520_14728.nbe);
        strict_args_tab = (uu___520_14728.strict_args_tab)
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
      let uu____14759 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14759
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14772 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14772)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14787 =
      let uu____14789 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14789  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14787)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14798  ->
    let uu____14799 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14799
  
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
      | ((formals,t),uu____14899) ->
          let vs = mk_univ_subst formals us  in
          let uu____14923 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14923)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14940  ->
    match uu___1_14940 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14966  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14986 = inst_tscheme t  in
      match uu____14986 with
      | (us,t1) ->
          let uu____14997 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14997)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____15018  ->
          match uu____15018 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____15040 =
                         let uu____15042 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____15046 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____15050 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____15052 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____15042 uu____15046 uu____15050 uu____15052
                          in
                       failwith uu____15040)
                    else ();
                    (let uu____15057 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____15057))
               | uu____15066 ->
                   let uu____15067 =
                     let uu____15069 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____15069
                      in
                   failwith uu____15067)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15081 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15092 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15103 -> false
  
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
             | ([],uu____15151) -> Maybe
             | (uu____15158,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15178 -> No  in
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
          let uu____15272 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15272 with
          | FStar_Pervasives_Native.None  ->
              let uu____15295 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15339  ->
                     match uu___2_15339 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15378 = FStar_Ident.lid_equals lid l  in
                         if uu____15378
                         then
                           let uu____15401 =
                             let uu____15420 =
                               let uu____15435 = inst_tscheme t  in
                               FStar_Util.Inl uu____15435  in
                             let uu____15450 = FStar_Ident.range_of_lid l  in
                             (uu____15420, uu____15450)  in
                           FStar_Pervasives_Native.Some uu____15401
                         else FStar_Pervasives_Native.None
                     | uu____15503 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15295
                (fun uu____15541  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15550  ->
                        match uu___3_15550 with
                        | (uu____15553,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15555);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15556;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15557;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15558;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15559;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15579 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15579
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
                                  uu____15631 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15638 -> cache t  in
                            let uu____15639 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15639 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15645 =
                                   let uu____15646 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15646)
                                    in
                                 maybe_cache uu____15645)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15717 = find_in_sigtab env lid  in
         match uu____15717 with
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
      let uu____15798 = lookup_qname env lid  in
      match uu____15798 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15819,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15933 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15933 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15978 =
          let uu____15981 = lookup_attr env1 attr  in se1 :: uu____15981  in
        FStar_Util.smap_add (attrtab env1) attr uu____15978  in
      FStar_List.iter
        (fun attr  ->
           let uu____15991 =
             let uu____15992 = FStar_Syntax_Subst.compress attr  in
             uu____15992.FStar_Syntax_Syntax.n  in
           match uu____15991 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15996 =
                 let uu____15998 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15998.FStar_Ident.str  in
               add_one1 env se uu____15996
           | uu____15999 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16022) ->
          add_sigelts env ses
      | uu____16031 ->
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
            | uu____16046 -> ()))

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
        (fun uu___4_16078  ->
           match uu___4_16078 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16096 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16158,lb::[]),uu____16160) ->
            let uu____16169 =
              let uu____16178 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16187 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16178, uu____16187)  in
            FStar_Pervasives_Native.Some uu____16169
        | FStar_Syntax_Syntax.Sig_let ((uu____16200,lbs),uu____16202) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16234 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16247 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16247
                     then
                       let uu____16260 =
                         let uu____16269 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16278 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16269, uu____16278)  in
                       FStar_Pervasives_Native.Some uu____16260
                     else FStar_Pervasives_Native.None)
        | uu____16301 -> FStar_Pervasives_Native.None
  
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
          let uu____16361 =
            let uu____16370 =
              let uu____16375 =
                let uu____16376 =
                  let uu____16379 =
                    let uu____16382 =
                      FStar_All.pipe_right ne.FStar_Syntax_Syntax.signature
                        FStar_Pervasives_Native.snd
                       in
                    FStar_All.pipe_right uu____16382
                      FStar_Syntax_Syntax.mk_Total
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____16379
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____16376)  in
              inst_tscheme1 uu____16375  in
            (uu____16370, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16361
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16416,uu____16417) ->
          let uu____16422 =
            let uu____16431 =
              let uu____16436 =
                let uu____16437 =
                  let uu____16440 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16440  in
                (us, uu____16437)  in
              inst_tscheme1 uu____16436  in
            (uu____16431, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16422
      | uu____16459 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16548 =
          match uu____16548 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16644,uvs,t,uu____16647,uu____16648,uu____16649);
                      FStar_Syntax_Syntax.sigrng = uu____16650;
                      FStar_Syntax_Syntax.sigquals = uu____16651;
                      FStar_Syntax_Syntax.sigmeta = uu____16652;
                      FStar_Syntax_Syntax.sigattrs = uu____16653;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16676 =
                     let uu____16685 = inst_tscheme1 (uvs, t)  in
                     (uu____16685, rng)  in
                   FStar_Pervasives_Native.Some uu____16676
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16709;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16711;
                      FStar_Syntax_Syntax.sigattrs = uu____16712;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16729 =
                     let uu____16731 = in_cur_mod env l  in uu____16731 = Yes
                      in
                   if uu____16729
                   then
                     let uu____16743 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16743
                      then
                        let uu____16759 =
                          let uu____16768 = inst_tscheme1 (uvs, t)  in
                          (uu____16768, rng)  in
                        FStar_Pervasives_Native.Some uu____16759
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16801 =
                        let uu____16810 = inst_tscheme1 (uvs, t)  in
                        (uu____16810, rng)  in
                      FStar_Pervasives_Native.Some uu____16801)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16835,uu____16836);
                      FStar_Syntax_Syntax.sigrng = uu____16837;
                      FStar_Syntax_Syntax.sigquals = uu____16838;
                      FStar_Syntax_Syntax.sigmeta = uu____16839;
                      FStar_Syntax_Syntax.sigattrs = uu____16840;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16881 =
                          let uu____16890 = inst_tscheme1 (uvs, k)  in
                          (uu____16890, rng)  in
                        FStar_Pervasives_Native.Some uu____16881
                    | uu____16911 ->
                        let uu____16912 =
                          let uu____16921 =
                            let uu____16926 =
                              let uu____16927 =
                                let uu____16930 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16930
                                 in
                              (uvs, uu____16927)  in
                            inst_tscheme1 uu____16926  in
                          (uu____16921, rng)  in
                        FStar_Pervasives_Native.Some uu____16912)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16953,uu____16954);
                      FStar_Syntax_Syntax.sigrng = uu____16955;
                      FStar_Syntax_Syntax.sigquals = uu____16956;
                      FStar_Syntax_Syntax.sigmeta = uu____16957;
                      FStar_Syntax_Syntax.sigattrs = uu____16958;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17000 =
                          let uu____17009 = inst_tscheme_with (uvs, k) us  in
                          (uu____17009, rng)  in
                        FStar_Pervasives_Native.Some uu____17000
                    | uu____17030 ->
                        let uu____17031 =
                          let uu____17040 =
                            let uu____17045 =
                              let uu____17046 =
                                let uu____17049 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17049
                                 in
                              (uvs, uu____17046)  in
                            inst_tscheme_with uu____17045 us  in
                          (uu____17040, rng)  in
                        FStar_Pervasives_Native.Some uu____17031)
               | FStar_Util.Inr se ->
                   let uu____17085 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17106;
                          FStar_Syntax_Syntax.sigrng = uu____17107;
                          FStar_Syntax_Syntax.sigquals = uu____17108;
                          FStar_Syntax_Syntax.sigmeta = uu____17109;
                          FStar_Syntax_Syntax.sigattrs = uu____17110;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17125 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____17085
                     (FStar_Util.map_option
                        (fun uu____17173  ->
                           match uu____17173 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17204 =
          let uu____17215 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17215 mapper  in
        match uu____17204 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17289 =
              let uu____17300 =
                let uu____17307 =
                  let uu___847_17310 = t  in
                  let uu____17311 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___847_17310.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17311;
                    FStar_Syntax_Syntax.vars =
                      (uu___847_17310.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17307)  in
              (uu____17300, r)  in
            FStar_Pervasives_Native.Some uu____17289
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17360 = lookup_qname env l  in
      match uu____17360 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17381 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17435 = try_lookup_bv env bv  in
      match uu____17435 with
      | FStar_Pervasives_Native.None  ->
          let uu____17450 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17450 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17466 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17467 =
            let uu____17468 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17468  in
          (uu____17466, uu____17467)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17490 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17490 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17556 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17556  in
          let uu____17557 =
            let uu____17566 =
              let uu____17571 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17571)  in
            (uu____17566, r1)  in
          FStar_Pervasives_Native.Some uu____17557
  
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
        let uu____17606 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17606 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17639,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17664 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17664  in
            let uu____17665 =
              let uu____17670 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17670, r1)  in
            FStar_Pervasives_Native.Some uu____17665
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17694 = try_lookup_lid env l  in
      match uu____17694 with
      | FStar_Pervasives_Native.None  ->
          let uu____17721 = name_not_found l  in
          let uu____17727 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17721 uu____17727
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17770  ->
              match uu___5_17770 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17774 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17795 = lookup_qname env lid  in
      match uu____17795 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17804,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17807;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17809;
              FStar_Syntax_Syntax.sigattrs = uu____17810;_},FStar_Pervasives_Native.None
            ),uu____17811)
          ->
          let uu____17860 =
            let uu____17867 =
              let uu____17868 =
                let uu____17871 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17871 t  in
              (uvs, uu____17868)  in
            (uu____17867, q)  in
          FStar_Pervasives_Native.Some uu____17860
      | uu____17884 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17906 = lookup_qname env lid  in
      match uu____17906 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17911,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17914;
              FStar_Syntax_Syntax.sigquals = uu____17915;
              FStar_Syntax_Syntax.sigmeta = uu____17916;
              FStar_Syntax_Syntax.sigattrs = uu____17917;_},FStar_Pervasives_Native.None
            ),uu____17918)
          ->
          let uu____17967 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17967 (uvs, t)
      | uu____17972 ->
          let uu____17973 = name_not_found lid  in
          let uu____17979 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17973 uu____17979
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17999 = lookup_qname env lid  in
      match uu____17999 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18004,uvs,t,uu____18007,uu____18008,uu____18009);
              FStar_Syntax_Syntax.sigrng = uu____18010;
              FStar_Syntax_Syntax.sigquals = uu____18011;
              FStar_Syntax_Syntax.sigmeta = uu____18012;
              FStar_Syntax_Syntax.sigattrs = uu____18013;_},FStar_Pervasives_Native.None
            ),uu____18014)
          ->
          let uu____18069 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18069 (uvs, t)
      | uu____18074 ->
          let uu____18075 = name_not_found lid  in
          let uu____18081 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18075 uu____18081
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18104 = lookup_qname env lid  in
      match uu____18104 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18112,uu____18113,uu____18114,uu____18115,uu____18116,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18118;
              FStar_Syntax_Syntax.sigquals = uu____18119;
              FStar_Syntax_Syntax.sigmeta = uu____18120;
              FStar_Syntax_Syntax.sigattrs = uu____18121;_},uu____18122),uu____18123)
          -> (true, dcs)
      | uu____18186 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18202 = lookup_qname env lid  in
      match uu____18202 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18203,uu____18204,uu____18205,l,uu____18207,uu____18208);
              FStar_Syntax_Syntax.sigrng = uu____18209;
              FStar_Syntax_Syntax.sigquals = uu____18210;
              FStar_Syntax_Syntax.sigmeta = uu____18211;
              FStar_Syntax_Syntax.sigattrs = uu____18212;_},uu____18213),uu____18214)
          -> l
      | uu____18271 ->
          let uu____18272 =
            let uu____18274 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18274  in
          failwith uu____18272
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18344)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18401) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18425 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18425
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18460 -> FStar_Pervasives_Native.None)
          | uu____18469 -> FStar_Pervasives_Native.None
  
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
        let uu____18531 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18531
  
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
        let uu____18564 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18564
  
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
             (FStar_Util.Inl uu____18616,uu____18617) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18666),uu____18667) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18716 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18734 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18744 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18761 ->
                  let uu____18768 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18768
              | FStar_Syntax_Syntax.Sig_let ((uu____18769,lbs),uu____18771)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18787 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18787
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18794 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18802 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18803 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18810 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18811 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18812 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18813 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18826 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18844 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18844
           (fun d_opt  ->
              let uu____18857 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18857
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18867 =
                   let uu____18870 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18870  in
                 match uu____18867 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18871 =
                       let uu____18873 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18873
                        in
                     failwith uu____18871
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18878 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18878
                       then
                         let uu____18881 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18883 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18885 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18881 uu____18883 uu____18885
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
        (FStar_Util.Inr (se,uu____18910),uu____18911) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18960 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18982),uu____18983) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19032 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19054 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19054
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19077 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19077 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19101 =
                      let uu____19102 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19102.FStar_Syntax_Syntax.n  in
                    match uu____19101 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19107 -> false))
  
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
        let uu____19144 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19144.FStar_Ident.str  in
      let uu____19145 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19145 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19173 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19173  in
          let res =
            match attrs with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some attrs1 ->
                FStar_Util.find_map attrs1
                  (fun x  ->
                     let uu____19201 =
                       FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                         FStar_Parser_Const.strict_on_arguments_attr
                        in
                     FStar_Pervasives_Native.fst uu____19201)
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
      let uu____19251 = lookup_qname env ftv  in
      match uu____19251 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19255) ->
          let uu____19300 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____19300 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19321,t),r) ->
               let uu____19336 =
                 let uu____19337 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19337 t  in
               FStar_Pervasives_Native.Some uu____19336)
      | uu____19338 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19350 = try_lookup_effect_lid env ftv  in
      match uu____19350 with
      | FStar_Pervasives_Native.None  ->
          let uu____19353 = name_not_found ftv  in
          let uu____19359 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19353 uu____19359
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
        let uu____19383 = lookup_qname env lid0  in
        match uu____19383 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19394);
                FStar_Syntax_Syntax.sigrng = uu____19395;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19397;
                FStar_Syntax_Syntax.sigattrs = uu____19398;_},FStar_Pervasives_Native.None
              ),uu____19399)
            ->
            let lid1 =
              let uu____19453 =
                let uu____19454 = FStar_Ident.range_of_lid lid  in
                let uu____19455 =
                  let uu____19456 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19456  in
                FStar_Range.set_use_range uu____19454 uu____19455  in
              FStar_Ident.set_lid_range lid uu____19453  in
            let uu____19457 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19463  ->
                      match uu___6_19463 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19466 -> false))
               in
            if uu____19457
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19485 =
                      let uu____19487 =
                        let uu____19489 = get_range env  in
                        FStar_Range.string_of_range uu____19489  in
                      let uu____19490 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19492 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19487 uu____19490 uu____19492
                       in
                    failwith uu____19485)
                  in
               match (binders, univs1) with
               | ([],uu____19513) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19539,uu____19540::uu____19541::uu____19542) ->
                   let uu____19563 =
                     let uu____19565 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19567 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19565 uu____19567
                      in
                   failwith uu____19563
               | uu____19578 ->
                   let uu____19593 =
                     let uu____19598 =
                       let uu____19599 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19599)  in
                     inst_tscheme_with uu____19598 insts  in
                   (match uu____19593 with
                    | (uu____19612,t) ->
                        let t1 =
                          let uu____19615 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19615 t  in
                        let uu____19616 =
                          let uu____19617 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19617.FStar_Syntax_Syntax.n  in
                        (match uu____19616 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19652 -> failwith "Impossible")))
        | uu____19660 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19684 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19684 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19697,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19704 = find1 l2  in
            (match uu____19704 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19711 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19711 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19715 = find1 l  in
            (match uu____19715 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19720 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19720
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19735 = lookup_qname env l1  in
      match uu____19735 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19738;
              FStar_Syntax_Syntax.sigrng = uu____19739;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19741;
              FStar_Syntax_Syntax.sigattrs = uu____19742;_},uu____19743),uu____19744)
          -> q
      | uu____19795 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19819 =
          let uu____19820 =
            let uu____19822 = FStar_Util.string_of_int i  in
            let uu____19824 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19822 uu____19824
             in
          failwith uu____19820  in
        let uu____19827 = lookup_datacon env lid  in
        match uu____19827 with
        | (uu____19832,t) ->
            let uu____19834 =
              let uu____19835 = FStar_Syntax_Subst.compress t  in
              uu____19835.FStar_Syntax_Syntax.n  in
            (match uu____19834 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19839) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19883 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19883
                      FStar_Pervasives_Native.fst)
             | uu____19894 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19908 = lookup_qname env l  in
      match uu____19908 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19910,uu____19911,uu____19912);
              FStar_Syntax_Syntax.sigrng = uu____19913;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19915;
              FStar_Syntax_Syntax.sigattrs = uu____19916;_},uu____19917),uu____19918)
          ->
          FStar_Util.for_some
            (fun uu___7_19971  ->
               match uu___7_19971 with
               | FStar_Syntax_Syntax.Projector uu____19973 -> true
               | uu____19979 -> false) quals
      | uu____19981 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19995 = lookup_qname env lid  in
      match uu____19995 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19997,uu____19998,uu____19999,uu____20000,uu____20001,uu____20002);
              FStar_Syntax_Syntax.sigrng = uu____20003;
              FStar_Syntax_Syntax.sigquals = uu____20004;
              FStar_Syntax_Syntax.sigmeta = uu____20005;
              FStar_Syntax_Syntax.sigattrs = uu____20006;_},uu____20007),uu____20008)
          -> true
      | uu____20066 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20080 = lookup_qname env lid  in
      match uu____20080 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20082,uu____20083,uu____20084,uu____20085,uu____20086,uu____20087);
              FStar_Syntax_Syntax.sigrng = uu____20088;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20090;
              FStar_Syntax_Syntax.sigattrs = uu____20091;_},uu____20092),uu____20093)
          ->
          FStar_Util.for_some
            (fun uu___8_20154  ->
               match uu___8_20154 with
               | FStar_Syntax_Syntax.RecordType uu____20156 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20166 -> true
               | uu____20176 -> false) quals
      | uu____20178 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20188,uu____20189);
            FStar_Syntax_Syntax.sigrng = uu____20190;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20192;
            FStar_Syntax_Syntax.sigattrs = uu____20193;_},uu____20194),uu____20195)
        ->
        FStar_Util.for_some
          (fun uu___9_20252  ->
             match uu___9_20252 with
             | FStar_Syntax_Syntax.Action uu____20254 -> true
             | uu____20256 -> false) quals
    | uu____20258 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20272 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20272
  
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
      let uu____20289 =
        let uu____20290 = FStar_Syntax_Util.un_uinst head1  in
        uu____20290.FStar_Syntax_Syntax.n  in
      match uu____20289 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20296 ->
               true
           | uu____20299 -> false)
      | uu____20301 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20315 = lookup_qname env l  in
      match uu____20315 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20318),uu____20319) ->
          FStar_Util.for_some
            (fun uu___10_20367  ->
               match uu___10_20367 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20370 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20372 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20448 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20466) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20484 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20492 ->
                 FStar_Pervasives_Native.Some true
             | uu____20511 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20514 =
        let uu____20518 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20518 mapper  in
      match uu____20514 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20578 = lookup_qname env lid  in
      match uu____20578 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20582,uu____20583,tps,uu____20585,uu____20586,uu____20587);
              FStar_Syntax_Syntax.sigrng = uu____20588;
              FStar_Syntax_Syntax.sigquals = uu____20589;
              FStar_Syntax_Syntax.sigmeta = uu____20590;
              FStar_Syntax_Syntax.sigattrs = uu____20591;_},uu____20592),uu____20593)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20659 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20705  ->
              match uu____20705 with
              | (d,uu____20714) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20730 = effect_decl_opt env l  in
      match uu____20730 with
      | FStar_Pervasives_Native.None  ->
          let uu____20745 = name_not_found l  in
          let uu____20751 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20745 uu____20751
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20774  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20793  ->
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
        let uu____20825 = FStar_Ident.lid_equals l1 l2  in
        if uu____20825
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20836 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20836
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20847 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20900  ->
                        match uu____20900 with
                        | (m1,m2,uu____20914,uu____20915,uu____20916) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20847 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20933 =
                    let uu____20939 =
                      let uu____20941 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20943 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20941
                        uu____20943
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20939)
                     in
                  FStar_Errors.raise_error uu____20933 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20953,uu____20954,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20988 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20988
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
  'Auu____21008 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21008) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21037 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21063  ->
                match uu____21063 with
                | (d,uu____21070) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21037 with
      | FStar_Pervasives_Native.None  ->
          let uu____21081 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21081
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21096 =
            let uu____21101 =
              let uu____21102 =
                FStar_All.pipe_right md.FStar_Syntax_Syntax.signature
                  FStar_Pervasives_Native.snd
                 in
              ((md.FStar_Syntax_Syntax.univs), uu____21102)  in
            inst_tscheme uu____21101  in
          (match uu____21096 with
           | (uu____21129,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21147)::(wp,uu____21149)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21205 -> failwith "Impossible"))
  
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
            let uu___1504_21255 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1504_21255.order);
              joins = (uu___1504_21255.joins)
            }  in
          let uu___1507_21264 = env  in
          {
            solver = (uu___1507_21264.solver);
            range = (uu___1507_21264.range);
            curmodule = (uu___1507_21264.curmodule);
            gamma = (uu___1507_21264.gamma);
            gamma_sig = (uu___1507_21264.gamma_sig);
            gamma_cache = (uu___1507_21264.gamma_cache);
            modules = (uu___1507_21264.modules);
            expected_typ = (uu___1507_21264.expected_typ);
            sigtab = (uu___1507_21264.sigtab);
            attrtab = (uu___1507_21264.attrtab);
            is_pattern = (uu___1507_21264.is_pattern);
            instantiate_imp = (uu___1507_21264.instantiate_imp);
            effects;
            generalize = (uu___1507_21264.generalize);
            letrecs = (uu___1507_21264.letrecs);
            top_level = (uu___1507_21264.top_level);
            check_uvars = (uu___1507_21264.check_uvars);
            use_eq = (uu___1507_21264.use_eq);
            is_iface = (uu___1507_21264.is_iface);
            admit = (uu___1507_21264.admit);
            lax = (uu___1507_21264.lax);
            lax_universes = (uu___1507_21264.lax_universes);
            phase1 = (uu___1507_21264.phase1);
            failhard = (uu___1507_21264.failhard);
            nosynth = (uu___1507_21264.nosynth);
            uvar_subtyping = (uu___1507_21264.uvar_subtyping);
            tc_term = (uu___1507_21264.tc_term);
            type_of = (uu___1507_21264.type_of);
            universe_of = (uu___1507_21264.universe_of);
            check_type_of = (uu___1507_21264.check_type_of);
            use_bv_sorts = (uu___1507_21264.use_bv_sorts);
            qtbl_name_and_index = (uu___1507_21264.qtbl_name_and_index);
            normalized_eff_names = (uu___1507_21264.normalized_eff_names);
            fv_delta_depths = (uu___1507_21264.fv_delta_depths);
            proof_ns = (uu___1507_21264.proof_ns);
            synth_hook = (uu___1507_21264.synth_hook);
            splice = (uu___1507_21264.splice);
            postprocess = (uu___1507_21264.postprocess);
            is_native_tactic = (uu___1507_21264.is_native_tactic);
            identifier_info = (uu___1507_21264.identifier_info);
            tc_hooks = (uu___1507_21264.tc_hooks);
            dsenv = (uu___1507_21264.dsenv);
            nbe = (uu___1507_21264.nbe);
            strict_args_tab = (uu___1507_21264.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____21294 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____21294  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____21452 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____21453 = l1 u t wp e  in
                                l2 u t uu____21452 uu____21453))
                | uu____21454 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21526 = inst_tscheme_with lift_t [u]  in
            match uu____21526 with
            | (uu____21533,lift_t1) ->
                let uu____21535 =
                  let uu____21542 =
                    let uu____21543 =
                      let uu____21560 =
                        let uu____21571 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21580 =
                          let uu____21591 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21591]  in
                        uu____21571 :: uu____21580  in
                      (lift_t1, uu____21560)  in
                    FStar_Syntax_Syntax.Tm_app uu____21543  in
                  FStar_Syntax_Syntax.mk uu____21542  in
                uu____21535 FStar_Pervasives_Native.None
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
            let uu____21701 = inst_tscheme_with lift_t [u]  in
            match uu____21701 with
            | (uu____21708,lift_t1) ->
                let uu____21710 =
                  let uu____21717 =
                    let uu____21718 =
                      let uu____21735 =
                        let uu____21746 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21755 =
                          let uu____21766 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21775 =
                            let uu____21786 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21786]  in
                          uu____21766 :: uu____21775  in
                        uu____21746 :: uu____21755  in
                      (lift_t1, uu____21735)  in
                    FStar_Syntax_Syntax.Tm_app uu____21718  in
                  FStar_Syntax_Syntax.mk uu____21717  in
                uu____21710 FStar_Pervasives_Native.None
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
              let uu____21888 =
                let uu____21889 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21889
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21888  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21898 =
              let uu____21900 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21900  in
            let uu____21901 =
              let uu____21903 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21931 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21931)
                 in
              FStar_Util.dflt "none" uu____21903  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21898
              uu____21901
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21960  ->
                    match uu____21960 with
                    | (e,uu____21968) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21991 =
            match uu____21991 with
            | (i,j) ->
                let uu____22002 = FStar_Ident.lid_equals i j  in
                if uu____22002
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _22009  -> FStar_Pervasives_Native.Some _22009)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____22038 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____22048 = FStar_Ident.lid_equals i k  in
                        if uu____22048
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____22062 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____22062
                                  then []
                                  else
                                    (let uu____22069 =
                                       let uu____22078 =
                                         find_edge order1 (i, k)  in
                                       let uu____22081 =
                                         find_edge order1 (k, j)  in
                                       (uu____22078, uu____22081)  in
                                     match uu____22069 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____22096 =
                                           compose_edges e1 e2  in
                                         [uu____22096]
                                     | uu____22097 -> [])))))
                 in
              FStar_List.append order1 uu____22038  in
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
                   let uu____22127 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____22130 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____22130
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____22127
                   then
                     let uu____22137 =
                       let uu____22143 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____22143)
                        in
                     let uu____22147 = get_range env  in
                     FStar_Errors.raise_error uu____22137 uu____22147
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____22225 = FStar_Ident.lid_equals i j
                                   in
                                if uu____22225
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____22277 =
                                              let uu____22286 =
                                                find_edge order2 (i, k)  in
                                              let uu____22289 =
                                                find_edge order2 (j, k)  in
                                              (uu____22286, uu____22289)  in
                                            match uu____22277 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____22331,uu____22332)
                                                     ->
                                                     let uu____22339 =
                                                       let uu____22346 =
                                                         let uu____22348 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22348
                                                          in
                                                       let uu____22351 =
                                                         let uu____22353 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22353
                                                          in
                                                       (uu____22346,
                                                         uu____22351)
                                                        in
                                                     (match uu____22339 with
                                                      | (true ,true ) ->
                                                          let uu____22370 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____22370
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
                                            | uu____22413 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1634_22486 = env.effects  in
              { decls = (uu___1634_22486.decls); order = order2; joins }  in
            let uu___1637_22487 = env  in
            {
              solver = (uu___1637_22487.solver);
              range = (uu___1637_22487.range);
              curmodule = (uu___1637_22487.curmodule);
              gamma = (uu___1637_22487.gamma);
              gamma_sig = (uu___1637_22487.gamma_sig);
              gamma_cache = (uu___1637_22487.gamma_cache);
              modules = (uu___1637_22487.modules);
              expected_typ = (uu___1637_22487.expected_typ);
              sigtab = (uu___1637_22487.sigtab);
              attrtab = (uu___1637_22487.attrtab);
              is_pattern = (uu___1637_22487.is_pattern);
              instantiate_imp = (uu___1637_22487.instantiate_imp);
              effects;
              generalize = (uu___1637_22487.generalize);
              letrecs = (uu___1637_22487.letrecs);
              top_level = (uu___1637_22487.top_level);
              check_uvars = (uu___1637_22487.check_uvars);
              use_eq = (uu___1637_22487.use_eq);
              is_iface = (uu___1637_22487.is_iface);
              admit = (uu___1637_22487.admit);
              lax = (uu___1637_22487.lax);
              lax_universes = (uu___1637_22487.lax_universes);
              phase1 = (uu___1637_22487.phase1);
              failhard = (uu___1637_22487.failhard);
              nosynth = (uu___1637_22487.nosynth);
              uvar_subtyping = (uu___1637_22487.uvar_subtyping);
              tc_term = (uu___1637_22487.tc_term);
              type_of = (uu___1637_22487.type_of);
              universe_of = (uu___1637_22487.universe_of);
              check_type_of = (uu___1637_22487.check_type_of);
              use_bv_sorts = (uu___1637_22487.use_bv_sorts);
              qtbl_name_and_index = (uu___1637_22487.qtbl_name_and_index);
              normalized_eff_names = (uu___1637_22487.normalized_eff_names);
              fv_delta_depths = (uu___1637_22487.fv_delta_depths);
              proof_ns = (uu___1637_22487.proof_ns);
              synth_hook = (uu___1637_22487.synth_hook);
              splice = (uu___1637_22487.splice);
              postprocess = (uu___1637_22487.postprocess);
              is_native_tactic = (uu___1637_22487.is_native_tactic);
              identifier_info = (uu___1637_22487.identifier_info);
              tc_hooks = (uu___1637_22487.tc_hooks);
              dsenv = (uu___1637_22487.dsenv);
              nbe = (uu___1637_22487.nbe);
              strict_args_tab = (uu___1637_22487.strict_args_tab)
            }))
      | uu____22488 -> env
  
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
        | uu____22517 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22530 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22530 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22547 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22547 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22572 =
                     let uu____22578 =
                       let uu____22580 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22588 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22599 =
                         let uu____22601 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22601  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22580 uu____22588 uu____22599
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22578)
                      in
                   FStar_Errors.raise_error uu____22572
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22609 =
                     let uu____22620 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22620 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22657  ->
                        fun uu____22658  ->
                          match (uu____22657, uu____22658) with
                          | ((x,uu____22688),(t,uu____22690)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22609
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22721 =
                     let uu___1675_22722 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1675_22722.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1675_22722.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1675_22722.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1675_22722.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22721
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22734 .
    'Auu____22734 ->
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
          let uu____22764 = effect_decl_opt env effect_name  in
          match uu____22764 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22807 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22830 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22869 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22869
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22874 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22874
                      in
                   let repr =
                     let uu____22885 =
                       let uu____22886 =
                         FStar_All.pipe_right ed.FStar_Syntax_Syntax.repr
                           FStar_Pervasives_Native.snd
                          in
                       ([], uu____22886)  in
                     inst_effect_fun_with [u_c] env ed uu____22885  in
                   let uu____22907 =
                     let uu____22910 = get_range env  in
                     let uu____22911 =
                       let uu____22918 =
                         let uu____22919 =
                           let uu____22936 =
                             let uu____22947 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22947; wp]  in
                           (repr, uu____22936)  in
                         FStar_Syntax_Syntax.Tm_app uu____22919  in
                       FStar_Syntax_Syntax.mk uu____22918  in
                     uu____22911 FStar_Pervasives_Native.None uu____22910  in
                   FStar_Pervasives_Native.Some uu____22907)
  
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
      | uu____23091 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23106 =
        let uu____23107 = FStar_Syntax_Subst.compress t  in
        uu____23107.FStar_Syntax_Syntax.n  in
      match uu____23106 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23111,c) ->
          is_reifiable_comp env c
      | uu____23133 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23153 =
           let uu____23155 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23155  in
         if uu____23153
         then
           let uu____23158 =
             let uu____23164 =
               let uu____23166 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23166
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23164)  in
           let uu____23170 = get_range env  in
           FStar_Errors.raise_error uu____23158 uu____23170
         else ());
        (let uu____23173 = effect_repr_aux true env c u_c  in
         match uu____23173 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1740_23209 = env  in
        {
          solver = (uu___1740_23209.solver);
          range = (uu___1740_23209.range);
          curmodule = (uu___1740_23209.curmodule);
          gamma = (uu___1740_23209.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1740_23209.gamma_cache);
          modules = (uu___1740_23209.modules);
          expected_typ = (uu___1740_23209.expected_typ);
          sigtab = (uu___1740_23209.sigtab);
          attrtab = (uu___1740_23209.attrtab);
          is_pattern = (uu___1740_23209.is_pattern);
          instantiate_imp = (uu___1740_23209.instantiate_imp);
          effects = (uu___1740_23209.effects);
          generalize = (uu___1740_23209.generalize);
          letrecs = (uu___1740_23209.letrecs);
          top_level = (uu___1740_23209.top_level);
          check_uvars = (uu___1740_23209.check_uvars);
          use_eq = (uu___1740_23209.use_eq);
          is_iface = (uu___1740_23209.is_iface);
          admit = (uu___1740_23209.admit);
          lax = (uu___1740_23209.lax);
          lax_universes = (uu___1740_23209.lax_universes);
          phase1 = (uu___1740_23209.phase1);
          failhard = (uu___1740_23209.failhard);
          nosynth = (uu___1740_23209.nosynth);
          uvar_subtyping = (uu___1740_23209.uvar_subtyping);
          tc_term = (uu___1740_23209.tc_term);
          type_of = (uu___1740_23209.type_of);
          universe_of = (uu___1740_23209.universe_of);
          check_type_of = (uu___1740_23209.check_type_of);
          use_bv_sorts = (uu___1740_23209.use_bv_sorts);
          qtbl_name_and_index = (uu___1740_23209.qtbl_name_and_index);
          normalized_eff_names = (uu___1740_23209.normalized_eff_names);
          fv_delta_depths = (uu___1740_23209.fv_delta_depths);
          proof_ns = (uu___1740_23209.proof_ns);
          synth_hook = (uu___1740_23209.synth_hook);
          splice = (uu___1740_23209.splice);
          postprocess = (uu___1740_23209.postprocess);
          is_native_tactic = (uu___1740_23209.is_native_tactic);
          identifier_info = (uu___1740_23209.identifier_info);
          tc_hooks = (uu___1740_23209.tc_hooks);
          dsenv = (uu___1740_23209.dsenv);
          nbe = (uu___1740_23209.nbe);
          strict_args_tab = (uu___1740_23209.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1747_23223 = env  in
      {
        solver = (uu___1747_23223.solver);
        range = (uu___1747_23223.range);
        curmodule = (uu___1747_23223.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1747_23223.gamma_sig);
        gamma_cache = (uu___1747_23223.gamma_cache);
        modules = (uu___1747_23223.modules);
        expected_typ = (uu___1747_23223.expected_typ);
        sigtab = (uu___1747_23223.sigtab);
        attrtab = (uu___1747_23223.attrtab);
        is_pattern = (uu___1747_23223.is_pattern);
        instantiate_imp = (uu___1747_23223.instantiate_imp);
        effects = (uu___1747_23223.effects);
        generalize = (uu___1747_23223.generalize);
        letrecs = (uu___1747_23223.letrecs);
        top_level = (uu___1747_23223.top_level);
        check_uvars = (uu___1747_23223.check_uvars);
        use_eq = (uu___1747_23223.use_eq);
        is_iface = (uu___1747_23223.is_iface);
        admit = (uu___1747_23223.admit);
        lax = (uu___1747_23223.lax);
        lax_universes = (uu___1747_23223.lax_universes);
        phase1 = (uu___1747_23223.phase1);
        failhard = (uu___1747_23223.failhard);
        nosynth = (uu___1747_23223.nosynth);
        uvar_subtyping = (uu___1747_23223.uvar_subtyping);
        tc_term = (uu___1747_23223.tc_term);
        type_of = (uu___1747_23223.type_of);
        universe_of = (uu___1747_23223.universe_of);
        check_type_of = (uu___1747_23223.check_type_of);
        use_bv_sorts = (uu___1747_23223.use_bv_sorts);
        qtbl_name_and_index = (uu___1747_23223.qtbl_name_and_index);
        normalized_eff_names = (uu___1747_23223.normalized_eff_names);
        fv_delta_depths = (uu___1747_23223.fv_delta_depths);
        proof_ns = (uu___1747_23223.proof_ns);
        synth_hook = (uu___1747_23223.synth_hook);
        splice = (uu___1747_23223.splice);
        postprocess = (uu___1747_23223.postprocess);
        is_native_tactic = (uu___1747_23223.is_native_tactic);
        identifier_info = (uu___1747_23223.identifier_info);
        tc_hooks = (uu___1747_23223.tc_hooks);
        dsenv = (uu___1747_23223.dsenv);
        nbe = (uu___1747_23223.nbe);
        strict_args_tab = (uu___1747_23223.strict_args_tab)
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
            (let uu___1760_23281 = env  in
             {
               solver = (uu___1760_23281.solver);
               range = (uu___1760_23281.range);
               curmodule = (uu___1760_23281.curmodule);
               gamma = rest;
               gamma_sig = (uu___1760_23281.gamma_sig);
               gamma_cache = (uu___1760_23281.gamma_cache);
               modules = (uu___1760_23281.modules);
               expected_typ = (uu___1760_23281.expected_typ);
               sigtab = (uu___1760_23281.sigtab);
               attrtab = (uu___1760_23281.attrtab);
               is_pattern = (uu___1760_23281.is_pattern);
               instantiate_imp = (uu___1760_23281.instantiate_imp);
               effects = (uu___1760_23281.effects);
               generalize = (uu___1760_23281.generalize);
               letrecs = (uu___1760_23281.letrecs);
               top_level = (uu___1760_23281.top_level);
               check_uvars = (uu___1760_23281.check_uvars);
               use_eq = (uu___1760_23281.use_eq);
               is_iface = (uu___1760_23281.is_iface);
               admit = (uu___1760_23281.admit);
               lax = (uu___1760_23281.lax);
               lax_universes = (uu___1760_23281.lax_universes);
               phase1 = (uu___1760_23281.phase1);
               failhard = (uu___1760_23281.failhard);
               nosynth = (uu___1760_23281.nosynth);
               uvar_subtyping = (uu___1760_23281.uvar_subtyping);
               tc_term = (uu___1760_23281.tc_term);
               type_of = (uu___1760_23281.type_of);
               universe_of = (uu___1760_23281.universe_of);
               check_type_of = (uu___1760_23281.check_type_of);
               use_bv_sorts = (uu___1760_23281.use_bv_sorts);
               qtbl_name_and_index = (uu___1760_23281.qtbl_name_and_index);
               normalized_eff_names = (uu___1760_23281.normalized_eff_names);
               fv_delta_depths = (uu___1760_23281.fv_delta_depths);
               proof_ns = (uu___1760_23281.proof_ns);
               synth_hook = (uu___1760_23281.synth_hook);
               splice = (uu___1760_23281.splice);
               postprocess = (uu___1760_23281.postprocess);
               is_native_tactic = (uu___1760_23281.is_native_tactic);
               identifier_info = (uu___1760_23281.identifier_info);
               tc_hooks = (uu___1760_23281.tc_hooks);
               dsenv = (uu___1760_23281.dsenv);
               nbe = (uu___1760_23281.nbe);
               strict_args_tab = (uu___1760_23281.strict_args_tab)
             }))
    | uu____23282 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23311  ->
             match uu____23311 with | (x,uu____23319) -> push_bv env1 x) env
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
            let uu___1774_23354 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1774_23354.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1774_23354.FStar_Syntax_Syntax.index);
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
      (let uu___1785_23396 = env  in
       {
         solver = (uu___1785_23396.solver);
         range = (uu___1785_23396.range);
         curmodule = (uu___1785_23396.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1785_23396.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1785_23396.sigtab);
         attrtab = (uu___1785_23396.attrtab);
         is_pattern = (uu___1785_23396.is_pattern);
         instantiate_imp = (uu___1785_23396.instantiate_imp);
         effects = (uu___1785_23396.effects);
         generalize = (uu___1785_23396.generalize);
         letrecs = (uu___1785_23396.letrecs);
         top_level = (uu___1785_23396.top_level);
         check_uvars = (uu___1785_23396.check_uvars);
         use_eq = (uu___1785_23396.use_eq);
         is_iface = (uu___1785_23396.is_iface);
         admit = (uu___1785_23396.admit);
         lax = (uu___1785_23396.lax);
         lax_universes = (uu___1785_23396.lax_universes);
         phase1 = (uu___1785_23396.phase1);
         failhard = (uu___1785_23396.failhard);
         nosynth = (uu___1785_23396.nosynth);
         uvar_subtyping = (uu___1785_23396.uvar_subtyping);
         tc_term = (uu___1785_23396.tc_term);
         type_of = (uu___1785_23396.type_of);
         universe_of = (uu___1785_23396.universe_of);
         check_type_of = (uu___1785_23396.check_type_of);
         use_bv_sorts = (uu___1785_23396.use_bv_sorts);
         qtbl_name_and_index = (uu___1785_23396.qtbl_name_and_index);
         normalized_eff_names = (uu___1785_23396.normalized_eff_names);
         fv_delta_depths = (uu___1785_23396.fv_delta_depths);
         proof_ns = (uu___1785_23396.proof_ns);
         synth_hook = (uu___1785_23396.synth_hook);
         splice = (uu___1785_23396.splice);
         postprocess = (uu___1785_23396.postprocess);
         is_native_tactic = (uu___1785_23396.is_native_tactic);
         identifier_info = (uu___1785_23396.identifier_info);
         tc_hooks = (uu___1785_23396.tc_hooks);
         dsenv = (uu___1785_23396.dsenv);
         nbe = (uu___1785_23396.nbe);
         strict_args_tab = (uu___1785_23396.strict_args_tab)
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
        let uu____23440 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23440 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23468 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23468)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1800_23484 = env  in
      {
        solver = (uu___1800_23484.solver);
        range = (uu___1800_23484.range);
        curmodule = (uu___1800_23484.curmodule);
        gamma = (uu___1800_23484.gamma);
        gamma_sig = (uu___1800_23484.gamma_sig);
        gamma_cache = (uu___1800_23484.gamma_cache);
        modules = (uu___1800_23484.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1800_23484.sigtab);
        attrtab = (uu___1800_23484.attrtab);
        is_pattern = (uu___1800_23484.is_pattern);
        instantiate_imp = (uu___1800_23484.instantiate_imp);
        effects = (uu___1800_23484.effects);
        generalize = (uu___1800_23484.generalize);
        letrecs = (uu___1800_23484.letrecs);
        top_level = (uu___1800_23484.top_level);
        check_uvars = (uu___1800_23484.check_uvars);
        use_eq = false;
        is_iface = (uu___1800_23484.is_iface);
        admit = (uu___1800_23484.admit);
        lax = (uu___1800_23484.lax);
        lax_universes = (uu___1800_23484.lax_universes);
        phase1 = (uu___1800_23484.phase1);
        failhard = (uu___1800_23484.failhard);
        nosynth = (uu___1800_23484.nosynth);
        uvar_subtyping = (uu___1800_23484.uvar_subtyping);
        tc_term = (uu___1800_23484.tc_term);
        type_of = (uu___1800_23484.type_of);
        universe_of = (uu___1800_23484.universe_of);
        check_type_of = (uu___1800_23484.check_type_of);
        use_bv_sorts = (uu___1800_23484.use_bv_sorts);
        qtbl_name_and_index = (uu___1800_23484.qtbl_name_and_index);
        normalized_eff_names = (uu___1800_23484.normalized_eff_names);
        fv_delta_depths = (uu___1800_23484.fv_delta_depths);
        proof_ns = (uu___1800_23484.proof_ns);
        synth_hook = (uu___1800_23484.synth_hook);
        splice = (uu___1800_23484.splice);
        postprocess = (uu___1800_23484.postprocess);
        is_native_tactic = (uu___1800_23484.is_native_tactic);
        identifier_info = (uu___1800_23484.identifier_info);
        tc_hooks = (uu___1800_23484.tc_hooks);
        dsenv = (uu___1800_23484.dsenv);
        nbe = (uu___1800_23484.nbe);
        strict_args_tab = (uu___1800_23484.strict_args_tab)
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
    let uu____23515 = expected_typ env_  in
    ((let uu___1807_23521 = env_  in
      {
        solver = (uu___1807_23521.solver);
        range = (uu___1807_23521.range);
        curmodule = (uu___1807_23521.curmodule);
        gamma = (uu___1807_23521.gamma);
        gamma_sig = (uu___1807_23521.gamma_sig);
        gamma_cache = (uu___1807_23521.gamma_cache);
        modules = (uu___1807_23521.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1807_23521.sigtab);
        attrtab = (uu___1807_23521.attrtab);
        is_pattern = (uu___1807_23521.is_pattern);
        instantiate_imp = (uu___1807_23521.instantiate_imp);
        effects = (uu___1807_23521.effects);
        generalize = (uu___1807_23521.generalize);
        letrecs = (uu___1807_23521.letrecs);
        top_level = (uu___1807_23521.top_level);
        check_uvars = (uu___1807_23521.check_uvars);
        use_eq = false;
        is_iface = (uu___1807_23521.is_iface);
        admit = (uu___1807_23521.admit);
        lax = (uu___1807_23521.lax);
        lax_universes = (uu___1807_23521.lax_universes);
        phase1 = (uu___1807_23521.phase1);
        failhard = (uu___1807_23521.failhard);
        nosynth = (uu___1807_23521.nosynth);
        uvar_subtyping = (uu___1807_23521.uvar_subtyping);
        tc_term = (uu___1807_23521.tc_term);
        type_of = (uu___1807_23521.type_of);
        universe_of = (uu___1807_23521.universe_of);
        check_type_of = (uu___1807_23521.check_type_of);
        use_bv_sorts = (uu___1807_23521.use_bv_sorts);
        qtbl_name_and_index = (uu___1807_23521.qtbl_name_and_index);
        normalized_eff_names = (uu___1807_23521.normalized_eff_names);
        fv_delta_depths = (uu___1807_23521.fv_delta_depths);
        proof_ns = (uu___1807_23521.proof_ns);
        synth_hook = (uu___1807_23521.synth_hook);
        splice = (uu___1807_23521.splice);
        postprocess = (uu___1807_23521.postprocess);
        is_native_tactic = (uu___1807_23521.is_native_tactic);
        identifier_info = (uu___1807_23521.identifier_info);
        tc_hooks = (uu___1807_23521.tc_hooks);
        dsenv = (uu___1807_23521.dsenv);
        nbe = (uu___1807_23521.nbe);
        strict_args_tab = (uu___1807_23521.strict_args_tab)
      }), uu____23515)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23533 =
      let uu____23536 = FStar_Ident.id_of_text ""  in [uu____23536]  in
    FStar_Ident.lid_of_ids uu____23533  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23543 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23543
        then
          let uu____23548 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23548 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1815_23576 = env  in
       {
         solver = (uu___1815_23576.solver);
         range = (uu___1815_23576.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1815_23576.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1815_23576.expected_typ);
         sigtab = (uu___1815_23576.sigtab);
         attrtab = (uu___1815_23576.attrtab);
         is_pattern = (uu___1815_23576.is_pattern);
         instantiate_imp = (uu___1815_23576.instantiate_imp);
         effects = (uu___1815_23576.effects);
         generalize = (uu___1815_23576.generalize);
         letrecs = (uu___1815_23576.letrecs);
         top_level = (uu___1815_23576.top_level);
         check_uvars = (uu___1815_23576.check_uvars);
         use_eq = (uu___1815_23576.use_eq);
         is_iface = (uu___1815_23576.is_iface);
         admit = (uu___1815_23576.admit);
         lax = (uu___1815_23576.lax);
         lax_universes = (uu___1815_23576.lax_universes);
         phase1 = (uu___1815_23576.phase1);
         failhard = (uu___1815_23576.failhard);
         nosynth = (uu___1815_23576.nosynth);
         uvar_subtyping = (uu___1815_23576.uvar_subtyping);
         tc_term = (uu___1815_23576.tc_term);
         type_of = (uu___1815_23576.type_of);
         universe_of = (uu___1815_23576.universe_of);
         check_type_of = (uu___1815_23576.check_type_of);
         use_bv_sorts = (uu___1815_23576.use_bv_sorts);
         qtbl_name_and_index = (uu___1815_23576.qtbl_name_and_index);
         normalized_eff_names = (uu___1815_23576.normalized_eff_names);
         fv_delta_depths = (uu___1815_23576.fv_delta_depths);
         proof_ns = (uu___1815_23576.proof_ns);
         synth_hook = (uu___1815_23576.synth_hook);
         splice = (uu___1815_23576.splice);
         postprocess = (uu___1815_23576.postprocess);
         is_native_tactic = (uu___1815_23576.is_native_tactic);
         identifier_info = (uu___1815_23576.identifier_info);
         tc_hooks = (uu___1815_23576.tc_hooks);
         dsenv = (uu___1815_23576.dsenv);
         nbe = (uu___1815_23576.nbe);
         strict_args_tab = (uu___1815_23576.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23628)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23632,(uu____23633,t)))::tl1
          ->
          let uu____23654 =
            let uu____23657 = FStar_Syntax_Free.uvars t  in
            ext out uu____23657  in
          aux uu____23654 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23660;
            FStar_Syntax_Syntax.index = uu____23661;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23669 =
            let uu____23672 = FStar_Syntax_Free.uvars t  in
            ext out uu____23672  in
          aux uu____23669 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23730)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23734,(uu____23735,t)))::tl1
          ->
          let uu____23756 =
            let uu____23759 = FStar_Syntax_Free.univs t  in
            ext out uu____23759  in
          aux uu____23756 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23762;
            FStar_Syntax_Syntax.index = uu____23763;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23771 =
            let uu____23774 = FStar_Syntax_Free.univs t  in
            ext out uu____23774  in
          aux uu____23771 tl1
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
          let uu____23836 = FStar_Util.set_add uname out  in
          aux uu____23836 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23839,(uu____23840,t)))::tl1
          ->
          let uu____23861 =
            let uu____23864 = FStar_Syntax_Free.univnames t  in
            ext out uu____23864  in
          aux uu____23861 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23867;
            FStar_Syntax_Syntax.index = uu____23868;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23876 =
            let uu____23879 = FStar_Syntax_Free.univnames t  in
            ext out uu____23879  in
          aux uu____23876 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_23900  ->
            match uu___11_23900 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23904 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23917 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23928 =
      let uu____23937 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23937
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23928 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23985 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_23998  ->
              match uu___12_23998 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24001 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24001
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24007) ->
                  let uu____24024 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24024))
       in
    FStar_All.pipe_right uu____23985 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24038  ->
    match uu___13_24038 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24044 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24044
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24067  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24122) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24155,uu____24156) -> false  in
      let uu____24170 =
        FStar_List.tryFind
          (fun uu____24192  ->
             match uu____24192 with | (p,uu____24203) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24170 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24222,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24252 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24252
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1958_24274 = e  in
        {
          solver = (uu___1958_24274.solver);
          range = (uu___1958_24274.range);
          curmodule = (uu___1958_24274.curmodule);
          gamma = (uu___1958_24274.gamma);
          gamma_sig = (uu___1958_24274.gamma_sig);
          gamma_cache = (uu___1958_24274.gamma_cache);
          modules = (uu___1958_24274.modules);
          expected_typ = (uu___1958_24274.expected_typ);
          sigtab = (uu___1958_24274.sigtab);
          attrtab = (uu___1958_24274.attrtab);
          is_pattern = (uu___1958_24274.is_pattern);
          instantiate_imp = (uu___1958_24274.instantiate_imp);
          effects = (uu___1958_24274.effects);
          generalize = (uu___1958_24274.generalize);
          letrecs = (uu___1958_24274.letrecs);
          top_level = (uu___1958_24274.top_level);
          check_uvars = (uu___1958_24274.check_uvars);
          use_eq = (uu___1958_24274.use_eq);
          is_iface = (uu___1958_24274.is_iface);
          admit = (uu___1958_24274.admit);
          lax = (uu___1958_24274.lax);
          lax_universes = (uu___1958_24274.lax_universes);
          phase1 = (uu___1958_24274.phase1);
          failhard = (uu___1958_24274.failhard);
          nosynth = (uu___1958_24274.nosynth);
          uvar_subtyping = (uu___1958_24274.uvar_subtyping);
          tc_term = (uu___1958_24274.tc_term);
          type_of = (uu___1958_24274.type_of);
          universe_of = (uu___1958_24274.universe_of);
          check_type_of = (uu___1958_24274.check_type_of);
          use_bv_sorts = (uu___1958_24274.use_bv_sorts);
          qtbl_name_and_index = (uu___1958_24274.qtbl_name_and_index);
          normalized_eff_names = (uu___1958_24274.normalized_eff_names);
          fv_delta_depths = (uu___1958_24274.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1958_24274.synth_hook);
          splice = (uu___1958_24274.splice);
          postprocess = (uu___1958_24274.postprocess);
          is_native_tactic = (uu___1958_24274.is_native_tactic);
          identifier_info = (uu___1958_24274.identifier_info);
          tc_hooks = (uu___1958_24274.tc_hooks);
          dsenv = (uu___1958_24274.dsenv);
          nbe = (uu___1958_24274.nbe);
          strict_args_tab = (uu___1958_24274.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1967_24322 = e  in
      {
        solver = (uu___1967_24322.solver);
        range = (uu___1967_24322.range);
        curmodule = (uu___1967_24322.curmodule);
        gamma = (uu___1967_24322.gamma);
        gamma_sig = (uu___1967_24322.gamma_sig);
        gamma_cache = (uu___1967_24322.gamma_cache);
        modules = (uu___1967_24322.modules);
        expected_typ = (uu___1967_24322.expected_typ);
        sigtab = (uu___1967_24322.sigtab);
        attrtab = (uu___1967_24322.attrtab);
        is_pattern = (uu___1967_24322.is_pattern);
        instantiate_imp = (uu___1967_24322.instantiate_imp);
        effects = (uu___1967_24322.effects);
        generalize = (uu___1967_24322.generalize);
        letrecs = (uu___1967_24322.letrecs);
        top_level = (uu___1967_24322.top_level);
        check_uvars = (uu___1967_24322.check_uvars);
        use_eq = (uu___1967_24322.use_eq);
        is_iface = (uu___1967_24322.is_iface);
        admit = (uu___1967_24322.admit);
        lax = (uu___1967_24322.lax);
        lax_universes = (uu___1967_24322.lax_universes);
        phase1 = (uu___1967_24322.phase1);
        failhard = (uu___1967_24322.failhard);
        nosynth = (uu___1967_24322.nosynth);
        uvar_subtyping = (uu___1967_24322.uvar_subtyping);
        tc_term = (uu___1967_24322.tc_term);
        type_of = (uu___1967_24322.type_of);
        universe_of = (uu___1967_24322.universe_of);
        check_type_of = (uu___1967_24322.check_type_of);
        use_bv_sorts = (uu___1967_24322.use_bv_sorts);
        qtbl_name_and_index = (uu___1967_24322.qtbl_name_and_index);
        normalized_eff_names = (uu___1967_24322.normalized_eff_names);
        fv_delta_depths = (uu___1967_24322.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1967_24322.synth_hook);
        splice = (uu___1967_24322.splice);
        postprocess = (uu___1967_24322.postprocess);
        is_native_tactic = (uu___1967_24322.is_native_tactic);
        identifier_info = (uu___1967_24322.identifier_info);
        tc_hooks = (uu___1967_24322.tc_hooks);
        dsenv = (uu___1967_24322.dsenv);
        nbe = (uu___1967_24322.nbe);
        strict_args_tab = (uu___1967_24322.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24338 = FStar_Syntax_Free.names t  in
      let uu____24341 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24338 uu____24341
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24364 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24364
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24374 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24374
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24395 =
      match uu____24395 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24415 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24415)
       in
    let uu____24423 =
      let uu____24427 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24427 FStar_List.rev  in
    FStar_All.pipe_right uu____24423 (FStar_String.concat " ")
  
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
                  (let uu____24497 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24497 with
                   | FStar_Pervasives_Native.Some uu____24501 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24504 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24514;
        univ_ineqs = uu____24515; implicits = uu____24516;_} -> true
    | uu____24528 -> false
  
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
          let uu___2011_24559 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2011_24559.deferred);
            univ_ineqs = (uu___2011_24559.univ_ineqs);
            implicits = (uu___2011_24559.implicits)
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
          let uu____24598 = FStar_Options.defensive ()  in
          if uu____24598
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24604 =
              let uu____24606 =
                let uu____24608 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24608  in
              Prims.op_Negation uu____24606  in
            (if uu____24604
             then
               let uu____24615 =
                 let uu____24621 =
                   let uu____24623 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24625 =
                     let uu____24627 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24627
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24623 uu____24625
                    in
                 (FStar_Errors.Warning_Defensive, uu____24621)  in
               FStar_Errors.log_issue rng uu____24615
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
          let uu____24667 =
            let uu____24669 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24669  in
          if uu____24667
          then ()
          else
            (let uu____24674 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24674 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24700 =
            let uu____24702 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24702  in
          if uu____24700
          then ()
          else
            (let uu____24707 = bound_vars e  in
             def_check_closed_in rng msg uu____24707 t)
  
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
          let uu___2048_24746 = g  in
          let uu____24747 =
            let uu____24748 =
              let uu____24749 =
                let uu____24756 =
                  let uu____24757 =
                    let uu____24774 =
                      let uu____24785 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24785]  in
                    (f, uu____24774)  in
                  FStar_Syntax_Syntax.Tm_app uu____24757  in
                FStar_Syntax_Syntax.mk uu____24756  in
              uu____24749 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24822  -> FStar_TypeChecker_Common.NonTrivial _24822)
              uu____24748
             in
          {
            guard_f = uu____24747;
            deferred = (uu___2048_24746.deferred);
            univ_ineqs = (uu___2048_24746.univ_ineqs);
            implicits = (uu___2048_24746.implicits)
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
          let uu___2055_24840 = g  in
          let uu____24841 =
            let uu____24842 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24842  in
          {
            guard_f = uu____24841;
            deferred = (uu___2055_24840.deferred);
            univ_ineqs = (uu___2055_24840.univ_ineqs);
            implicits = (uu___2055_24840.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2060_24859 = g  in
          let uu____24860 =
            let uu____24861 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24861  in
          {
            guard_f = uu____24860;
            deferred = (uu___2060_24859.deferred);
            univ_ineqs = (uu___2060_24859.univ_ineqs);
            implicits = (uu___2060_24859.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2064_24863 = g  in
          let uu____24864 =
            let uu____24865 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24865  in
          {
            guard_f = uu____24864;
            deferred = (uu___2064_24863.deferred);
            univ_ineqs = (uu___2064_24863.univ_ineqs);
            implicits = (uu___2064_24863.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24872 ->
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
          let uu____24889 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24889
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24896 =
      let uu____24897 = FStar_Syntax_Util.unmeta t  in
      uu____24897.FStar_Syntax_Syntax.n  in
    match uu____24896 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24901 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24944 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24944;
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
                       let uu____25039 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25039
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2119_25046 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2119_25046.deferred);
              univ_ineqs = (uu___2119_25046.univ_ineqs);
              implicits = (uu___2119_25046.implicits)
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
               let uu____25080 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25080
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
            let uu___2134_25107 = g  in
            let uu____25108 =
              let uu____25109 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25109  in
            {
              guard_f = uu____25108;
              deferred = (uu___2134_25107.deferred);
              univ_ineqs = (uu___2134_25107.univ_ineqs);
              implicits = (uu___2134_25107.implicits)
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
              let uu____25167 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25167 with
              | FStar_Pervasives_Native.Some
                  (uu____25192::(tm,uu____25194)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25258 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25276 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25276;
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
                      let uu___2156_25308 = trivial_guard  in
                      {
                        guard_f = (uu___2156_25308.guard_f);
                        deferred = (uu___2156_25308.deferred);
                        univ_ineqs = (uu___2156_25308.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25326  -> ());
    push = (fun uu____25328  -> ());
    pop = (fun uu____25331  -> ());
    snapshot =
      (fun uu____25334  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25353  -> fun uu____25354  -> ());
    encode_sig = (fun uu____25369  -> fun uu____25370  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25376 =
             let uu____25383 = FStar_Options.peek ()  in (e, g, uu____25383)
              in
           [uu____25376]);
    solve = (fun uu____25399  -> fun uu____25400  -> fun uu____25401  -> ());
    finish = (fun uu____25408  -> ());
    refresh = (fun uu____25410  -> ())
  } 