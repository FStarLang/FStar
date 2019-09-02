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
          let uu____15022 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15024 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15022 uu____15024
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
        fun uu____15051  ->
          match uu____15051 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15065 =
                    let uu____15067 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15071 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15075 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15077 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15067 uu____15071 uu____15075 uu____15077
                     in
                  failwith uu____15065)
               else ();
               (let uu____15082 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15082))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15100 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15111 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15122 -> false
  
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
             | ([],uu____15170) -> Maybe
             | (uu____15177,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15197 -> No  in
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
          let uu____15291 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15291 with
          | FStar_Pervasives_Native.None  ->
              let uu____15314 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15358  ->
                     match uu___2_15358 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15397 = FStar_Ident.lid_equals lid l  in
                         if uu____15397
                         then
                           let uu____15420 =
                             let uu____15439 =
                               let uu____15454 = inst_tscheme t  in
                               FStar_Util.Inl uu____15454  in
                             let uu____15469 = FStar_Ident.range_of_lid l  in
                             (uu____15439, uu____15469)  in
                           FStar_Pervasives_Native.Some uu____15420
                         else FStar_Pervasives_Native.None
                     | uu____15522 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15314
                (fun uu____15560  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15569  ->
                        match uu___3_15569 with
                        | (uu____15572,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15574);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15575;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15576;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15577;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15578;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15598 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15598
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
                                  uu____15650 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15657 -> cache t  in
                            let uu____15658 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15658 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15664 =
                                   let uu____15665 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15665)
                                    in
                                 maybe_cache uu____15664)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15736 = find_in_sigtab env lid  in
         match uu____15736 with
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
      let uu____15817 = lookup_qname env lid  in
      match uu____15817 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15838,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15952 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15952 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15997 =
          let uu____16000 = lookup_attr env1 attr  in se1 :: uu____16000  in
        FStar_Util.smap_add (attrtab env1) attr uu____15997  in
      FStar_List.iter
        (fun attr  ->
           let uu____16010 =
             let uu____16011 = FStar_Syntax_Subst.compress attr  in
             uu____16011.FStar_Syntax_Syntax.n  in
           match uu____16010 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16015 =
                 let uu____16017 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16017.FStar_Ident.str  in
               add_one1 env se uu____16015
           | uu____16018 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16041) ->
          add_sigelts env ses
      | uu____16050 ->
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
        (fun uu___4_16088  ->
           match uu___4_16088 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16106 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16168,lb::[]),uu____16170) ->
            let uu____16179 =
              let uu____16188 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16197 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16188, uu____16197)  in
            FStar_Pervasives_Native.Some uu____16179
        | FStar_Syntax_Syntax.Sig_let ((uu____16210,lbs),uu____16212) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16244 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16257 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16257
                     then
                       let uu____16270 =
                         let uu____16279 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16288 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16279, uu____16288)  in
                       FStar_Pervasives_Native.Some uu____16270
                     else FStar_Pervasives_Native.None)
        | uu____16311 -> FStar_Pervasives_Native.None
  
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
                    let uu____16403 =
                      let uu____16405 =
                        let uu____16407 =
                          let uu____16409 =
                            let uu____16411 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16417 =
                              let uu____16419 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16419  in
                            Prims.op_Hat uu____16411 uu____16417  in
                          Prims.op_Hat ", expected " uu____16409  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16407
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16405
                       in
                    failwith uu____16403
                  else ());
             (let uu____16426 =
                let uu____16435 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16435, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16426))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16455,uu____16456) ->
            let uu____16461 =
              let uu____16470 =
                let uu____16475 =
                  let uu____16476 =
                    let uu____16479 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16479  in
                  (us, uu____16476)  in
                inst_ts us_opt uu____16475  in
              (uu____16470, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16461
        | uu____16498 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16587 =
          match uu____16587 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16683,uvs,t,uu____16686,uu____16687,uu____16688);
                      FStar_Syntax_Syntax.sigrng = uu____16689;
                      FStar_Syntax_Syntax.sigquals = uu____16690;
                      FStar_Syntax_Syntax.sigmeta = uu____16691;
                      FStar_Syntax_Syntax.sigattrs = uu____16692;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16715 =
                     let uu____16724 = inst_tscheme1 (uvs, t)  in
                     (uu____16724, rng)  in
                   FStar_Pervasives_Native.Some uu____16715
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16748;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16750;
                      FStar_Syntax_Syntax.sigattrs = uu____16751;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16768 =
                     let uu____16770 = in_cur_mod env l  in uu____16770 = Yes
                      in
                   if uu____16768
                   then
                     let uu____16782 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16782
                      then
                        let uu____16798 =
                          let uu____16807 = inst_tscheme1 (uvs, t)  in
                          (uu____16807, rng)  in
                        FStar_Pervasives_Native.Some uu____16798
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16840 =
                        let uu____16849 = inst_tscheme1 (uvs, t)  in
                        (uu____16849, rng)  in
                      FStar_Pervasives_Native.Some uu____16840)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16874,uu____16875);
                      FStar_Syntax_Syntax.sigrng = uu____16876;
                      FStar_Syntax_Syntax.sigquals = uu____16877;
                      FStar_Syntax_Syntax.sigmeta = uu____16878;
                      FStar_Syntax_Syntax.sigattrs = uu____16879;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16920 =
                          let uu____16929 = inst_tscheme1 (uvs, k)  in
                          (uu____16929, rng)  in
                        FStar_Pervasives_Native.Some uu____16920
                    | uu____16950 ->
                        let uu____16951 =
                          let uu____16960 =
                            let uu____16965 =
                              let uu____16966 =
                                let uu____16969 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16969
                                 in
                              (uvs, uu____16966)  in
                            inst_tscheme1 uu____16965  in
                          (uu____16960, rng)  in
                        FStar_Pervasives_Native.Some uu____16951)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16992,uu____16993);
                      FStar_Syntax_Syntax.sigrng = uu____16994;
                      FStar_Syntax_Syntax.sigquals = uu____16995;
                      FStar_Syntax_Syntax.sigmeta = uu____16996;
                      FStar_Syntax_Syntax.sigattrs = uu____16997;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17039 =
                          let uu____17048 = inst_tscheme_with (uvs, k) us  in
                          (uu____17048, rng)  in
                        FStar_Pervasives_Native.Some uu____17039
                    | uu____17069 ->
                        let uu____17070 =
                          let uu____17079 =
                            let uu____17084 =
                              let uu____17085 =
                                let uu____17088 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17088
                                 in
                              (uvs, uu____17085)  in
                            inst_tscheme_with uu____17084 us  in
                          (uu____17079, rng)  in
                        FStar_Pervasives_Native.Some uu____17070)
               | FStar_Util.Inr se ->
                   let uu____17124 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17145;
                          FStar_Syntax_Syntax.sigrng = uu____17146;
                          FStar_Syntax_Syntax.sigquals = uu____17147;
                          FStar_Syntax_Syntax.sigmeta = uu____17148;
                          FStar_Syntax_Syntax.sigattrs = uu____17149;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17164 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17124
                     (FStar_Util.map_option
                        (fun uu____17212  ->
                           match uu____17212 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17243 =
          let uu____17254 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17254 mapper  in
        match uu____17243 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17328 =
              let uu____17339 =
                let uu____17346 =
                  let uu___851_17349 = t  in
                  let uu____17350 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___851_17349.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17350;
                    FStar_Syntax_Syntax.vars =
                      (uu___851_17349.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17346)  in
              (uu____17339, r)  in
            FStar_Pervasives_Native.Some uu____17328
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17399 = lookup_qname env l  in
      match uu____17399 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17420 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17474 = try_lookup_bv env bv  in
      match uu____17474 with
      | FStar_Pervasives_Native.None  ->
          let uu____17489 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17489 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17505 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17506 =
            let uu____17507 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17507  in
          (uu____17505, uu____17506)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17529 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17529 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17595 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17595  in
          let uu____17596 =
            let uu____17605 =
              let uu____17610 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17610)  in
            (uu____17605, r1)  in
          FStar_Pervasives_Native.Some uu____17596
  
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
        let uu____17645 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17645 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17678,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17703 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17703  in
            let uu____17704 =
              let uu____17709 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17709, r1)  in
            FStar_Pervasives_Native.Some uu____17704
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17733 = try_lookup_lid env l  in
      match uu____17733 with
      | FStar_Pervasives_Native.None  ->
          let uu____17760 = name_not_found l  in
          let uu____17766 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17760 uu____17766
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17809  ->
              match uu___5_17809 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17813 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17834 = lookup_qname env lid  in
      match uu____17834 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17843,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17846;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17848;
              FStar_Syntax_Syntax.sigattrs = uu____17849;_},FStar_Pervasives_Native.None
            ),uu____17850)
          ->
          let uu____17899 =
            let uu____17906 =
              let uu____17907 =
                let uu____17910 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17910 t  in
              (uvs, uu____17907)  in
            (uu____17906, q)  in
          FStar_Pervasives_Native.Some uu____17899
      | uu____17923 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17945 = lookup_qname env lid  in
      match uu____17945 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17950,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17953;
              FStar_Syntax_Syntax.sigquals = uu____17954;
              FStar_Syntax_Syntax.sigmeta = uu____17955;
              FStar_Syntax_Syntax.sigattrs = uu____17956;_},FStar_Pervasives_Native.None
            ),uu____17957)
          ->
          let uu____18006 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18006 (uvs, t)
      | uu____18011 ->
          let uu____18012 = name_not_found lid  in
          let uu____18018 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18012 uu____18018
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18038 = lookup_qname env lid  in
      match uu____18038 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18043,uvs,t,uu____18046,uu____18047,uu____18048);
              FStar_Syntax_Syntax.sigrng = uu____18049;
              FStar_Syntax_Syntax.sigquals = uu____18050;
              FStar_Syntax_Syntax.sigmeta = uu____18051;
              FStar_Syntax_Syntax.sigattrs = uu____18052;_},FStar_Pervasives_Native.None
            ),uu____18053)
          ->
          let uu____18108 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18108 (uvs, t)
      | uu____18113 ->
          let uu____18114 = name_not_found lid  in
          let uu____18120 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18114 uu____18120
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18143 = lookup_qname env lid  in
      match uu____18143 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18151,uu____18152,uu____18153,uu____18154,uu____18155,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18157;
              FStar_Syntax_Syntax.sigquals = uu____18158;
              FStar_Syntax_Syntax.sigmeta = uu____18159;
              FStar_Syntax_Syntax.sigattrs = uu____18160;_},uu____18161),uu____18162)
          -> (true, dcs)
      | uu____18225 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18241 = lookup_qname env lid  in
      match uu____18241 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18242,uu____18243,uu____18244,l,uu____18246,uu____18247);
              FStar_Syntax_Syntax.sigrng = uu____18248;
              FStar_Syntax_Syntax.sigquals = uu____18249;
              FStar_Syntax_Syntax.sigmeta = uu____18250;
              FStar_Syntax_Syntax.sigattrs = uu____18251;_},uu____18252),uu____18253)
          -> l
      | uu____18310 ->
          let uu____18311 =
            let uu____18313 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18313  in
          failwith uu____18311
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18383)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18440) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18464 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18464
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18499 -> FStar_Pervasives_Native.None)
          | uu____18508 -> FStar_Pervasives_Native.None
  
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
        let uu____18570 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18570
  
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
        let uu____18603 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18603
  
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
             (FStar_Util.Inl uu____18655,uu____18656) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18705),uu____18706) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18755 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18773 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18783 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18800 ->
                  let uu____18807 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18807
              | FStar_Syntax_Syntax.Sig_let ((uu____18808,lbs),uu____18810)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18826 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18826
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18833 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18841 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18842 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18849 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18850 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18851 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18852 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18865 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18883 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18883
           (fun d_opt  ->
              let uu____18896 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18896
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18906 =
                   let uu____18909 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18909  in
                 match uu____18906 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18910 =
                       let uu____18912 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18912
                        in
                     failwith uu____18910
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18917 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18917
                       then
                         let uu____18920 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18922 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18924 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18920 uu____18922 uu____18924
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
        (FStar_Util.Inr (se,uu____18949),uu____18950) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18999 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19021),uu____19022) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19071 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19093 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19093
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19116 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19116 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19140 =
                      let uu____19141 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19141.FStar_Syntax_Syntax.n  in
                    match uu____19140 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19146 -> false))
  
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
        let uu____19183 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19183.FStar_Ident.str  in
      let uu____19184 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19184 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19212 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19212  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____19240 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____19240)
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
      let uu____19290 = lookup_qname env ftv  in
      match uu____19290 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19294) ->
          let uu____19339 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19339 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19360,t),r) ->
               let uu____19375 =
                 let uu____19376 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19376 t  in
               FStar_Pervasives_Native.Some uu____19375)
      | uu____19377 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19389 = try_lookup_effect_lid env ftv  in
      match uu____19389 with
      | FStar_Pervasives_Native.None  ->
          let uu____19392 = name_not_found ftv  in
          let uu____19398 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19392 uu____19398
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
        let uu____19422 = lookup_qname env lid0  in
        match uu____19422 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19433);
                FStar_Syntax_Syntax.sigrng = uu____19434;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19436;
                FStar_Syntax_Syntax.sigattrs = uu____19437;_},FStar_Pervasives_Native.None
              ),uu____19438)
            ->
            let lid1 =
              let uu____19492 =
                let uu____19493 = FStar_Ident.range_of_lid lid  in
                let uu____19494 =
                  let uu____19495 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19495  in
                FStar_Range.set_use_range uu____19493 uu____19494  in
              FStar_Ident.set_lid_range lid uu____19492  in
            let uu____19496 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19502  ->
                      match uu___6_19502 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19505 -> false))
               in
            if uu____19496
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19524 =
                      let uu____19526 =
                        let uu____19528 = get_range env  in
                        FStar_Range.string_of_range uu____19528  in
                      let uu____19529 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19531 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19526 uu____19529 uu____19531
                       in
                    failwith uu____19524)
                  in
               match (binders, univs1) with
               | ([],uu____19552) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19578,uu____19579::uu____19580::uu____19581) ->
                   let uu____19602 =
                     let uu____19604 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19606 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19604 uu____19606
                      in
                   failwith uu____19602
               | uu____19617 ->
                   let uu____19632 =
                     let uu____19637 =
                       let uu____19638 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19638)  in
                     inst_tscheme_with uu____19637 insts  in
                   (match uu____19632 with
                    | (uu____19651,t) ->
                        let t1 =
                          let uu____19654 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19654 t  in
                        let uu____19655 =
                          let uu____19656 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19656.FStar_Syntax_Syntax.n  in
                        (match uu____19655 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19691 -> failwith "Impossible")))
        | uu____19699 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19723 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19723 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19736,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19743 = find1 l2  in
            (match uu____19743 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19750 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19750 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19754 = find1 l  in
            (match uu____19754 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19759 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19759
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19774 = lookup_qname env l1  in
      match uu____19774 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19777;
              FStar_Syntax_Syntax.sigrng = uu____19778;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19780;
              FStar_Syntax_Syntax.sigattrs = uu____19781;_},uu____19782),uu____19783)
          -> q
      | uu____19834 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19858 =
          let uu____19859 =
            let uu____19861 = FStar_Util.string_of_int i  in
            let uu____19863 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19861 uu____19863
             in
          failwith uu____19859  in
        let uu____19866 = lookup_datacon env lid  in
        match uu____19866 with
        | (uu____19871,t) ->
            let uu____19873 =
              let uu____19874 = FStar_Syntax_Subst.compress t  in
              uu____19874.FStar_Syntax_Syntax.n  in
            (match uu____19873 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19878) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19922 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19922
                      FStar_Pervasives_Native.fst)
             | uu____19933 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19947 = lookup_qname env l  in
      match uu____19947 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19949,uu____19950,uu____19951);
              FStar_Syntax_Syntax.sigrng = uu____19952;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19954;
              FStar_Syntax_Syntax.sigattrs = uu____19955;_},uu____19956),uu____19957)
          ->
          FStar_Util.for_some
            (fun uu___7_20010  ->
               match uu___7_20010 with
               | FStar_Syntax_Syntax.Projector uu____20012 -> true
               | uu____20018 -> false) quals
      | uu____20020 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20034 = lookup_qname env lid  in
      match uu____20034 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20036,uu____20037,uu____20038,uu____20039,uu____20040,uu____20041);
              FStar_Syntax_Syntax.sigrng = uu____20042;
              FStar_Syntax_Syntax.sigquals = uu____20043;
              FStar_Syntax_Syntax.sigmeta = uu____20044;
              FStar_Syntax_Syntax.sigattrs = uu____20045;_},uu____20046),uu____20047)
          -> true
      | uu____20105 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20119 = lookup_qname env lid  in
      match uu____20119 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20121,uu____20122,uu____20123,uu____20124,uu____20125,uu____20126);
              FStar_Syntax_Syntax.sigrng = uu____20127;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20129;
              FStar_Syntax_Syntax.sigattrs = uu____20130;_},uu____20131),uu____20132)
          ->
          FStar_Util.for_some
            (fun uu___8_20193  ->
               match uu___8_20193 with
               | FStar_Syntax_Syntax.RecordType uu____20195 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20205 -> true
               | uu____20215 -> false) quals
      | uu____20217 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20227,uu____20228);
            FStar_Syntax_Syntax.sigrng = uu____20229;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20231;
            FStar_Syntax_Syntax.sigattrs = uu____20232;_},uu____20233),uu____20234)
        ->
        FStar_Util.for_some
          (fun uu___9_20291  ->
             match uu___9_20291 with
             | FStar_Syntax_Syntax.Action uu____20293 -> true
             | uu____20295 -> false) quals
    | uu____20297 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20311 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20311
  
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
      let uu____20328 =
        let uu____20329 = FStar_Syntax_Util.un_uinst head1  in
        uu____20329.FStar_Syntax_Syntax.n  in
      match uu____20328 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20335 ->
               true
           | uu____20338 -> false)
      | uu____20340 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20354 = lookup_qname env l  in
      match uu____20354 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20357),uu____20358) ->
          FStar_Util.for_some
            (fun uu___10_20406  ->
               match uu___10_20406 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20409 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20411 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20487 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20505) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20523 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20531 ->
                 FStar_Pervasives_Native.Some true
             | uu____20550 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20553 =
        let uu____20557 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20557 mapper  in
      match uu____20553 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20617 = lookup_qname env lid  in
      match uu____20617 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20621,uu____20622,tps,uu____20624,uu____20625,uu____20626);
              FStar_Syntax_Syntax.sigrng = uu____20627;
              FStar_Syntax_Syntax.sigquals = uu____20628;
              FStar_Syntax_Syntax.sigmeta = uu____20629;
              FStar_Syntax_Syntax.sigattrs = uu____20630;_},uu____20631),uu____20632)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20698 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20744  ->
              match uu____20744 with
              | (d,uu____20753) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20769 = effect_decl_opt env l  in
      match uu____20769 with
      | FStar_Pervasives_Native.None  ->
          let uu____20784 = name_not_found l  in
          let uu____20790 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20784 uu____20790
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20813  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20832  ->
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
        let uu____20864 = FStar_Ident.lid_equals l1 l2  in
        if uu____20864
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20875 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20875
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20886 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20939  ->
                        match uu____20939 with
                        | (m1,m2,uu____20953,uu____20954,uu____20955) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20886 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20972 =
                    let uu____20978 =
                      let uu____20980 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20982 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20980
                        uu____20982
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20978)
                     in
                  FStar_Errors.raise_error uu____20972 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20992,uu____20993,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21027 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21027
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
  'Auu____21047 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21047) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21076 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21102  ->
                match uu____21102 with
                | (d,uu____21109) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21076 with
      | FStar_Pervasives_Native.None  ->
          let uu____21120 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21120
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21135 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21135 with
           | (uu____21146,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21164)::(wp,uu____21166)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21222 -> failwith "Impossible"))
  
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
        | uu____21287 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21300 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21300 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21317 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21317 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21342 =
                     let uu____21348 =
                       let uu____21350 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____21358 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____21369 =
                         let uu____21371 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____21371  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21350 uu____21358 uu____21369
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21348)
                      in
                   FStar_Errors.raise_error uu____21342
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____21379 =
                     let uu____21390 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____21390 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____21427  ->
                        fun uu____21428  ->
                          match (uu____21427, uu____21428) with
                          | ((x,uu____21458),(t,uu____21460)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21379
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____21491 =
                     let uu___1539_21492 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1539_21492.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1539_21492.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1539_21492.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1539_21492.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____21491
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____21504 .
    'Auu____21504 ->
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
          let uu____21534 = effect_decl_opt env effect_name  in
          match uu____21534 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____21577 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____21600 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____21639 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____21639
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____21644 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____21644
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____21655 =
                     let uu____21658 = get_range env  in
                     let uu____21659 =
                       let uu____21666 =
                         let uu____21667 =
                           let uu____21684 =
                             let uu____21695 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____21695; wp]  in
                           (repr, uu____21684)  in
                         FStar_Syntax_Syntax.Tm_app uu____21667  in
                       FStar_Syntax_Syntax.mk uu____21666  in
                     uu____21659 FStar_Pervasives_Native.None uu____21658  in
                   FStar_Pervasives_Native.Some uu____21655)
  
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
      | uu____21839 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21854 =
        let uu____21855 = FStar_Syntax_Subst.compress t  in
        uu____21855.FStar_Syntax_Syntax.n  in
      match uu____21854 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____21859,c) ->
          is_reifiable_comp env c
      | uu____21881 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____21901 =
           let uu____21903 = is_reifiable_effect env l  in
           Prims.op_Negation uu____21903  in
         if uu____21901
         then
           let uu____21906 =
             let uu____21912 =
               let uu____21914 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____21914
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____21912)  in
           let uu____21918 = get_range env  in
           FStar_Errors.raise_error uu____21906 uu____21918
         else ());
        (let uu____21921 = effect_repr_aux true env c u_c  in
         match uu____21921 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1604_21957 = env  in
        {
          solver = (uu___1604_21957.solver);
          range = (uu___1604_21957.range);
          curmodule = (uu___1604_21957.curmodule);
          gamma = (uu___1604_21957.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1604_21957.gamma_cache);
          modules = (uu___1604_21957.modules);
          expected_typ = (uu___1604_21957.expected_typ);
          sigtab = (uu___1604_21957.sigtab);
          attrtab = (uu___1604_21957.attrtab);
          is_pattern = (uu___1604_21957.is_pattern);
          instantiate_imp = (uu___1604_21957.instantiate_imp);
          effects = (uu___1604_21957.effects);
          generalize = (uu___1604_21957.generalize);
          letrecs = (uu___1604_21957.letrecs);
          top_level = (uu___1604_21957.top_level);
          check_uvars = (uu___1604_21957.check_uvars);
          use_eq = (uu___1604_21957.use_eq);
          is_iface = (uu___1604_21957.is_iface);
          admit = (uu___1604_21957.admit);
          lax = (uu___1604_21957.lax);
          lax_universes = (uu___1604_21957.lax_universes);
          phase1 = (uu___1604_21957.phase1);
          failhard = (uu___1604_21957.failhard);
          nosynth = (uu___1604_21957.nosynth);
          uvar_subtyping = (uu___1604_21957.uvar_subtyping);
          tc_term = (uu___1604_21957.tc_term);
          type_of = (uu___1604_21957.type_of);
          universe_of = (uu___1604_21957.universe_of);
          check_type_of = (uu___1604_21957.check_type_of);
          use_bv_sorts = (uu___1604_21957.use_bv_sorts);
          qtbl_name_and_index = (uu___1604_21957.qtbl_name_and_index);
          normalized_eff_names = (uu___1604_21957.normalized_eff_names);
          fv_delta_depths = (uu___1604_21957.fv_delta_depths);
          proof_ns = (uu___1604_21957.proof_ns);
          synth_hook = (uu___1604_21957.synth_hook);
          splice = (uu___1604_21957.splice);
          postprocess = (uu___1604_21957.postprocess);
          is_native_tactic = (uu___1604_21957.is_native_tactic);
          identifier_info = (uu___1604_21957.identifier_info);
          tc_hooks = (uu___1604_21957.tc_hooks);
          dsenv = (uu___1604_21957.dsenv);
          nbe = (uu___1604_21957.nbe);
          strict_args_tab = (uu___1604_21957.strict_args_tab)
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
    fun uu____21976  ->
      match uu____21976 with
      | (ed,quals) ->
          let effects =
            let uu___1613_21990 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1613_21990.order);
              joins = (uu___1613_21990.joins)
            }  in
          let uu___1616_21999 = env  in
          {
            solver = (uu___1616_21999.solver);
            range = (uu___1616_21999.range);
            curmodule = (uu___1616_21999.curmodule);
            gamma = (uu___1616_21999.gamma);
            gamma_sig = (uu___1616_21999.gamma_sig);
            gamma_cache = (uu___1616_21999.gamma_cache);
            modules = (uu___1616_21999.modules);
            expected_typ = (uu___1616_21999.expected_typ);
            sigtab = (uu___1616_21999.sigtab);
            attrtab = (uu___1616_21999.attrtab);
            is_pattern = (uu___1616_21999.is_pattern);
            instantiate_imp = (uu___1616_21999.instantiate_imp);
            effects;
            generalize = (uu___1616_21999.generalize);
            letrecs = (uu___1616_21999.letrecs);
            top_level = (uu___1616_21999.top_level);
            check_uvars = (uu___1616_21999.check_uvars);
            use_eq = (uu___1616_21999.use_eq);
            is_iface = (uu___1616_21999.is_iface);
            admit = (uu___1616_21999.admit);
            lax = (uu___1616_21999.lax);
            lax_universes = (uu___1616_21999.lax_universes);
            phase1 = (uu___1616_21999.phase1);
            failhard = (uu___1616_21999.failhard);
            nosynth = (uu___1616_21999.nosynth);
            uvar_subtyping = (uu___1616_21999.uvar_subtyping);
            tc_term = (uu___1616_21999.tc_term);
            type_of = (uu___1616_21999.type_of);
            universe_of = (uu___1616_21999.universe_of);
            check_type_of = (uu___1616_21999.check_type_of);
            use_bv_sorts = (uu___1616_21999.use_bv_sorts);
            qtbl_name_and_index = (uu___1616_21999.qtbl_name_and_index);
            normalized_eff_names = (uu___1616_21999.normalized_eff_names);
            fv_delta_depths = (uu___1616_21999.fv_delta_depths);
            proof_ns = (uu___1616_21999.proof_ns);
            synth_hook = (uu___1616_21999.synth_hook);
            splice = (uu___1616_21999.splice);
            postprocess = (uu___1616_21999.postprocess);
            is_native_tactic = (uu___1616_21999.is_native_tactic);
            identifier_info = (uu___1616_21999.identifier_info);
            tc_hooks = (uu___1616_21999.tc_hooks);
            dsenv = (uu___1616_21999.dsenv);
            nbe = (uu___1616_21999.nbe);
            strict_args_tab = (uu___1616_21999.strict_args_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____22039 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____22039  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____22197 = (e1.mlift).mlift_wp u t wp  in
                            let uu____22198 = l1 u t wp e  in
                            l2 u t uu____22197 uu____22198))
            | uu____22199 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____22271 = inst_tscheme_with lift_t [u]  in
        match uu____22271 with
        | (uu____22278,lift_t1) ->
            let uu____22280 =
              let uu____22287 =
                let uu____22288 =
                  let uu____22305 =
                    let uu____22316 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22325 =
                      let uu____22336 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____22336]  in
                    uu____22316 :: uu____22325  in
                  (lift_t1, uu____22305)  in
                FStar_Syntax_Syntax.Tm_app uu____22288  in
              FStar_Syntax_Syntax.mk uu____22287  in
            uu____22280 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____22446 = inst_tscheme_with lift_t [u]  in
        match uu____22446 with
        | (uu____22453,lift_t1) ->
            let uu____22455 =
              let uu____22462 =
                let uu____22463 =
                  let uu____22480 =
                    let uu____22491 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22500 =
                      let uu____22511 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____22520 =
                        let uu____22531 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____22531]  in
                      uu____22511 :: uu____22520  in
                    uu____22491 :: uu____22500  in
                  (lift_t1, uu____22480)  in
                FStar_Syntax_Syntax.Tm_app uu____22463  in
              FStar_Syntax_Syntax.mk uu____22462  in
            uu____22455 FStar_Pervasives_Native.None
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
          let uu____22633 =
            let uu____22634 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____22634
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____22633  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____22643 =
          let uu____22645 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____22645  in
        let uu____22646 =
          let uu____22648 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____22676 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____22676)
             in
          FStar_Util.dflt "none" uu____22648  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22643 uu____22646
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____22705  ->
                match uu____22705 with
                | (e,uu____22713) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____22736 =
        match uu____22736 with
        | (i,j) ->
            let uu____22747 = FStar_Ident.lid_equals i j  in
            if uu____22747
            then
              FStar_All.pipe_right (id_edge i)
                (fun _22754  -> FStar_Pervasives_Native.Some _22754)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____22783 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____22793 = FStar_Ident.lid_equals i k  in
                    if uu____22793
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____22807 = FStar_Ident.lid_equals j k
                                 in
                              if uu____22807
                              then []
                              else
                                (let uu____22814 =
                                   let uu____22823 = find_edge order1 (i, k)
                                      in
                                   let uu____22826 = find_edge order1 (k, j)
                                      in
                                   (uu____22823, uu____22826)  in
                                 match uu____22814 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____22841 = compose_edges e1 e2
                                        in
                                     [uu____22841]
                                 | uu____22842 -> [])))))
             in
          FStar_List.append order1 uu____22783  in
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
              let uu____22872 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____22875 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____22875
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____22872
              then
                let uu____22882 =
                  let uu____22888 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____22888)
                   in
                let uu____22892 = get_range env  in
                FStar_Errors.raise_error uu____22882 uu____22892
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____22970 = FStar_Ident.lid_equals i j  in
                           if uu____22970
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____23022 =
                                         let uu____23031 =
                                           find_edge order2 (i, k)  in
                                         let uu____23034 =
                                           find_edge order2 (j, k)  in
                                         (uu____23031, uu____23034)  in
                                       match uu____23022 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____23076,uu____23077)
                                                ->
                                                let uu____23084 =
                                                  let uu____23091 =
                                                    let uu____23093 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23093
                                                     in
                                                  let uu____23096 =
                                                    let uu____23098 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23098
                                                     in
                                                  (uu____23091, uu____23096)
                                                   in
                                                (match uu____23084 with
                                                 | (true ,true ) ->
                                                     let uu____23115 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____23115
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
                                       | uu____23158 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1743_23231 = env.effects  in
         { decls = (uu___1743_23231.decls); order = order2; joins }  in
       let uu___1746_23232 = env  in
       {
         solver = (uu___1746_23232.solver);
         range = (uu___1746_23232.range);
         curmodule = (uu___1746_23232.curmodule);
         gamma = (uu___1746_23232.gamma);
         gamma_sig = (uu___1746_23232.gamma_sig);
         gamma_cache = (uu___1746_23232.gamma_cache);
         modules = (uu___1746_23232.modules);
         expected_typ = (uu___1746_23232.expected_typ);
         sigtab = (uu___1746_23232.sigtab);
         attrtab = (uu___1746_23232.attrtab);
         is_pattern = (uu___1746_23232.is_pattern);
         instantiate_imp = (uu___1746_23232.instantiate_imp);
         effects;
         generalize = (uu___1746_23232.generalize);
         letrecs = (uu___1746_23232.letrecs);
         top_level = (uu___1746_23232.top_level);
         check_uvars = (uu___1746_23232.check_uvars);
         use_eq = (uu___1746_23232.use_eq);
         is_iface = (uu___1746_23232.is_iface);
         admit = (uu___1746_23232.admit);
         lax = (uu___1746_23232.lax);
         lax_universes = (uu___1746_23232.lax_universes);
         phase1 = (uu___1746_23232.phase1);
         failhard = (uu___1746_23232.failhard);
         nosynth = (uu___1746_23232.nosynth);
         uvar_subtyping = (uu___1746_23232.uvar_subtyping);
         tc_term = (uu___1746_23232.tc_term);
         type_of = (uu___1746_23232.type_of);
         universe_of = (uu___1746_23232.universe_of);
         check_type_of = (uu___1746_23232.check_type_of);
         use_bv_sorts = (uu___1746_23232.use_bv_sorts);
         qtbl_name_and_index = (uu___1746_23232.qtbl_name_and_index);
         normalized_eff_names = (uu___1746_23232.normalized_eff_names);
         fv_delta_depths = (uu___1746_23232.fv_delta_depths);
         proof_ns = (uu___1746_23232.proof_ns);
         synth_hook = (uu___1746_23232.synth_hook);
         splice = (uu___1746_23232.splice);
         postprocess = (uu___1746_23232.postprocess);
         is_native_tactic = (uu___1746_23232.is_native_tactic);
         identifier_info = (uu___1746_23232.identifier_info);
         tc_hooks = (uu___1746_23232.tc_hooks);
         dsenv = (uu___1746_23232.dsenv);
         nbe = (uu___1746_23232.nbe);
         strict_args_tab = (uu___1746_23232.strict_args_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1750_23244 = env  in
      {
        solver = (uu___1750_23244.solver);
        range = (uu___1750_23244.range);
        curmodule = (uu___1750_23244.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1750_23244.gamma_sig);
        gamma_cache = (uu___1750_23244.gamma_cache);
        modules = (uu___1750_23244.modules);
        expected_typ = (uu___1750_23244.expected_typ);
        sigtab = (uu___1750_23244.sigtab);
        attrtab = (uu___1750_23244.attrtab);
        is_pattern = (uu___1750_23244.is_pattern);
        instantiate_imp = (uu___1750_23244.instantiate_imp);
        effects = (uu___1750_23244.effects);
        generalize = (uu___1750_23244.generalize);
        letrecs = (uu___1750_23244.letrecs);
        top_level = (uu___1750_23244.top_level);
        check_uvars = (uu___1750_23244.check_uvars);
        use_eq = (uu___1750_23244.use_eq);
        is_iface = (uu___1750_23244.is_iface);
        admit = (uu___1750_23244.admit);
        lax = (uu___1750_23244.lax);
        lax_universes = (uu___1750_23244.lax_universes);
        phase1 = (uu___1750_23244.phase1);
        failhard = (uu___1750_23244.failhard);
        nosynth = (uu___1750_23244.nosynth);
        uvar_subtyping = (uu___1750_23244.uvar_subtyping);
        tc_term = (uu___1750_23244.tc_term);
        type_of = (uu___1750_23244.type_of);
        universe_of = (uu___1750_23244.universe_of);
        check_type_of = (uu___1750_23244.check_type_of);
        use_bv_sorts = (uu___1750_23244.use_bv_sorts);
        qtbl_name_and_index = (uu___1750_23244.qtbl_name_and_index);
        normalized_eff_names = (uu___1750_23244.normalized_eff_names);
        fv_delta_depths = (uu___1750_23244.fv_delta_depths);
        proof_ns = (uu___1750_23244.proof_ns);
        synth_hook = (uu___1750_23244.synth_hook);
        splice = (uu___1750_23244.splice);
        postprocess = (uu___1750_23244.postprocess);
        is_native_tactic = (uu___1750_23244.is_native_tactic);
        identifier_info = (uu___1750_23244.identifier_info);
        tc_hooks = (uu___1750_23244.tc_hooks);
        dsenv = (uu___1750_23244.dsenv);
        nbe = (uu___1750_23244.nbe);
        strict_args_tab = (uu___1750_23244.strict_args_tab)
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
            (let uu___1763_23302 = env  in
             {
               solver = (uu___1763_23302.solver);
               range = (uu___1763_23302.range);
               curmodule = (uu___1763_23302.curmodule);
               gamma = rest;
               gamma_sig = (uu___1763_23302.gamma_sig);
               gamma_cache = (uu___1763_23302.gamma_cache);
               modules = (uu___1763_23302.modules);
               expected_typ = (uu___1763_23302.expected_typ);
               sigtab = (uu___1763_23302.sigtab);
               attrtab = (uu___1763_23302.attrtab);
               is_pattern = (uu___1763_23302.is_pattern);
               instantiate_imp = (uu___1763_23302.instantiate_imp);
               effects = (uu___1763_23302.effects);
               generalize = (uu___1763_23302.generalize);
               letrecs = (uu___1763_23302.letrecs);
               top_level = (uu___1763_23302.top_level);
               check_uvars = (uu___1763_23302.check_uvars);
               use_eq = (uu___1763_23302.use_eq);
               is_iface = (uu___1763_23302.is_iface);
               admit = (uu___1763_23302.admit);
               lax = (uu___1763_23302.lax);
               lax_universes = (uu___1763_23302.lax_universes);
               phase1 = (uu___1763_23302.phase1);
               failhard = (uu___1763_23302.failhard);
               nosynth = (uu___1763_23302.nosynth);
               uvar_subtyping = (uu___1763_23302.uvar_subtyping);
               tc_term = (uu___1763_23302.tc_term);
               type_of = (uu___1763_23302.type_of);
               universe_of = (uu___1763_23302.universe_of);
               check_type_of = (uu___1763_23302.check_type_of);
               use_bv_sorts = (uu___1763_23302.use_bv_sorts);
               qtbl_name_and_index = (uu___1763_23302.qtbl_name_and_index);
               normalized_eff_names = (uu___1763_23302.normalized_eff_names);
               fv_delta_depths = (uu___1763_23302.fv_delta_depths);
               proof_ns = (uu___1763_23302.proof_ns);
               synth_hook = (uu___1763_23302.synth_hook);
               splice = (uu___1763_23302.splice);
               postprocess = (uu___1763_23302.postprocess);
               is_native_tactic = (uu___1763_23302.is_native_tactic);
               identifier_info = (uu___1763_23302.identifier_info);
               tc_hooks = (uu___1763_23302.tc_hooks);
               dsenv = (uu___1763_23302.dsenv);
               nbe = (uu___1763_23302.nbe);
               strict_args_tab = (uu___1763_23302.strict_args_tab)
             }))
    | uu____23303 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23332  ->
             match uu____23332 with | (x,uu____23340) -> push_bv env1 x) env
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
            let uu___1777_23375 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1777_23375.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1777_23375.FStar_Syntax_Syntax.index);
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
        let uu____23448 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23448 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23476 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23476)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1798_23492 = env  in
      {
        solver = (uu___1798_23492.solver);
        range = (uu___1798_23492.range);
        curmodule = (uu___1798_23492.curmodule);
        gamma = (uu___1798_23492.gamma);
        gamma_sig = (uu___1798_23492.gamma_sig);
        gamma_cache = (uu___1798_23492.gamma_cache);
        modules = (uu___1798_23492.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1798_23492.sigtab);
        attrtab = (uu___1798_23492.attrtab);
        is_pattern = (uu___1798_23492.is_pattern);
        instantiate_imp = (uu___1798_23492.instantiate_imp);
        effects = (uu___1798_23492.effects);
        generalize = (uu___1798_23492.generalize);
        letrecs = (uu___1798_23492.letrecs);
        top_level = (uu___1798_23492.top_level);
        check_uvars = (uu___1798_23492.check_uvars);
        use_eq = false;
        is_iface = (uu___1798_23492.is_iface);
        admit = (uu___1798_23492.admit);
        lax = (uu___1798_23492.lax);
        lax_universes = (uu___1798_23492.lax_universes);
        phase1 = (uu___1798_23492.phase1);
        failhard = (uu___1798_23492.failhard);
        nosynth = (uu___1798_23492.nosynth);
        uvar_subtyping = (uu___1798_23492.uvar_subtyping);
        tc_term = (uu___1798_23492.tc_term);
        type_of = (uu___1798_23492.type_of);
        universe_of = (uu___1798_23492.universe_of);
        check_type_of = (uu___1798_23492.check_type_of);
        use_bv_sorts = (uu___1798_23492.use_bv_sorts);
        qtbl_name_and_index = (uu___1798_23492.qtbl_name_and_index);
        normalized_eff_names = (uu___1798_23492.normalized_eff_names);
        fv_delta_depths = (uu___1798_23492.fv_delta_depths);
        proof_ns = (uu___1798_23492.proof_ns);
        synth_hook = (uu___1798_23492.synth_hook);
        splice = (uu___1798_23492.splice);
        postprocess = (uu___1798_23492.postprocess);
        is_native_tactic = (uu___1798_23492.is_native_tactic);
        identifier_info = (uu___1798_23492.identifier_info);
        tc_hooks = (uu___1798_23492.tc_hooks);
        dsenv = (uu___1798_23492.dsenv);
        nbe = (uu___1798_23492.nbe);
        strict_args_tab = (uu___1798_23492.strict_args_tab)
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
    let uu____23523 = expected_typ env_  in
    ((let uu___1805_23529 = env_  in
      {
        solver = (uu___1805_23529.solver);
        range = (uu___1805_23529.range);
        curmodule = (uu___1805_23529.curmodule);
        gamma = (uu___1805_23529.gamma);
        gamma_sig = (uu___1805_23529.gamma_sig);
        gamma_cache = (uu___1805_23529.gamma_cache);
        modules = (uu___1805_23529.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1805_23529.sigtab);
        attrtab = (uu___1805_23529.attrtab);
        is_pattern = (uu___1805_23529.is_pattern);
        instantiate_imp = (uu___1805_23529.instantiate_imp);
        effects = (uu___1805_23529.effects);
        generalize = (uu___1805_23529.generalize);
        letrecs = (uu___1805_23529.letrecs);
        top_level = (uu___1805_23529.top_level);
        check_uvars = (uu___1805_23529.check_uvars);
        use_eq = false;
        is_iface = (uu___1805_23529.is_iface);
        admit = (uu___1805_23529.admit);
        lax = (uu___1805_23529.lax);
        lax_universes = (uu___1805_23529.lax_universes);
        phase1 = (uu___1805_23529.phase1);
        failhard = (uu___1805_23529.failhard);
        nosynth = (uu___1805_23529.nosynth);
        uvar_subtyping = (uu___1805_23529.uvar_subtyping);
        tc_term = (uu___1805_23529.tc_term);
        type_of = (uu___1805_23529.type_of);
        universe_of = (uu___1805_23529.universe_of);
        check_type_of = (uu___1805_23529.check_type_of);
        use_bv_sorts = (uu___1805_23529.use_bv_sorts);
        qtbl_name_and_index = (uu___1805_23529.qtbl_name_and_index);
        normalized_eff_names = (uu___1805_23529.normalized_eff_names);
        fv_delta_depths = (uu___1805_23529.fv_delta_depths);
        proof_ns = (uu___1805_23529.proof_ns);
        synth_hook = (uu___1805_23529.synth_hook);
        splice = (uu___1805_23529.splice);
        postprocess = (uu___1805_23529.postprocess);
        is_native_tactic = (uu___1805_23529.is_native_tactic);
        identifier_info = (uu___1805_23529.identifier_info);
        tc_hooks = (uu___1805_23529.tc_hooks);
        dsenv = (uu___1805_23529.dsenv);
        nbe = (uu___1805_23529.nbe);
        strict_args_tab = (uu___1805_23529.strict_args_tab)
      }), uu____23523)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23541 =
      let uu____23544 = FStar_Ident.id_of_text ""  in [uu____23544]  in
    FStar_Ident.lid_of_ids uu____23541  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23551 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23551
        then
          let uu____23556 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23556 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1813_23584 = env  in
       {
         solver = (uu___1813_23584.solver);
         range = (uu___1813_23584.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1813_23584.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1813_23584.expected_typ);
         sigtab = (uu___1813_23584.sigtab);
         attrtab = (uu___1813_23584.attrtab);
         is_pattern = (uu___1813_23584.is_pattern);
         instantiate_imp = (uu___1813_23584.instantiate_imp);
         effects = (uu___1813_23584.effects);
         generalize = (uu___1813_23584.generalize);
         letrecs = (uu___1813_23584.letrecs);
         top_level = (uu___1813_23584.top_level);
         check_uvars = (uu___1813_23584.check_uvars);
         use_eq = (uu___1813_23584.use_eq);
         is_iface = (uu___1813_23584.is_iface);
         admit = (uu___1813_23584.admit);
         lax = (uu___1813_23584.lax);
         lax_universes = (uu___1813_23584.lax_universes);
         phase1 = (uu___1813_23584.phase1);
         failhard = (uu___1813_23584.failhard);
         nosynth = (uu___1813_23584.nosynth);
         uvar_subtyping = (uu___1813_23584.uvar_subtyping);
         tc_term = (uu___1813_23584.tc_term);
         type_of = (uu___1813_23584.type_of);
         universe_of = (uu___1813_23584.universe_of);
         check_type_of = (uu___1813_23584.check_type_of);
         use_bv_sorts = (uu___1813_23584.use_bv_sorts);
         qtbl_name_and_index = (uu___1813_23584.qtbl_name_and_index);
         normalized_eff_names = (uu___1813_23584.normalized_eff_names);
         fv_delta_depths = (uu___1813_23584.fv_delta_depths);
         proof_ns = (uu___1813_23584.proof_ns);
         synth_hook = (uu___1813_23584.synth_hook);
         splice = (uu___1813_23584.splice);
         postprocess = (uu___1813_23584.postprocess);
         is_native_tactic = (uu___1813_23584.is_native_tactic);
         identifier_info = (uu___1813_23584.identifier_info);
         tc_hooks = (uu___1813_23584.tc_hooks);
         dsenv = (uu___1813_23584.dsenv);
         nbe = (uu___1813_23584.nbe);
         strict_args_tab = (uu___1813_23584.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23636)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23640,(uu____23641,t)))::tl1
          ->
          let uu____23662 =
            let uu____23665 = FStar_Syntax_Free.uvars t  in
            ext out uu____23665  in
          aux uu____23662 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23668;
            FStar_Syntax_Syntax.index = uu____23669;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23677 =
            let uu____23680 = FStar_Syntax_Free.uvars t  in
            ext out uu____23680  in
          aux uu____23677 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23738)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23742,(uu____23743,t)))::tl1
          ->
          let uu____23764 =
            let uu____23767 = FStar_Syntax_Free.univs t  in
            ext out uu____23767  in
          aux uu____23764 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23770;
            FStar_Syntax_Syntax.index = uu____23771;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23779 =
            let uu____23782 = FStar_Syntax_Free.univs t  in
            ext out uu____23782  in
          aux uu____23779 tl1
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
          let uu____23844 = FStar_Util.set_add uname out  in
          aux uu____23844 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23847,(uu____23848,t)))::tl1
          ->
          let uu____23869 =
            let uu____23872 = FStar_Syntax_Free.univnames t  in
            ext out uu____23872  in
          aux uu____23869 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23875;
            FStar_Syntax_Syntax.index = uu____23876;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23884 =
            let uu____23887 = FStar_Syntax_Free.univnames t  in
            ext out uu____23887  in
          aux uu____23884 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_23908  ->
            match uu___11_23908 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23912 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23925 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23936 =
      let uu____23945 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23945
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23936 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23993 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24006  ->
              match uu___12_24006 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24009 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24009
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24015) ->
                  let uu____24032 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24032))
       in
    FStar_All.pipe_right uu____23993 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24046  ->
    match uu___13_24046 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24052 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24052
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24075  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24130) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24163,uu____24164) -> false  in
      let uu____24178 =
        FStar_List.tryFind
          (fun uu____24200  ->
             match uu____24200 with | (p,uu____24211) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24178 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24230,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24260 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24260
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1956_24282 = e  in
        {
          solver = (uu___1956_24282.solver);
          range = (uu___1956_24282.range);
          curmodule = (uu___1956_24282.curmodule);
          gamma = (uu___1956_24282.gamma);
          gamma_sig = (uu___1956_24282.gamma_sig);
          gamma_cache = (uu___1956_24282.gamma_cache);
          modules = (uu___1956_24282.modules);
          expected_typ = (uu___1956_24282.expected_typ);
          sigtab = (uu___1956_24282.sigtab);
          attrtab = (uu___1956_24282.attrtab);
          is_pattern = (uu___1956_24282.is_pattern);
          instantiate_imp = (uu___1956_24282.instantiate_imp);
          effects = (uu___1956_24282.effects);
          generalize = (uu___1956_24282.generalize);
          letrecs = (uu___1956_24282.letrecs);
          top_level = (uu___1956_24282.top_level);
          check_uvars = (uu___1956_24282.check_uvars);
          use_eq = (uu___1956_24282.use_eq);
          is_iface = (uu___1956_24282.is_iface);
          admit = (uu___1956_24282.admit);
          lax = (uu___1956_24282.lax);
          lax_universes = (uu___1956_24282.lax_universes);
          phase1 = (uu___1956_24282.phase1);
          failhard = (uu___1956_24282.failhard);
          nosynth = (uu___1956_24282.nosynth);
          uvar_subtyping = (uu___1956_24282.uvar_subtyping);
          tc_term = (uu___1956_24282.tc_term);
          type_of = (uu___1956_24282.type_of);
          universe_of = (uu___1956_24282.universe_of);
          check_type_of = (uu___1956_24282.check_type_of);
          use_bv_sorts = (uu___1956_24282.use_bv_sorts);
          qtbl_name_and_index = (uu___1956_24282.qtbl_name_and_index);
          normalized_eff_names = (uu___1956_24282.normalized_eff_names);
          fv_delta_depths = (uu___1956_24282.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1956_24282.synth_hook);
          splice = (uu___1956_24282.splice);
          postprocess = (uu___1956_24282.postprocess);
          is_native_tactic = (uu___1956_24282.is_native_tactic);
          identifier_info = (uu___1956_24282.identifier_info);
          tc_hooks = (uu___1956_24282.tc_hooks);
          dsenv = (uu___1956_24282.dsenv);
          nbe = (uu___1956_24282.nbe);
          strict_args_tab = (uu___1956_24282.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1965_24330 = e  in
      {
        solver = (uu___1965_24330.solver);
        range = (uu___1965_24330.range);
        curmodule = (uu___1965_24330.curmodule);
        gamma = (uu___1965_24330.gamma);
        gamma_sig = (uu___1965_24330.gamma_sig);
        gamma_cache = (uu___1965_24330.gamma_cache);
        modules = (uu___1965_24330.modules);
        expected_typ = (uu___1965_24330.expected_typ);
        sigtab = (uu___1965_24330.sigtab);
        attrtab = (uu___1965_24330.attrtab);
        is_pattern = (uu___1965_24330.is_pattern);
        instantiate_imp = (uu___1965_24330.instantiate_imp);
        effects = (uu___1965_24330.effects);
        generalize = (uu___1965_24330.generalize);
        letrecs = (uu___1965_24330.letrecs);
        top_level = (uu___1965_24330.top_level);
        check_uvars = (uu___1965_24330.check_uvars);
        use_eq = (uu___1965_24330.use_eq);
        is_iface = (uu___1965_24330.is_iface);
        admit = (uu___1965_24330.admit);
        lax = (uu___1965_24330.lax);
        lax_universes = (uu___1965_24330.lax_universes);
        phase1 = (uu___1965_24330.phase1);
        failhard = (uu___1965_24330.failhard);
        nosynth = (uu___1965_24330.nosynth);
        uvar_subtyping = (uu___1965_24330.uvar_subtyping);
        tc_term = (uu___1965_24330.tc_term);
        type_of = (uu___1965_24330.type_of);
        universe_of = (uu___1965_24330.universe_of);
        check_type_of = (uu___1965_24330.check_type_of);
        use_bv_sorts = (uu___1965_24330.use_bv_sorts);
        qtbl_name_and_index = (uu___1965_24330.qtbl_name_and_index);
        normalized_eff_names = (uu___1965_24330.normalized_eff_names);
        fv_delta_depths = (uu___1965_24330.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1965_24330.synth_hook);
        splice = (uu___1965_24330.splice);
        postprocess = (uu___1965_24330.postprocess);
        is_native_tactic = (uu___1965_24330.is_native_tactic);
        identifier_info = (uu___1965_24330.identifier_info);
        tc_hooks = (uu___1965_24330.tc_hooks);
        dsenv = (uu___1965_24330.dsenv);
        nbe = (uu___1965_24330.nbe);
        strict_args_tab = (uu___1965_24330.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24346 = FStar_Syntax_Free.names t  in
      let uu____24349 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24346 uu____24349
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24372 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24372
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24382 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24382
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24403 =
      match uu____24403 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24423 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24423)
       in
    let uu____24431 =
      let uu____24435 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24435 FStar_List.rev  in
    FStar_All.pipe_right uu____24431 (FStar_String.concat " ")
  
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
                  (let uu____24505 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24505 with
                   | FStar_Pervasives_Native.Some uu____24509 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24512 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24522;
        univ_ineqs = uu____24523; implicits = uu____24524;_} -> true
    | uu____24536 -> false
  
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
          let uu___2009_24567 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2009_24567.deferred);
            univ_ineqs = (uu___2009_24567.univ_ineqs);
            implicits = (uu___2009_24567.implicits)
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
          let uu____24606 = FStar_Options.defensive ()  in
          if uu____24606
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24612 =
              let uu____24614 =
                let uu____24616 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24616  in
              Prims.op_Negation uu____24614  in
            (if uu____24612
             then
               let uu____24623 =
                 let uu____24629 =
                   let uu____24631 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24633 =
                     let uu____24635 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24635
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24631 uu____24633
                    in
                 (FStar_Errors.Warning_Defensive, uu____24629)  in
               FStar_Errors.log_issue rng uu____24623
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
          let uu____24675 =
            let uu____24677 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24677  in
          if uu____24675
          then ()
          else
            (let uu____24682 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24682 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24708 =
            let uu____24710 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24710  in
          if uu____24708
          then ()
          else
            (let uu____24715 = bound_vars e  in
             def_check_closed_in rng msg uu____24715 t)
  
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
          let uu___2046_24754 = g  in
          let uu____24755 =
            let uu____24756 =
              let uu____24757 =
                let uu____24764 =
                  let uu____24765 =
                    let uu____24782 =
                      let uu____24793 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24793]  in
                    (f, uu____24782)  in
                  FStar_Syntax_Syntax.Tm_app uu____24765  in
                FStar_Syntax_Syntax.mk uu____24764  in
              uu____24757 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24830  -> FStar_TypeChecker_Common.NonTrivial _24830)
              uu____24756
             in
          {
            guard_f = uu____24755;
            deferred = (uu___2046_24754.deferred);
            univ_ineqs = (uu___2046_24754.univ_ineqs);
            implicits = (uu___2046_24754.implicits)
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
          let uu___2053_24848 = g  in
          let uu____24849 =
            let uu____24850 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24850  in
          {
            guard_f = uu____24849;
            deferred = (uu___2053_24848.deferred);
            univ_ineqs = (uu___2053_24848.univ_ineqs);
            implicits = (uu___2053_24848.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2058_24867 = g  in
          let uu____24868 =
            let uu____24869 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24869  in
          {
            guard_f = uu____24868;
            deferred = (uu___2058_24867.deferred);
            univ_ineqs = (uu___2058_24867.univ_ineqs);
            implicits = (uu___2058_24867.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2062_24871 = g  in
          let uu____24872 =
            let uu____24873 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24873  in
          {
            guard_f = uu____24872;
            deferred = (uu___2062_24871.deferred);
            univ_ineqs = (uu___2062_24871.univ_ineqs);
            implicits = (uu___2062_24871.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24880 ->
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
          let uu____24897 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24897
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24904 =
      let uu____24905 = FStar_Syntax_Util.unmeta t  in
      uu____24905.FStar_Syntax_Syntax.n  in
    match uu____24904 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24909 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24952 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24952;
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
                       let uu____25047 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25047
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2117_25054 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2117_25054.deferred);
              univ_ineqs = (uu___2117_25054.univ_ineqs);
              implicits = (uu___2117_25054.implicits)
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
               let uu____25088 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25088
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
            let uu___2132_25115 = g  in
            let uu____25116 =
              let uu____25117 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25117  in
            {
              guard_f = uu____25116;
              deferred = (uu___2132_25115.deferred);
              univ_ineqs = (uu___2132_25115.univ_ineqs);
              implicits = (uu___2132_25115.implicits)
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
              let uu____25175 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25175 with
              | FStar_Pervasives_Native.Some
                  (uu____25200::(tm,uu____25202)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25266 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25284 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25284;
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
                      let uu___2154_25316 = trivial_guard  in
                      {
                        guard_f = (uu___2154_25316.guard_f);
                        deferred = (uu___2154_25316.deferred);
                        univ_ineqs = (uu___2154_25316.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25334  -> ());
    push = (fun uu____25336  -> ());
    pop = (fun uu____25339  -> ());
    snapshot =
      (fun uu____25342  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25361  -> fun uu____25362  -> ());
    encode_sig = (fun uu____25377  -> fun uu____25378  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25384 =
             let uu____25391 = FStar_Options.peek ()  in (e, g, uu____25391)
              in
           [uu____25384]);
    solve = (fun uu____25407  -> fun uu____25408  -> fun uu____25409  -> ());
    finish = (fun uu____25416  -> ());
    refresh = (fun uu____25418  -> ())
  } 