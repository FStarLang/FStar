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
      let inst_tscheme1 us_opt1 ts =
        match us_opt1 with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____16370 =
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
                  failwith
                    "effect_signature: insufficient number of universes"
                else
                  (let uu____16417 =
                     FStar_List.splitAt
                       (FStar_List.length ne.FStar_Syntax_Syntax.univs) us
                      in
                   match uu____16417 with
                   | (ne_us,sig_us) ->
                       ((FStar_Pervasives_Native.Some ne_us),
                         (FStar_Pervasives_Native.Some sig_us)))
             in
          (match uu____16370 with
           | (ne_us,sig_us) ->
               let uu____16468 =
                 inst_tscheme1 sig_us ne.FStar_Syntax_Syntax.signature  in
               (match uu____16468 with
                | (sig_us1,signature_t) ->
                    let uu____16485 =
                      let uu____16490 =
                        let uu____16491 =
                          let uu____16494 =
                            FStar_Syntax_Syntax.mk_Total signature_t  in
                          FStar_Syntax_Util.arrow
                            ne.FStar_Syntax_Syntax.binders uu____16494
                           in
                        ((ne.FStar_Syntax_Syntax.univs), uu____16491)  in
                      inst_tscheme1 ne_us uu____16490  in
                    (match uu____16485 with
                     | (ne_us1,signature_t1) ->
                         FStar_Pervasives_Native.Some
                           (((FStar_List.append ne_us1 sig_us1),
                              signature_t1), (se.FStar_Syntax_Syntax.sigrng)))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16528,uu____16529) ->
          let uu____16534 =
            let uu____16543 =
              let uu____16548 =
                let uu____16549 =
                  let uu____16552 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16552  in
                (us, uu____16549)  in
              inst_tscheme1 us_opt uu____16548  in
            (uu____16543, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16534
      | uu____16571 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16660 =
          match uu____16660 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16756,uvs,t,uu____16759,uu____16760,uu____16761);
                      FStar_Syntax_Syntax.sigrng = uu____16762;
                      FStar_Syntax_Syntax.sigquals = uu____16763;
                      FStar_Syntax_Syntax.sigmeta = uu____16764;
                      FStar_Syntax_Syntax.sigattrs = uu____16765;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16788 =
                     let uu____16797 = inst_tscheme1 (uvs, t)  in
                     (uu____16797, rng)  in
                   FStar_Pervasives_Native.Some uu____16788
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16821;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16823;
                      FStar_Syntax_Syntax.sigattrs = uu____16824;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16841 =
                     let uu____16843 = in_cur_mod env l  in uu____16843 = Yes
                      in
                   if uu____16841
                   then
                     let uu____16855 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16855
                      then
                        let uu____16871 =
                          let uu____16880 = inst_tscheme1 (uvs, t)  in
                          (uu____16880, rng)  in
                        FStar_Pervasives_Native.Some uu____16871
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16913 =
                        let uu____16922 = inst_tscheme1 (uvs, t)  in
                        (uu____16922, rng)  in
                      FStar_Pervasives_Native.Some uu____16913)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16947,uu____16948);
                      FStar_Syntax_Syntax.sigrng = uu____16949;
                      FStar_Syntax_Syntax.sigquals = uu____16950;
                      FStar_Syntax_Syntax.sigmeta = uu____16951;
                      FStar_Syntax_Syntax.sigattrs = uu____16952;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16993 =
                          let uu____17002 = inst_tscheme1 (uvs, k)  in
                          (uu____17002, rng)  in
                        FStar_Pervasives_Native.Some uu____16993
                    | uu____17023 ->
                        let uu____17024 =
                          let uu____17033 =
                            let uu____17038 =
                              let uu____17039 =
                                let uu____17042 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17042
                                 in
                              (uvs, uu____17039)  in
                            inst_tscheme1 uu____17038  in
                          (uu____17033, rng)  in
                        FStar_Pervasives_Native.Some uu____17024)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17065,uu____17066);
                      FStar_Syntax_Syntax.sigrng = uu____17067;
                      FStar_Syntax_Syntax.sigquals = uu____17068;
                      FStar_Syntax_Syntax.sigmeta = uu____17069;
                      FStar_Syntax_Syntax.sigattrs = uu____17070;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17112 =
                          let uu____17121 = inst_tscheme_with (uvs, k) us  in
                          (uu____17121, rng)  in
                        FStar_Pervasives_Native.Some uu____17112
                    | uu____17142 ->
                        let uu____17143 =
                          let uu____17152 =
                            let uu____17157 =
                              let uu____17158 =
                                let uu____17161 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17161
                                 in
                              (uvs, uu____17158)  in
                            inst_tscheme_with uu____17157 us  in
                          (uu____17152, rng)  in
                        FStar_Pervasives_Native.Some uu____17143)
               | FStar_Util.Inr se ->
                   let uu____17197 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17218;
                          FStar_Syntax_Syntax.sigrng = uu____17219;
                          FStar_Syntax_Syntax.sigquals = uu____17220;
                          FStar_Syntax_Syntax.sigmeta = uu____17221;
                          FStar_Syntax_Syntax.sigattrs = uu____17222;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17237 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____17197
                     (FStar_Util.map_option
                        (fun uu____17285  ->
                           match uu____17285 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17316 =
          let uu____17327 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17327 mapper  in
        match uu____17316 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17401 =
              let uu____17412 =
                let uu____17419 =
                  let uu___864_17422 = t  in
                  let uu____17423 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___864_17422.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17423;
                    FStar_Syntax_Syntax.vars =
                      (uu___864_17422.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17419)  in
              (uu____17412, r)  in
            FStar_Pervasives_Native.Some uu____17401
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17472 = lookup_qname env l  in
      match uu____17472 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17493 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17547 = try_lookup_bv env bv  in
      match uu____17547 with
      | FStar_Pervasives_Native.None  ->
          let uu____17562 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17562 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17578 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17579 =
            let uu____17580 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17580  in
          (uu____17578, uu____17579)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17602 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17602 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17668 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17668  in
          let uu____17669 =
            let uu____17678 =
              let uu____17683 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17683)  in
            (uu____17678, r1)  in
          FStar_Pervasives_Native.Some uu____17669
  
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
        let uu____17718 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17718 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17751,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17776 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17776  in
            let uu____17777 =
              let uu____17782 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17782, r1)  in
            FStar_Pervasives_Native.Some uu____17777
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17806 = try_lookup_lid env l  in
      match uu____17806 with
      | FStar_Pervasives_Native.None  ->
          let uu____17833 = name_not_found l  in
          let uu____17839 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17833 uu____17839
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17882  ->
              match uu___5_17882 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17886 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17907 = lookup_qname env lid  in
      match uu____17907 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17916,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17919;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17921;
              FStar_Syntax_Syntax.sigattrs = uu____17922;_},FStar_Pervasives_Native.None
            ),uu____17923)
          ->
          let uu____17972 =
            let uu____17979 =
              let uu____17980 =
                let uu____17983 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17983 t  in
              (uvs, uu____17980)  in
            (uu____17979, q)  in
          FStar_Pervasives_Native.Some uu____17972
      | uu____17996 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18018 = lookup_qname env lid  in
      match uu____18018 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18023,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18026;
              FStar_Syntax_Syntax.sigquals = uu____18027;
              FStar_Syntax_Syntax.sigmeta = uu____18028;
              FStar_Syntax_Syntax.sigattrs = uu____18029;_},FStar_Pervasives_Native.None
            ),uu____18030)
          ->
          let uu____18079 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18079 (uvs, t)
      | uu____18084 ->
          let uu____18085 = name_not_found lid  in
          let uu____18091 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18085 uu____18091
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18111 = lookup_qname env lid  in
      match uu____18111 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18116,uvs,t,uu____18119,uu____18120,uu____18121);
              FStar_Syntax_Syntax.sigrng = uu____18122;
              FStar_Syntax_Syntax.sigquals = uu____18123;
              FStar_Syntax_Syntax.sigmeta = uu____18124;
              FStar_Syntax_Syntax.sigattrs = uu____18125;_},FStar_Pervasives_Native.None
            ),uu____18126)
          ->
          let uu____18181 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18181 (uvs, t)
      | uu____18186 ->
          let uu____18187 = name_not_found lid  in
          let uu____18193 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18187 uu____18193
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18216 = lookup_qname env lid  in
      match uu____18216 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18224,uu____18225,uu____18226,uu____18227,uu____18228,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18230;
              FStar_Syntax_Syntax.sigquals = uu____18231;
              FStar_Syntax_Syntax.sigmeta = uu____18232;
              FStar_Syntax_Syntax.sigattrs = uu____18233;_},uu____18234),uu____18235)
          -> (true, dcs)
      | uu____18298 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18314 = lookup_qname env lid  in
      match uu____18314 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18315,uu____18316,uu____18317,l,uu____18319,uu____18320);
              FStar_Syntax_Syntax.sigrng = uu____18321;
              FStar_Syntax_Syntax.sigquals = uu____18322;
              FStar_Syntax_Syntax.sigmeta = uu____18323;
              FStar_Syntax_Syntax.sigattrs = uu____18324;_},uu____18325),uu____18326)
          -> l
      | uu____18383 ->
          let uu____18384 =
            let uu____18386 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18386  in
          failwith uu____18384
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18456)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18513) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18537 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18537
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18572 -> FStar_Pervasives_Native.None)
          | uu____18581 -> FStar_Pervasives_Native.None
  
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
        let uu____18643 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18643
  
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
        let uu____18676 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18676
  
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
             (FStar_Util.Inl uu____18728,uu____18729) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18778),uu____18779) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18828 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18846 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18856 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18873 ->
                  let uu____18880 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18880
              | FStar_Syntax_Syntax.Sig_let ((uu____18881,lbs),uu____18883)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18899 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18899
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18906 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18914 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18915 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18922 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18923 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18924 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18925 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18938 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18956 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18956
           (fun d_opt  ->
              let uu____18969 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18969
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18979 =
                   let uu____18982 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18982  in
                 match uu____18979 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18983 =
                       let uu____18985 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18985
                        in
                     failwith uu____18983
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18990 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18990
                       then
                         let uu____18993 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18995 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18997 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18993 uu____18995 uu____18997
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
        (FStar_Util.Inr (se,uu____19022),uu____19023) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19072 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19094),uu____19095) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19144 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19166 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19166
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19189 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19189 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19213 =
                      let uu____19214 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19214.FStar_Syntax_Syntax.n  in
                    match uu____19213 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19219 -> false))
  
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
        let uu____19256 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19256.FStar_Ident.str  in
      let uu____19257 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19257 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19285 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19285  in
          let res =
            match attrs with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some attrs1 ->
                FStar_Util.find_map attrs1
                  (fun x  ->
                     let uu____19313 =
                       FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                         FStar_Parser_Const.strict_on_arguments_attr
                        in
                     FStar_Pervasives_Native.fst uu____19313)
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
      let uu____19363 = lookup_qname env ftv  in
      match uu____19363 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19367) ->
          let uu____19412 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____19412 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19433,t),r) ->
               let uu____19448 =
                 let uu____19449 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19449 t  in
               FStar_Pervasives_Native.Some uu____19448)
      | uu____19450 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19462 = try_lookup_effect_lid env ftv  in
      match uu____19462 with
      | FStar_Pervasives_Native.None  ->
          let uu____19465 = name_not_found ftv  in
          let uu____19471 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19465 uu____19471
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
        let uu____19495 = lookup_qname env lid0  in
        match uu____19495 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19506);
                FStar_Syntax_Syntax.sigrng = uu____19507;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19509;
                FStar_Syntax_Syntax.sigattrs = uu____19510;_},FStar_Pervasives_Native.None
              ),uu____19511)
            ->
            let lid1 =
              let uu____19565 =
                let uu____19566 = FStar_Ident.range_of_lid lid  in
                let uu____19567 =
                  let uu____19568 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19568  in
                FStar_Range.set_use_range uu____19566 uu____19567  in
              FStar_Ident.set_lid_range lid uu____19565  in
            let uu____19569 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19575  ->
                      match uu___6_19575 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19578 -> false))
               in
            if uu____19569
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19597 =
                      let uu____19599 =
                        let uu____19601 = get_range env  in
                        FStar_Range.string_of_range uu____19601  in
                      let uu____19602 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19604 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19599 uu____19602 uu____19604
                       in
                    failwith uu____19597)
                  in
               match (binders, univs1) with
               | ([],uu____19625) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19651,uu____19652::uu____19653::uu____19654) ->
                   let uu____19675 =
                     let uu____19677 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19679 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19677 uu____19679
                      in
                   failwith uu____19675
               | uu____19690 ->
                   let uu____19705 =
                     let uu____19710 =
                       let uu____19711 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19711)  in
                     inst_tscheme_with uu____19710 insts  in
                   (match uu____19705 with
                    | (uu____19724,t) ->
                        let t1 =
                          let uu____19727 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19727 t  in
                        let uu____19728 =
                          let uu____19729 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19729.FStar_Syntax_Syntax.n  in
                        (match uu____19728 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19764 -> failwith "Impossible")))
        | uu____19772 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19796 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19796 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19809,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19816 = find1 l2  in
            (match uu____19816 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19823 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19823 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19827 = find1 l  in
            (match uu____19827 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19832 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19832
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19847 = lookup_qname env l1  in
      match uu____19847 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19850;
              FStar_Syntax_Syntax.sigrng = uu____19851;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19853;
              FStar_Syntax_Syntax.sigattrs = uu____19854;_},uu____19855),uu____19856)
          -> q
      | uu____19907 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19931 =
          let uu____19932 =
            let uu____19934 = FStar_Util.string_of_int i  in
            let uu____19936 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19934 uu____19936
             in
          failwith uu____19932  in
        let uu____19939 = lookup_datacon env lid  in
        match uu____19939 with
        | (uu____19944,t) ->
            let uu____19946 =
              let uu____19947 = FStar_Syntax_Subst.compress t  in
              uu____19947.FStar_Syntax_Syntax.n  in
            (match uu____19946 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19951) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19995 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19995
                      FStar_Pervasives_Native.fst)
             | uu____20006 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20020 = lookup_qname env l  in
      match uu____20020 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20022,uu____20023,uu____20024);
              FStar_Syntax_Syntax.sigrng = uu____20025;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20027;
              FStar_Syntax_Syntax.sigattrs = uu____20028;_},uu____20029),uu____20030)
          ->
          FStar_Util.for_some
            (fun uu___7_20083  ->
               match uu___7_20083 with
               | FStar_Syntax_Syntax.Projector uu____20085 -> true
               | uu____20091 -> false) quals
      | uu____20093 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20107 = lookup_qname env lid  in
      match uu____20107 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20109,uu____20110,uu____20111,uu____20112,uu____20113,uu____20114);
              FStar_Syntax_Syntax.sigrng = uu____20115;
              FStar_Syntax_Syntax.sigquals = uu____20116;
              FStar_Syntax_Syntax.sigmeta = uu____20117;
              FStar_Syntax_Syntax.sigattrs = uu____20118;_},uu____20119),uu____20120)
          -> true
      | uu____20178 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20192 = lookup_qname env lid  in
      match uu____20192 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20194,uu____20195,uu____20196,uu____20197,uu____20198,uu____20199);
              FStar_Syntax_Syntax.sigrng = uu____20200;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20202;
              FStar_Syntax_Syntax.sigattrs = uu____20203;_},uu____20204),uu____20205)
          ->
          FStar_Util.for_some
            (fun uu___8_20266  ->
               match uu___8_20266 with
               | FStar_Syntax_Syntax.RecordType uu____20268 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20278 -> true
               | uu____20288 -> false) quals
      | uu____20290 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20300,uu____20301);
            FStar_Syntax_Syntax.sigrng = uu____20302;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20304;
            FStar_Syntax_Syntax.sigattrs = uu____20305;_},uu____20306),uu____20307)
        ->
        FStar_Util.for_some
          (fun uu___9_20364  ->
             match uu___9_20364 with
             | FStar_Syntax_Syntax.Action uu____20366 -> true
             | uu____20368 -> false) quals
    | uu____20370 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20384 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20384
  
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
      let uu____20401 =
        let uu____20402 = FStar_Syntax_Util.un_uinst head1  in
        uu____20402.FStar_Syntax_Syntax.n  in
      match uu____20401 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20408 ->
               true
           | uu____20411 -> false)
      | uu____20413 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20427 = lookup_qname env l  in
      match uu____20427 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20430),uu____20431) ->
          FStar_Util.for_some
            (fun uu___10_20479  ->
               match uu___10_20479 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20482 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20484 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20560 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20578) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20596 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20604 ->
                 FStar_Pervasives_Native.Some true
             | uu____20623 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20626 =
        let uu____20630 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20630 mapper  in
      match uu____20626 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20690 = lookup_qname env lid  in
      match uu____20690 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20694,uu____20695,tps,uu____20697,uu____20698,uu____20699);
              FStar_Syntax_Syntax.sigrng = uu____20700;
              FStar_Syntax_Syntax.sigquals = uu____20701;
              FStar_Syntax_Syntax.sigmeta = uu____20702;
              FStar_Syntax_Syntax.sigattrs = uu____20703;_},uu____20704),uu____20705)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20771 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20817  ->
              match uu____20817 with
              | (d,uu____20826) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20842 = effect_decl_opt env l  in
      match uu____20842 with
      | FStar_Pervasives_Native.None  ->
          let uu____20857 = name_not_found l  in
          let uu____20863 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20857 uu____20863
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20886  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20905  ->
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
        let uu____20937 = FStar_Ident.lid_equals l1 l2  in
        if uu____20937
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20948 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20948
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20959 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21012  ->
                        match uu____21012 with
                        | (m1,m2,uu____21026,uu____21027,uu____21028) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20959 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21045 =
                    let uu____21051 =
                      let uu____21053 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21055 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21053
                        uu____21055
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21051)
                     in
                  FStar_Errors.raise_error uu____21045 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21065,uu____21066,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21100 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21100
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
  'Auu____21120 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21120) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21149 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21175  ->
                match uu____21175 with
                | (d,uu____21182) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21149 with
      | FStar_Pervasives_Native.None  ->
          let uu____21193 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21193
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21208 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21208 with
           | (uu____21219,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21237)::(wp,uu____21239)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21295 -> failwith "Impossible"))
  
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
            let uu___1521_21345 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1521_21345.order);
              joins = (uu___1521_21345.joins)
            }  in
          let uu___1524_21354 = env  in
          {
            solver = (uu___1524_21354.solver);
            range = (uu___1524_21354.range);
            curmodule = (uu___1524_21354.curmodule);
            gamma = (uu___1524_21354.gamma);
            gamma_sig = (uu___1524_21354.gamma_sig);
            gamma_cache = (uu___1524_21354.gamma_cache);
            modules = (uu___1524_21354.modules);
            expected_typ = (uu___1524_21354.expected_typ);
            sigtab = (uu___1524_21354.sigtab);
            attrtab = (uu___1524_21354.attrtab);
            is_pattern = (uu___1524_21354.is_pattern);
            instantiate_imp = (uu___1524_21354.instantiate_imp);
            effects;
            generalize = (uu___1524_21354.generalize);
            letrecs = (uu___1524_21354.letrecs);
            top_level = (uu___1524_21354.top_level);
            check_uvars = (uu___1524_21354.check_uvars);
            use_eq = (uu___1524_21354.use_eq);
            is_iface = (uu___1524_21354.is_iface);
            admit = (uu___1524_21354.admit);
            lax = (uu___1524_21354.lax);
            lax_universes = (uu___1524_21354.lax_universes);
            phase1 = (uu___1524_21354.phase1);
            failhard = (uu___1524_21354.failhard);
            nosynth = (uu___1524_21354.nosynth);
            uvar_subtyping = (uu___1524_21354.uvar_subtyping);
            tc_term = (uu___1524_21354.tc_term);
            type_of = (uu___1524_21354.type_of);
            universe_of = (uu___1524_21354.universe_of);
            check_type_of = (uu___1524_21354.check_type_of);
            use_bv_sorts = (uu___1524_21354.use_bv_sorts);
            qtbl_name_and_index = (uu___1524_21354.qtbl_name_and_index);
            normalized_eff_names = (uu___1524_21354.normalized_eff_names);
            fv_delta_depths = (uu___1524_21354.fv_delta_depths);
            proof_ns = (uu___1524_21354.proof_ns);
            synth_hook = (uu___1524_21354.synth_hook);
            splice = (uu___1524_21354.splice);
            postprocess = (uu___1524_21354.postprocess);
            is_native_tactic = (uu___1524_21354.is_native_tactic);
            identifier_info = (uu___1524_21354.identifier_info);
            tc_hooks = (uu___1524_21354.tc_hooks);
            dsenv = (uu___1524_21354.dsenv);
            nbe = (uu___1524_21354.nbe);
            strict_args_tab = (uu___1524_21354.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____21384 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____21384  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____21542 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____21543 = l1 u t wp e  in
                                l2 u t uu____21542 uu____21543))
                | uu____21544 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21616 = inst_tscheme_with lift_t [u]  in
            match uu____21616 with
            | (uu____21623,lift_t1) ->
                let uu____21625 =
                  let uu____21632 =
                    let uu____21633 =
                      let uu____21650 =
                        let uu____21661 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21670 =
                          let uu____21681 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21681]  in
                        uu____21661 :: uu____21670  in
                      (lift_t1, uu____21650)  in
                    FStar_Syntax_Syntax.Tm_app uu____21633  in
                  FStar_Syntax_Syntax.mk uu____21632  in
                uu____21625 FStar_Pervasives_Native.None
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
            let uu____21791 = inst_tscheme_with lift_t [u]  in
            match uu____21791 with
            | (uu____21798,lift_t1) ->
                let uu____21800 =
                  let uu____21807 =
                    let uu____21808 =
                      let uu____21825 =
                        let uu____21836 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21845 =
                          let uu____21856 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21865 =
                            let uu____21876 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21876]  in
                          uu____21856 :: uu____21865  in
                        uu____21836 :: uu____21845  in
                      (lift_t1, uu____21825)  in
                    FStar_Syntax_Syntax.Tm_app uu____21808  in
                  FStar_Syntax_Syntax.mk uu____21807  in
                uu____21800 FStar_Pervasives_Native.None
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
              let uu____21978 =
                let uu____21979 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21979
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21978  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21988 =
              let uu____21990 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21990  in
            let uu____21991 =
              let uu____21993 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____22021 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____22021)
                 in
              FStar_Util.dflt "none" uu____21993  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21988
              uu____21991
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____22050  ->
                    match uu____22050 with
                    | (e,uu____22058) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____22081 =
            match uu____22081 with
            | (i,j) ->
                let uu____22092 = FStar_Ident.lid_equals i j  in
                if uu____22092
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _22099  -> FStar_Pervasives_Native.Some _22099)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____22128 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____22138 = FStar_Ident.lid_equals i k  in
                        if uu____22138
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____22152 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____22152
                                  then []
                                  else
                                    (let uu____22159 =
                                       let uu____22168 =
                                         find_edge order1 (i, k)  in
                                       let uu____22171 =
                                         find_edge order1 (k, j)  in
                                       (uu____22168, uu____22171)  in
                                     match uu____22159 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____22186 =
                                           compose_edges e1 e2  in
                                         [uu____22186]
                                     | uu____22187 -> [])))))
                 in
              FStar_List.append order1 uu____22128  in
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
                   let uu____22217 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____22220 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____22220
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____22217
                   then
                     let uu____22227 =
                       let uu____22233 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____22233)
                        in
                     let uu____22237 = get_range env  in
                     FStar_Errors.raise_error uu____22227 uu____22237
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____22315 = FStar_Ident.lid_equals i j
                                   in
                                if uu____22315
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____22367 =
                                              let uu____22376 =
                                                find_edge order2 (i, k)  in
                                              let uu____22379 =
                                                find_edge order2 (j, k)  in
                                              (uu____22376, uu____22379)  in
                                            match uu____22367 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____22421,uu____22422)
                                                     ->
                                                     let uu____22429 =
                                                       let uu____22436 =
                                                         let uu____22438 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22438
                                                          in
                                                       let uu____22441 =
                                                         let uu____22443 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22443
                                                          in
                                                       (uu____22436,
                                                         uu____22441)
                                                        in
                                                     (match uu____22429 with
                                                      | (true ,true ) ->
                                                          let uu____22460 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____22460
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
                                            | uu____22503 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1651_22576 = env.effects  in
              { decls = (uu___1651_22576.decls); order = order2; joins }  in
            let uu___1654_22577 = env  in
            {
              solver = (uu___1654_22577.solver);
              range = (uu___1654_22577.range);
              curmodule = (uu___1654_22577.curmodule);
              gamma = (uu___1654_22577.gamma);
              gamma_sig = (uu___1654_22577.gamma_sig);
              gamma_cache = (uu___1654_22577.gamma_cache);
              modules = (uu___1654_22577.modules);
              expected_typ = (uu___1654_22577.expected_typ);
              sigtab = (uu___1654_22577.sigtab);
              attrtab = (uu___1654_22577.attrtab);
              is_pattern = (uu___1654_22577.is_pattern);
              instantiate_imp = (uu___1654_22577.instantiate_imp);
              effects;
              generalize = (uu___1654_22577.generalize);
              letrecs = (uu___1654_22577.letrecs);
              top_level = (uu___1654_22577.top_level);
              check_uvars = (uu___1654_22577.check_uvars);
              use_eq = (uu___1654_22577.use_eq);
              is_iface = (uu___1654_22577.is_iface);
              admit = (uu___1654_22577.admit);
              lax = (uu___1654_22577.lax);
              lax_universes = (uu___1654_22577.lax_universes);
              phase1 = (uu___1654_22577.phase1);
              failhard = (uu___1654_22577.failhard);
              nosynth = (uu___1654_22577.nosynth);
              uvar_subtyping = (uu___1654_22577.uvar_subtyping);
              tc_term = (uu___1654_22577.tc_term);
              type_of = (uu___1654_22577.type_of);
              universe_of = (uu___1654_22577.universe_of);
              check_type_of = (uu___1654_22577.check_type_of);
              use_bv_sorts = (uu___1654_22577.use_bv_sorts);
              qtbl_name_and_index = (uu___1654_22577.qtbl_name_and_index);
              normalized_eff_names = (uu___1654_22577.normalized_eff_names);
              fv_delta_depths = (uu___1654_22577.fv_delta_depths);
              proof_ns = (uu___1654_22577.proof_ns);
              synth_hook = (uu___1654_22577.synth_hook);
              splice = (uu___1654_22577.splice);
              postprocess = (uu___1654_22577.postprocess);
              is_native_tactic = (uu___1654_22577.is_native_tactic);
              identifier_info = (uu___1654_22577.identifier_info);
              tc_hooks = (uu___1654_22577.tc_hooks);
              dsenv = (uu___1654_22577.dsenv);
              nbe = (uu___1654_22577.nbe);
              strict_args_tab = (uu___1654_22577.strict_args_tab)
            }))
      | uu____22578 -> env
  
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
        | uu____22607 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22620 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22620 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22637 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22637 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22662 =
                     let uu____22668 =
                       let uu____22670 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22678 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22689 =
                         let uu____22691 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22691  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22670 uu____22678 uu____22689
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22668)
                      in
                   FStar_Errors.raise_error uu____22662
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22699 =
                     let uu____22710 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22710 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22747  ->
                        fun uu____22748  ->
                          match (uu____22747, uu____22748) with
                          | ((x,uu____22778),(t,uu____22780)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22699
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22811 =
                     let uu___1692_22812 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1692_22812.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1692_22812.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1692_22812.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1692_22812.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22811
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22824 .
    'Auu____22824 ->
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
          let uu____22854 = effect_decl_opt env effect_name  in
          match uu____22854 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22897 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22920 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22959 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22959
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22964 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22964
                      in
                   let repr =
                     let uu____22975 =
                       let uu____22976 =
                         FStar_All.pipe_right ed.FStar_Syntax_Syntax.repr
                           FStar_Pervasives_Native.snd
                          in
                       ([], uu____22976)  in
                     inst_effect_fun_with [u_c] env ed uu____22975  in
                   let uu____22997 =
                     let uu____23000 = get_range env  in
                     let uu____23001 =
                       let uu____23008 =
                         let uu____23009 =
                           let uu____23026 =
                             let uu____23037 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23037; wp]  in
                           (repr, uu____23026)  in
                         FStar_Syntax_Syntax.Tm_app uu____23009  in
                       FStar_Syntax_Syntax.mk uu____23008  in
                     uu____23001 FStar_Pervasives_Native.None uu____23000  in
                   FStar_Pervasives_Native.Some uu____22997)
  
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
      | uu____23181 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23196 =
        let uu____23197 = FStar_Syntax_Subst.compress t  in
        uu____23197.FStar_Syntax_Syntax.n  in
      match uu____23196 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23201,c) ->
          is_reifiable_comp env c
      | uu____23223 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23243 =
           let uu____23245 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23245  in
         if uu____23243
         then
           let uu____23248 =
             let uu____23254 =
               let uu____23256 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23256
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23254)  in
           let uu____23260 = get_range env  in
           FStar_Errors.raise_error uu____23248 uu____23260
         else ());
        (let uu____23263 = effect_repr_aux true env c u_c  in
         match uu____23263 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1757_23299 = env  in
        {
          solver = (uu___1757_23299.solver);
          range = (uu___1757_23299.range);
          curmodule = (uu___1757_23299.curmodule);
          gamma = (uu___1757_23299.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1757_23299.gamma_cache);
          modules = (uu___1757_23299.modules);
          expected_typ = (uu___1757_23299.expected_typ);
          sigtab = (uu___1757_23299.sigtab);
          attrtab = (uu___1757_23299.attrtab);
          is_pattern = (uu___1757_23299.is_pattern);
          instantiate_imp = (uu___1757_23299.instantiate_imp);
          effects = (uu___1757_23299.effects);
          generalize = (uu___1757_23299.generalize);
          letrecs = (uu___1757_23299.letrecs);
          top_level = (uu___1757_23299.top_level);
          check_uvars = (uu___1757_23299.check_uvars);
          use_eq = (uu___1757_23299.use_eq);
          is_iface = (uu___1757_23299.is_iface);
          admit = (uu___1757_23299.admit);
          lax = (uu___1757_23299.lax);
          lax_universes = (uu___1757_23299.lax_universes);
          phase1 = (uu___1757_23299.phase1);
          failhard = (uu___1757_23299.failhard);
          nosynth = (uu___1757_23299.nosynth);
          uvar_subtyping = (uu___1757_23299.uvar_subtyping);
          tc_term = (uu___1757_23299.tc_term);
          type_of = (uu___1757_23299.type_of);
          universe_of = (uu___1757_23299.universe_of);
          check_type_of = (uu___1757_23299.check_type_of);
          use_bv_sorts = (uu___1757_23299.use_bv_sorts);
          qtbl_name_and_index = (uu___1757_23299.qtbl_name_and_index);
          normalized_eff_names = (uu___1757_23299.normalized_eff_names);
          fv_delta_depths = (uu___1757_23299.fv_delta_depths);
          proof_ns = (uu___1757_23299.proof_ns);
          synth_hook = (uu___1757_23299.synth_hook);
          splice = (uu___1757_23299.splice);
          postprocess = (uu___1757_23299.postprocess);
          is_native_tactic = (uu___1757_23299.is_native_tactic);
          identifier_info = (uu___1757_23299.identifier_info);
          tc_hooks = (uu___1757_23299.tc_hooks);
          dsenv = (uu___1757_23299.dsenv);
          nbe = (uu___1757_23299.nbe);
          strict_args_tab = (uu___1757_23299.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1764_23313 = env  in
      {
        solver = (uu___1764_23313.solver);
        range = (uu___1764_23313.range);
        curmodule = (uu___1764_23313.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1764_23313.gamma_sig);
        gamma_cache = (uu___1764_23313.gamma_cache);
        modules = (uu___1764_23313.modules);
        expected_typ = (uu___1764_23313.expected_typ);
        sigtab = (uu___1764_23313.sigtab);
        attrtab = (uu___1764_23313.attrtab);
        is_pattern = (uu___1764_23313.is_pattern);
        instantiate_imp = (uu___1764_23313.instantiate_imp);
        effects = (uu___1764_23313.effects);
        generalize = (uu___1764_23313.generalize);
        letrecs = (uu___1764_23313.letrecs);
        top_level = (uu___1764_23313.top_level);
        check_uvars = (uu___1764_23313.check_uvars);
        use_eq = (uu___1764_23313.use_eq);
        is_iface = (uu___1764_23313.is_iface);
        admit = (uu___1764_23313.admit);
        lax = (uu___1764_23313.lax);
        lax_universes = (uu___1764_23313.lax_universes);
        phase1 = (uu___1764_23313.phase1);
        failhard = (uu___1764_23313.failhard);
        nosynth = (uu___1764_23313.nosynth);
        uvar_subtyping = (uu___1764_23313.uvar_subtyping);
        tc_term = (uu___1764_23313.tc_term);
        type_of = (uu___1764_23313.type_of);
        universe_of = (uu___1764_23313.universe_of);
        check_type_of = (uu___1764_23313.check_type_of);
        use_bv_sorts = (uu___1764_23313.use_bv_sorts);
        qtbl_name_and_index = (uu___1764_23313.qtbl_name_and_index);
        normalized_eff_names = (uu___1764_23313.normalized_eff_names);
        fv_delta_depths = (uu___1764_23313.fv_delta_depths);
        proof_ns = (uu___1764_23313.proof_ns);
        synth_hook = (uu___1764_23313.synth_hook);
        splice = (uu___1764_23313.splice);
        postprocess = (uu___1764_23313.postprocess);
        is_native_tactic = (uu___1764_23313.is_native_tactic);
        identifier_info = (uu___1764_23313.identifier_info);
        tc_hooks = (uu___1764_23313.tc_hooks);
        dsenv = (uu___1764_23313.dsenv);
        nbe = (uu___1764_23313.nbe);
        strict_args_tab = (uu___1764_23313.strict_args_tab)
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
            (let uu___1777_23371 = env  in
             {
               solver = (uu___1777_23371.solver);
               range = (uu___1777_23371.range);
               curmodule = (uu___1777_23371.curmodule);
               gamma = rest;
               gamma_sig = (uu___1777_23371.gamma_sig);
               gamma_cache = (uu___1777_23371.gamma_cache);
               modules = (uu___1777_23371.modules);
               expected_typ = (uu___1777_23371.expected_typ);
               sigtab = (uu___1777_23371.sigtab);
               attrtab = (uu___1777_23371.attrtab);
               is_pattern = (uu___1777_23371.is_pattern);
               instantiate_imp = (uu___1777_23371.instantiate_imp);
               effects = (uu___1777_23371.effects);
               generalize = (uu___1777_23371.generalize);
               letrecs = (uu___1777_23371.letrecs);
               top_level = (uu___1777_23371.top_level);
               check_uvars = (uu___1777_23371.check_uvars);
               use_eq = (uu___1777_23371.use_eq);
               is_iface = (uu___1777_23371.is_iface);
               admit = (uu___1777_23371.admit);
               lax = (uu___1777_23371.lax);
               lax_universes = (uu___1777_23371.lax_universes);
               phase1 = (uu___1777_23371.phase1);
               failhard = (uu___1777_23371.failhard);
               nosynth = (uu___1777_23371.nosynth);
               uvar_subtyping = (uu___1777_23371.uvar_subtyping);
               tc_term = (uu___1777_23371.tc_term);
               type_of = (uu___1777_23371.type_of);
               universe_of = (uu___1777_23371.universe_of);
               check_type_of = (uu___1777_23371.check_type_of);
               use_bv_sorts = (uu___1777_23371.use_bv_sorts);
               qtbl_name_and_index = (uu___1777_23371.qtbl_name_and_index);
               normalized_eff_names = (uu___1777_23371.normalized_eff_names);
               fv_delta_depths = (uu___1777_23371.fv_delta_depths);
               proof_ns = (uu___1777_23371.proof_ns);
               synth_hook = (uu___1777_23371.synth_hook);
               splice = (uu___1777_23371.splice);
               postprocess = (uu___1777_23371.postprocess);
               is_native_tactic = (uu___1777_23371.is_native_tactic);
               identifier_info = (uu___1777_23371.identifier_info);
               tc_hooks = (uu___1777_23371.tc_hooks);
               dsenv = (uu___1777_23371.dsenv);
               nbe = (uu___1777_23371.nbe);
               strict_args_tab = (uu___1777_23371.strict_args_tab)
             }))
    | uu____23372 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23401  ->
             match uu____23401 with | (x,uu____23409) -> push_bv env1 x) env
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
            let uu___1791_23444 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1791_23444.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1791_23444.FStar_Syntax_Syntax.index);
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
      (let uu___1802_23486 = env  in
       {
         solver = (uu___1802_23486.solver);
         range = (uu___1802_23486.range);
         curmodule = (uu___1802_23486.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1802_23486.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1802_23486.sigtab);
         attrtab = (uu___1802_23486.attrtab);
         is_pattern = (uu___1802_23486.is_pattern);
         instantiate_imp = (uu___1802_23486.instantiate_imp);
         effects = (uu___1802_23486.effects);
         generalize = (uu___1802_23486.generalize);
         letrecs = (uu___1802_23486.letrecs);
         top_level = (uu___1802_23486.top_level);
         check_uvars = (uu___1802_23486.check_uvars);
         use_eq = (uu___1802_23486.use_eq);
         is_iface = (uu___1802_23486.is_iface);
         admit = (uu___1802_23486.admit);
         lax = (uu___1802_23486.lax);
         lax_universes = (uu___1802_23486.lax_universes);
         phase1 = (uu___1802_23486.phase1);
         failhard = (uu___1802_23486.failhard);
         nosynth = (uu___1802_23486.nosynth);
         uvar_subtyping = (uu___1802_23486.uvar_subtyping);
         tc_term = (uu___1802_23486.tc_term);
         type_of = (uu___1802_23486.type_of);
         universe_of = (uu___1802_23486.universe_of);
         check_type_of = (uu___1802_23486.check_type_of);
         use_bv_sorts = (uu___1802_23486.use_bv_sorts);
         qtbl_name_and_index = (uu___1802_23486.qtbl_name_and_index);
         normalized_eff_names = (uu___1802_23486.normalized_eff_names);
         fv_delta_depths = (uu___1802_23486.fv_delta_depths);
         proof_ns = (uu___1802_23486.proof_ns);
         synth_hook = (uu___1802_23486.synth_hook);
         splice = (uu___1802_23486.splice);
         postprocess = (uu___1802_23486.postprocess);
         is_native_tactic = (uu___1802_23486.is_native_tactic);
         identifier_info = (uu___1802_23486.identifier_info);
         tc_hooks = (uu___1802_23486.tc_hooks);
         dsenv = (uu___1802_23486.dsenv);
         nbe = (uu___1802_23486.nbe);
         strict_args_tab = (uu___1802_23486.strict_args_tab)
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
        let uu____23530 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23530 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23558 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23558)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1817_23574 = env  in
      {
        solver = (uu___1817_23574.solver);
        range = (uu___1817_23574.range);
        curmodule = (uu___1817_23574.curmodule);
        gamma = (uu___1817_23574.gamma);
        gamma_sig = (uu___1817_23574.gamma_sig);
        gamma_cache = (uu___1817_23574.gamma_cache);
        modules = (uu___1817_23574.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1817_23574.sigtab);
        attrtab = (uu___1817_23574.attrtab);
        is_pattern = (uu___1817_23574.is_pattern);
        instantiate_imp = (uu___1817_23574.instantiate_imp);
        effects = (uu___1817_23574.effects);
        generalize = (uu___1817_23574.generalize);
        letrecs = (uu___1817_23574.letrecs);
        top_level = (uu___1817_23574.top_level);
        check_uvars = (uu___1817_23574.check_uvars);
        use_eq = false;
        is_iface = (uu___1817_23574.is_iface);
        admit = (uu___1817_23574.admit);
        lax = (uu___1817_23574.lax);
        lax_universes = (uu___1817_23574.lax_universes);
        phase1 = (uu___1817_23574.phase1);
        failhard = (uu___1817_23574.failhard);
        nosynth = (uu___1817_23574.nosynth);
        uvar_subtyping = (uu___1817_23574.uvar_subtyping);
        tc_term = (uu___1817_23574.tc_term);
        type_of = (uu___1817_23574.type_of);
        universe_of = (uu___1817_23574.universe_of);
        check_type_of = (uu___1817_23574.check_type_of);
        use_bv_sorts = (uu___1817_23574.use_bv_sorts);
        qtbl_name_and_index = (uu___1817_23574.qtbl_name_and_index);
        normalized_eff_names = (uu___1817_23574.normalized_eff_names);
        fv_delta_depths = (uu___1817_23574.fv_delta_depths);
        proof_ns = (uu___1817_23574.proof_ns);
        synth_hook = (uu___1817_23574.synth_hook);
        splice = (uu___1817_23574.splice);
        postprocess = (uu___1817_23574.postprocess);
        is_native_tactic = (uu___1817_23574.is_native_tactic);
        identifier_info = (uu___1817_23574.identifier_info);
        tc_hooks = (uu___1817_23574.tc_hooks);
        dsenv = (uu___1817_23574.dsenv);
        nbe = (uu___1817_23574.nbe);
        strict_args_tab = (uu___1817_23574.strict_args_tab)
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
    let uu____23605 = expected_typ env_  in
    ((let uu___1824_23611 = env_  in
      {
        solver = (uu___1824_23611.solver);
        range = (uu___1824_23611.range);
        curmodule = (uu___1824_23611.curmodule);
        gamma = (uu___1824_23611.gamma);
        gamma_sig = (uu___1824_23611.gamma_sig);
        gamma_cache = (uu___1824_23611.gamma_cache);
        modules = (uu___1824_23611.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1824_23611.sigtab);
        attrtab = (uu___1824_23611.attrtab);
        is_pattern = (uu___1824_23611.is_pattern);
        instantiate_imp = (uu___1824_23611.instantiate_imp);
        effects = (uu___1824_23611.effects);
        generalize = (uu___1824_23611.generalize);
        letrecs = (uu___1824_23611.letrecs);
        top_level = (uu___1824_23611.top_level);
        check_uvars = (uu___1824_23611.check_uvars);
        use_eq = false;
        is_iface = (uu___1824_23611.is_iface);
        admit = (uu___1824_23611.admit);
        lax = (uu___1824_23611.lax);
        lax_universes = (uu___1824_23611.lax_universes);
        phase1 = (uu___1824_23611.phase1);
        failhard = (uu___1824_23611.failhard);
        nosynth = (uu___1824_23611.nosynth);
        uvar_subtyping = (uu___1824_23611.uvar_subtyping);
        tc_term = (uu___1824_23611.tc_term);
        type_of = (uu___1824_23611.type_of);
        universe_of = (uu___1824_23611.universe_of);
        check_type_of = (uu___1824_23611.check_type_of);
        use_bv_sorts = (uu___1824_23611.use_bv_sorts);
        qtbl_name_and_index = (uu___1824_23611.qtbl_name_and_index);
        normalized_eff_names = (uu___1824_23611.normalized_eff_names);
        fv_delta_depths = (uu___1824_23611.fv_delta_depths);
        proof_ns = (uu___1824_23611.proof_ns);
        synth_hook = (uu___1824_23611.synth_hook);
        splice = (uu___1824_23611.splice);
        postprocess = (uu___1824_23611.postprocess);
        is_native_tactic = (uu___1824_23611.is_native_tactic);
        identifier_info = (uu___1824_23611.identifier_info);
        tc_hooks = (uu___1824_23611.tc_hooks);
        dsenv = (uu___1824_23611.dsenv);
        nbe = (uu___1824_23611.nbe);
        strict_args_tab = (uu___1824_23611.strict_args_tab)
      }), uu____23605)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23623 =
      let uu____23626 = FStar_Ident.id_of_text ""  in [uu____23626]  in
    FStar_Ident.lid_of_ids uu____23623  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23633 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23633
        then
          let uu____23638 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23638 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1832_23666 = env  in
       {
         solver = (uu___1832_23666.solver);
         range = (uu___1832_23666.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1832_23666.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1832_23666.expected_typ);
         sigtab = (uu___1832_23666.sigtab);
         attrtab = (uu___1832_23666.attrtab);
         is_pattern = (uu___1832_23666.is_pattern);
         instantiate_imp = (uu___1832_23666.instantiate_imp);
         effects = (uu___1832_23666.effects);
         generalize = (uu___1832_23666.generalize);
         letrecs = (uu___1832_23666.letrecs);
         top_level = (uu___1832_23666.top_level);
         check_uvars = (uu___1832_23666.check_uvars);
         use_eq = (uu___1832_23666.use_eq);
         is_iface = (uu___1832_23666.is_iface);
         admit = (uu___1832_23666.admit);
         lax = (uu___1832_23666.lax);
         lax_universes = (uu___1832_23666.lax_universes);
         phase1 = (uu___1832_23666.phase1);
         failhard = (uu___1832_23666.failhard);
         nosynth = (uu___1832_23666.nosynth);
         uvar_subtyping = (uu___1832_23666.uvar_subtyping);
         tc_term = (uu___1832_23666.tc_term);
         type_of = (uu___1832_23666.type_of);
         universe_of = (uu___1832_23666.universe_of);
         check_type_of = (uu___1832_23666.check_type_of);
         use_bv_sorts = (uu___1832_23666.use_bv_sorts);
         qtbl_name_and_index = (uu___1832_23666.qtbl_name_and_index);
         normalized_eff_names = (uu___1832_23666.normalized_eff_names);
         fv_delta_depths = (uu___1832_23666.fv_delta_depths);
         proof_ns = (uu___1832_23666.proof_ns);
         synth_hook = (uu___1832_23666.synth_hook);
         splice = (uu___1832_23666.splice);
         postprocess = (uu___1832_23666.postprocess);
         is_native_tactic = (uu___1832_23666.is_native_tactic);
         identifier_info = (uu___1832_23666.identifier_info);
         tc_hooks = (uu___1832_23666.tc_hooks);
         dsenv = (uu___1832_23666.dsenv);
         nbe = (uu___1832_23666.nbe);
         strict_args_tab = (uu___1832_23666.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23718)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23722,(uu____23723,t)))::tl1
          ->
          let uu____23744 =
            let uu____23747 = FStar_Syntax_Free.uvars t  in
            ext out uu____23747  in
          aux uu____23744 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23750;
            FStar_Syntax_Syntax.index = uu____23751;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23759 =
            let uu____23762 = FStar_Syntax_Free.uvars t  in
            ext out uu____23762  in
          aux uu____23759 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23820)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23824,(uu____23825,t)))::tl1
          ->
          let uu____23846 =
            let uu____23849 = FStar_Syntax_Free.univs t  in
            ext out uu____23849  in
          aux uu____23846 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23852;
            FStar_Syntax_Syntax.index = uu____23853;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23861 =
            let uu____23864 = FStar_Syntax_Free.univs t  in
            ext out uu____23864  in
          aux uu____23861 tl1
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
          let uu____23926 = FStar_Util.set_add uname out  in
          aux uu____23926 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23929,(uu____23930,t)))::tl1
          ->
          let uu____23951 =
            let uu____23954 = FStar_Syntax_Free.univnames t  in
            ext out uu____23954  in
          aux uu____23951 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23957;
            FStar_Syntax_Syntax.index = uu____23958;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23966 =
            let uu____23969 = FStar_Syntax_Free.univnames t  in
            ext out uu____23969  in
          aux uu____23966 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_23990  ->
            match uu___11_23990 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23994 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24007 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24018 =
      let uu____24027 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24027
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24018 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24075 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24088  ->
              match uu___12_24088 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24091 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24091
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24097) ->
                  let uu____24114 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24114))
       in
    FStar_All.pipe_right uu____24075 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24128  ->
    match uu___13_24128 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24134 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24134
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24157  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24212) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24245,uu____24246) -> false  in
      let uu____24260 =
        FStar_List.tryFind
          (fun uu____24282  ->
             match uu____24282 with | (p,uu____24293) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24260 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24312,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24342 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24342
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1975_24364 = e  in
        {
          solver = (uu___1975_24364.solver);
          range = (uu___1975_24364.range);
          curmodule = (uu___1975_24364.curmodule);
          gamma = (uu___1975_24364.gamma);
          gamma_sig = (uu___1975_24364.gamma_sig);
          gamma_cache = (uu___1975_24364.gamma_cache);
          modules = (uu___1975_24364.modules);
          expected_typ = (uu___1975_24364.expected_typ);
          sigtab = (uu___1975_24364.sigtab);
          attrtab = (uu___1975_24364.attrtab);
          is_pattern = (uu___1975_24364.is_pattern);
          instantiate_imp = (uu___1975_24364.instantiate_imp);
          effects = (uu___1975_24364.effects);
          generalize = (uu___1975_24364.generalize);
          letrecs = (uu___1975_24364.letrecs);
          top_level = (uu___1975_24364.top_level);
          check_uvars = (uu___1975_24364.check_uvars);
          use_eq = (uu___1975_24364.use_eq);
          is_iface = (uu___1975_24364.is_iface);
          admit = (uu___1975_24364.admit);
          lax = (uu___1975_24364.lax);
          lax_universes = (uu___1975_24364.lax_universes);
          phase1 = (uu___1975_24364.phase1);
          failhard = (uu___1975_24364.failhard);
          nosynth = (uu___1975_24364.nosynth);
          uvar_subtyping = (uu___1975_24364.uvar_subtyping);
          tc_term = (uu___1975_24364.tc_term);
          type_of = (uu___1975_24364.type_of);
          universe_of = (uu___1975_24364.universe_of);
          check_type_of = (uu___1975_24364.check_type_of);
          use_bv_sorts = (uu___1975_24364.use_bv_sorts);
          qtbl_name_and_index = (uu___1975_24364.qtbl_name_and_index);
          normalized_eff_names = (uu___1975_24364.normalized_eff_names);
          fv_delta_depths = (uu___1975_24364.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1975_24364.synth_hook);
          splice = (uu___1975_24364.splice);
          postprocess = (uu___1975_24364.postprocess);
          is_native_tactic = (uu___1975_24364.is_native_tactic);
          identifier_info = (uu___1975_24364.identifier_info);
          tc_hooks = (uu___1975_24364.tc_hooks);
          dsenv = (uu___1975_24364.dsenv);
          nbe = (uu___1975_24364.nbe);
          strict_args_tab = (uu___1975_24364.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1984_24412 = e  in
      {
        solver = (uu___1984_24412.solver);
        range = (uu___1984_24412.range);
        curmodule = (uu___1984_24412.curmodule);
        gamma = (uu___1984_24412.gamma);
        gamma_sig = (uu___1984_24412.gamma_sig);
        gamma_cache = (uu___1984_24412.gamma_cache);
        modules = (uu___1984_24412.modules);
        expected_typ = (uu___1984_24412.expected_typ);
        sigtab = (uu___1984_24412.sigtab);
        attrtab = (uu___1984_24412.attrtab);
        is_pattern = (uu___1984_24412.is_pattern);
        instantiate_imp = (uu___1984_24412.instantiate_imp);
        effects = (uu___1984_24412.effects);
        generalize = (uu___1984_24412.generalize);
        letrecs = (uu___1984_24412.letrecs);
        top_level = (uu___1984_24412.top_level);
        check_uvars = (uu___1984_24412.check_uvars);
        use_eq = (uu___1984_24412.use_eq);
        is_iface = (uu___1984_24412.is_iface);
        admit = (uu___1984_24412.admit);
        lax = (uu___1984_24412.lax);
        lax_universes = (uu___1984_24412.lax_universes);
        phase1 = (uu___1984_24412.phase1);
        failhard = (uu___1984_24412.failhard);
        nosynth = (uu___1984_24412.nosynth);
        uvar_subtyping = (uu___1984_24412.uvar_subtyping);
        tc_term = (uu___1984_24412.tc_term);
        type_of = (uu___1984_24412.type_of);
        universe_of = (uu___1984_24412.universe_of);
        check_type_of = (uu___1984_24412.check_type_of);
        use_bv_sorts = (uu___1984_24412.use_bv_sorts);
        qtbl_name_and_index = (uu___1984_24412.qtbl_name_and_index);
        normalized_eff_names = (uu___1984_24412.normalized_eff_names);
        fv_delta_depths = (uu___1984_24412.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1984_24412.synth_hook);
        splice = (uu___1984_24412.splice);
        postprocess = (uu___1984_24412.postprocess);
        is_native_tactic = (uu___1984_24412.is_native_tactic);
        identifier_info = (uu___1984_24412.identifier_info);
        tc_hooks = (uu___1984_24412.tc_hooks);
        dsenv = (uu___1984_24412.dsenv);
        nbe = (uu___1984_24412.nbe);
        strict_args_tab = (uu___1984_24412.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24428 = FStar_Syntax_Free.names t  in
      let uu____24431 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24428 uu____24431
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24454 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24454
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24464 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24464
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24485 =
      match uu____24485 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24505 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24505)
       in
    let uu____24513 =
      let uu____24517 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24517 FStar_List.rev  in
    FStar_All.pipe_right uu____24513 (FStar_String.concat " ")
  
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
                  (let uu____24587 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24587 with
                   | FStar_Pervasives_Native.Some uu____24591 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24594 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24604;
        univ_ineqs = uu____24605; implicits = uu____24606;_} -> true
    | uu____24618 -> false
  
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
          let uu___2028_24649 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2028_24649.deferred);
            univ_ineqs = (uu___2028_24649.univ_ineqs);
            implicits = (uu___2028_24649.implicits)
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
          let uu____24688 = FStar_Options.defensive ()  in
          if uu____24688
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24694 =
              let uu____24696 =
                let uu____24698 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24698  in
              Prims.op_Negation uu____24696  in
            (if uu____24694
             then
               let uu____24705 =
                 let uu____24711 =
                   let uu____24713 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24715 =
                     let uu____24717 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24717
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24713 uu____24715
                    in
                 (FStar_Errors.Warning_Defensive, uu____24711)  in
               FStar_Errors.log_issue rng uu____24705
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
          let uu____24757 =
            let uu____24759 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24759  in
          if uu____24757
          then ()
          else
            (let uu____24764 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24764 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24790 =
            let uu____24792 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24792  in
          if uu____24790
          then ()
          else
            (let uu____24797 = bound_vars e  in
             def_check_closed_in rng msg uu____24797 t)
  
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
          let uu___2065_24836 = g  in
          let uu____24837 =
            let uu____24838 =
              let uu____24839 =
                let uu____24846 =
                  let uu____24847 =
                    let uu____24864 =
                      let uu____24875 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24875]  in
                    (f, uu____24864)  in
                  FStar_Syntax_Syntax.Tm_app uu____24847  in
                FStar_Syntax_Syntax.mk uu____24846  in
              uu____24839 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24912  -> FStar_TypeChecker_Common.NonTrivial _24912)
              uu____24838
             in
          {
            guard_f = uu____24837;
            deferred = (uu___2065_24836.deferred);
            univ_ineqs = (uu___2065_24836.univ_ineqs);
            implicits = (uu___2065_24836.implicits)
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
          let uu___2072_24930 = g  in
          let uu____24931 =
            let uu____24932 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24932  in
          {
            guard_f = uu____24931;
            deferred = (uu___2072_24930.deferred);
            univ_ineqs = (uu___2072_24930.univ_ineqs);
            implicits = (uu___2072_24930.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2077_24949 = g  in
          let uu____24950 =
            let uu____24951 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24951  in
          {
            guard_f = uu____24950;
            deferred = (uu___2077_24949.deferred);
            univ_ineqs = (uu___2077_24949.univ_ineqs);
            implicits = (uu___2077_24949.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2081_24953 = g  in
          let uu____24954 =
            let uu____24955 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24955  in
          {
            guard_f = uu____24954;
            deferred = (uu___2081_24953.deferred);
            univ_ineqs = (uu___2081_24953.univ_ineqs);
            implicits = (uu___2081_24953.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24962 ->
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
          let uu____24979 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24979
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24986 =
      let uu____24987 = FStar_Syntax_Util.unmeta t  in
      uu____24987.FStar_Syntax_Syntax.n  in
    match uu____24986 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24991 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25034 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25034;
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
                       let uu____25129 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25129
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2136_25136 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2136_25136.deferred);
              univ_ineqs = (uu___2136_25136.univ_ineqs);
              implicits = (uu___2136_25136.implicits)
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
               let uu____25170 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25170
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
            let uu___2151_25197 = g  in
            let uu____25198 =
              let uu____25199 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25199  in
            {
              guard_f = uu____25198;
              deferred = (uu___2151_25197.deferred);
              univ_ineqs = (uu___2151_25197.univ_ineqs);
              implicits = (uu___2151_25197.implicits)
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
              let uu____25257 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25257 with
              | FStar_Pervasives_Native.Some
                  (uu____25282::(tm,uu____25284)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25348 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25366 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25366;
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
                      let uu___2173_25398 = trivial_guard  in
                      {
                        guard_f = (uu___2173_25398.guard_f);
                        deferred = (uu___2173_25398.deferred);
                        univ_ineqs = (uu___2173_25398.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25416  -> ());
    push = (fun uu____25418  -> ());
    pop = (fun uu____25421  -> ());
    snapshot =
      (fun uu____25424  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25443  -> fun uu____25444  -> ());
    encode_sig = (fun uu____25459  -> fun uu____25460  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25466 =
             let uu____25473 = FStar_Options.peek ()  in (e, g, uu____25473)
              in
           [uu____25466]);
    solve = (fun uu____25489  -> fun uu____25490  -> fun uu____25491  -> ());
    finish = (fun uu____25498  -> ());
    refresh = (fun uu____25500  -> ())
  } 