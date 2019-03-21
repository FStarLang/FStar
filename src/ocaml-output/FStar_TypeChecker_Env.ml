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
  fun projectee  ->
    match projectee with | Beta  -> true | uu____51477 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____51488 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____51499 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____51511 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____51529 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____51540 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____51551 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____51562 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____51573 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____51584 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____51596 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____51617 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____51644 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____51671 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____51695 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____51706 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____51717 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____51728 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____51739 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____51750 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____51761 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____51772 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____51783 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____51794 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____51805 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____51816 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____51827 -> false
  
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
      | uu____51887 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____51913 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____51924 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____51935 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____51947 -> false
  
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
           (fun uu___446_63164  ->
              match uu___446_63164 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____63167 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____63167  in
                  let uu____63168 =
                    let uu____63169 = FStar_Syntax_Subst.compress y  in
                    uu____63169.FStar_Syntax_Syntax.n  in
                  (match uu____63168 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____63173 =
                         let uu___775_63174 = y1  in
                         let uu____63175 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_63174.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_63174.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____63175
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____63173
                   | uu____63178 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_63192 = env  in
      let uu____63193 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_63192.solver);
        range = (uu___781_63192.range);
        curmodule = (uu___781_63192.curmodule);
        gamma = uu____63193;
        gamma_sig = (uu___781_63192.gamma_sig);
        gamma_cache = (uu___781_63192.gamma_cache);
        modules = (uu___781_63192.modules);
        expected_typ = (uu___781_63192.expected_typ);
        sigtab = (uu___781_63192.sigtab);
        attrtab = (uu___781_63192.attrtab);
        is_pattern = (uu___781_63192.is_pattern);
        instantiate_imp = (uu___781_63192.instantiate_imp);
        effects = (uu___781_63192.effects);
        generalize = (uu___781_63192.generalize);
        letrecs = (uu___781_63192.letrecs);
        top_level = (uu___781_63192.top_level);
        check_uvars = (uu___781_63192.check_uvars);
        use_eq = (uu___781_63192.use_eq);
        is_iface = (uu___781_63192.is_iface);
        admit = (uu___781_63192.admit);
        lax = (uu___781_63192.lax);
        lax_universes = (uu___781_63192.lax_universes);
        phase1 = (uu___781_63192.phase1);
        failhard = (uu___781_63192.failhard);
        nosynth = (uu___781_63192.nosynth);
        uvar_subtyping = (uu___781_63192.uvar_subtyping);
        tc_term = (uu___781_63192.tc_term);
        type_of = (uu___781_63192.type_of);
        universe_of = (uu___781_63192.universe_of);
        check_type_of = (uu___781_63192.check_type_of);
        use_bv_sorts = (uu___781_63192.use_bv_sorts);
        qtbl_name_and_index = (uu___781_63192.qtbl_name_and_index);
        normalized_eff_names = (uu___781_63192.normalized_eff_names);
        fv_delta_depths = (uu___781_63192.fv_delta_depths);
        proof_ns = (uu___781_63192.proof_ns);
        synth_hook = (uu___781_63192.synth_hook);
        splice = (uu___781_63192.splice);
        postprocess = (uu___781_63192.postprocess);
        is_native_tactic = (uu___781_63192.is_native_tactic);
        identifier_info = (uu___781_63192.identifier_info);
        tc_hooks = (uu___781_63192.tc_hooks);
        dsenv = (uu___781_63192.dsenv);
        nbe = (uu___781_63192.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____63201  -> fun uu____63202  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_63224 = env  in
      {
        solver = (uu___788_63224.solver);
        range = (uu___788_63224.range);
        curmodule = (uu___788_63224.curmodule);
        gamma = (uu___788_63224.gamma);
        gamma_sig = (uu___788_63224.gamma_sig);
        gamma_cache = (uu___788_63224.gamma_cache);
        modules = (uu___788_63224.modules);
        expected_typ = (uu___788_63224.expected_typ);
        sigtab = (uu___788_63224.sigtab);
        attrtab = (uu___788_63224.attrtab);
        is_pattern = (uu___788_63224.is_pattern);
        instantiate_imp = (uu___788_63224.instantiate_imp);
        effects = (uu___788_63224.effects);
        generalize = (uu___788_63224.generalize);
        letrecs = (uu___788_63224.letrecs);
        top_level = (uu___788_63224.top_level);
        check_uvars = (uu___788_63224.check_uvars);
        use_eq = (uu___788_63224.use_eq);
        is_iface = (uu___788_63224.is_iface);
        admit = (uu___788_63224.admit);
        lax = (uu___788_63224.lax);
        lax_universes = (uu___788_63224.lax_universes);
        phase1 = (uu___788_63224.phase1);
        failhard = (uu___788_63224.failhard);
        nosynth = (uu___788_63224.nosynth);
        uvar_subtyping = (uu___788_63224.uvar_subtyping);
        tc_term = (uu___788_63224.tc_term);
        type_of = (uu___788_63224.type_of);
        universe_of = (uu___788_63224.universe_of);
        check_type_of = (uu___788_63224.check_type_of);
        use_bv_sorts = (uu___788_63224.use_bv_sorts);
        qtbl_name_and_index = (uu___788_63224.qtbl_name_and_index);
        normalized_eff_names = (uu___788_63224.normalized_eff_names);
        fv_delta_depths = (uu___788_63224.fv_delta_depths);
        proof_ns = (uu___788_63224.proof_ns);
        synth_hook = (uu___788_63224.synth_hook);
        splice = (uu___788_63224.splice);
        postprocess = (uu___788_63224.postprocess);
        is_native_tactic = (uu___788_63224.is_native_tactic);
        identifier_info = (uu___788_63224.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_63224.dsenv);
        nbe = (uu___788_63224.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_63236 = e  in
      let uu____63237 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_63236.solver);
        range = (uu___792_63236.range);
        curmodule = (uu___792_63236.curmodule);
        gamma = (uu___792_63236.gamma);
        gamma_sig = (uu___792_63236.gamma_sig);
        gamma_cache = (uu___792_63236.gamma_cache);
        modules = (uu___792_63236.modules);
        expected_typ = (uu___792_63236.expected_typ);
        sigtab = (uu___792_63236.sigtab);
        attrtab = (uu___792_63236.attrtab);
        is_pattern = (uu___792_63236.is_pattern);
        instantiate_imp = (uu___792_63236.instantiate_imp);
        effects = (uu___792_63236.effects);
        generalize = (uu___792_63236.generalize);
        letrecs = (uu___792_63236.letrecs);
        top_level = (uu___792_63236.top_level);
        check_uvars = (uu___792_63236.check_uvars);
        use_eq = (uu___792_63236.use_eq);
        is_iface = (uu___792_63236.is_iface);
        admit = (uu___792_63236.admit);
        lax = (uu___792_63236.lax);
        lax_universes = (uu___792_63236.lax_universes);
        phase1 = (uu___792_63236.phase1);
        failhard = (uu___792_63236.failhard);
        nosynth = (uu___792_63236.nosynth);
        uvar_subtyping = (uu___792_63236.uvar_subtyping);
        tc_term = (uu___792_63236.tc_term);
        type_of = (uu___792_63236.type_of);
        universe_of = (uu___792_63236.universe_of);
        check_type_of = (uu___792_63236.check_type_of);
        use_bv_sorts = (uu___792_63236.use_bv_sorts);
        qtbl_name_and_index = (uu___792_63236.qtbl_name_and_index);
        normalized_eff_names = (uu___792_63236.normalized_eff_names);
        fv_delta_depths = (uu___792_63236.fv_delta_depths);
        proof_ns = (uu___792_63236.proof_ns);
        synth_hook = (uu___792_63236.synth_hook);
        splice = (uu___792_63236.splice);
        postprocess = (uu___792_63236.postprocess);
        is_native_tactic = (uu___792_63236.is_native_tactic);
        identifier_info = (uu___792_63236.identifier_info);
        tc_hooks = (uu___792_63236.tc_hooks);
        dsenv = uu____63237;
        nbe = (uu___792_63236.nbe)
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
      | (NoDelta ,uu____63266) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____63269,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____63271,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____63274 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____63288 . unit -> 'Auu____63288 FStar_Util.smap =
  fun uu____63295  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____63301 . unit -> 'Auu____63301 FStar_Util.smap =
  fun uu____63308  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____63446 = new_gamma_cache ()  in
                  let uu____63449 = new_sigtab ()  in
                  let uu____63452 = new_sigtab ()  in
                  let uu____63459 =
                    let uu____63474 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____63474, FStar_Pervasives_Native.None)  in
                  let uu____63495 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____63499 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____63503 = FStar_Options.using_facts_from ()  in
                  let uu____63504 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____63507 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____63446;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____63449;
                    attrtab = uu____63452;
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
                    qtbl_name_and_index = uu____63459;
                    normalized_eff_names = uu____63495;
                    fv_delta_depths = uu____63499;
                    proof_ns = uu____63503;
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
                    is_native_tactic = (fun uu____63569  -> false);
                    identifier_info = uu____63504;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____63507;
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
  fun uu____63648  ->
    let uu____63649 = FStar_ST.op_Bang query_indices  in
    match uu____63649 with
    | [] -> failwith "Empty query indices!"
    | uu____63704 ->
        let uu____63714 =
          let uu____63724 =
            let uu____63732 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____63732  in
          let uu____63786 = FStar_ST.op_Bang query_indices  in uu____63724 ::
            uu____63786
           in
        FStar_ST.op_Colon_Equals query_indices uu____63714
  
let (pop_query_indices : unit -> unit) =
  fun uu____63882  ->
    let uu____63883 = FStar_ST.op_Bang query_indices  in
    match uu____63883 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____64010  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____64047  ->
    match uu____64047 with
    | (l,n1) ->
        let uu____64057 = FStar_ST.op_Bang query_indices  in
        (match uu____64057 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____64179 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____64202  ->
    let uu____64203 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____64203
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____64271 =
       let uu____64274 = FStar_ST.op_Bang stack  in env :: uu____64274  in
     FStar_ST.op_Colon_Equals stack uu____64271);
    (let uu___860_64323 = env  in
     let uu____64324 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____64327 = FStar_Util.smap_copy (sigtab env)  in
     let uu____64330 = FStar_Util.smap_copy (attrtab env)  in
     let uu____64337 =
       let uu____64352 =
         let uu____64356 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____64356  in
       let uu____64388 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____64352, uu____64388)  in
     let uu____64437 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____64440 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____64443 =
       let uu____64446 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____64446  in
     {
       solver = (uu___860_64323.solver);
       range = (uu___860_64323.range);
       curmodule = (uu___860_64323.curmodule);
       gamma = (uu___860_64323.gamma);
       gamma_sig = (uu___860_64323.gamma_sig);
       gamma_cache = uu____64324;
       modules = (uu___860_64323.modules);
       expected_typ = (uu___860_64323.expected_typ);
       sigtab = uu____64327;
       attrtab = uu____64330;
       is_pattern = (uu___860_64323.is_pattern);
       instantiate_imp = (uu___860_64323.instantiate_imp);
       effects = (uu___860_64323.effects);
       generalize = (uu___860_64323.generalize);
       letrecs = (uu___860_64323.letrecs);
       top_level = (uu___860_64323.top_level);
       check_uvars = (uu___860_64323.check_uvars);
       use_eq = (uu___860_64323.use_eq);
       is_iface = (uu___860_64323.is_iface);
       admit = (uu___860_64323.admit);
       lax = (uu___860_64323.lax);
       lax_universes = (uu___860_64323.lax_universes);
       phase1 = (uu___860_64323.phase1);
       failhard = (uu___860_64323.failhard);
       nosynth = (uu___860_64323.nosynth);
       uvar_subtyping = (uu___860_64323.uvar_subtyping);
       tc_term = (uu___860_64323.tc_term);
       type_of = (uu___860_64323.type_of);
       universe_of = (uu___860_64323.universe_of);
       check_type_of = (uu___860_64323.check_type_of);
       use_bv_sorts = (uu___860_64323.use_bv_sorts);
       qtbl_name_and_index = uu____64337;
       normalized_eff_names = uu____64437;
       fv_delta_depths = uu____64440;
       proof_ns = (uu___860_64323.proof_ns);
       synth_hook = (uu___860_64323.synth_hook);
       splice = (uu___860_64323.splice);
       postprocess = (uu___860_64323.postprocess);
       is_native_tactic = (uu___860_64323.is_native_tactic);
       identifier_info = uu____64443;
       tc_hooks = (uu___860_64323.tc_hooks);
       dsenv = (uu___860_64323.dsenv);
       nbe = (uu___860_64323.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____64471  ->
    let uu____64472 = FStar_ST.op_Bang stack  in
    match uu____64472 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____64526 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____64616  ->
           let uu____64617 = snapshot_stack env  in
           match uu____64617 with
           | (stack_depth,env1) ->
               let uu____64651 = snapshot_query_indices ()  in
               (match uu____64651 with
                | (query_indices_depth,()) ->
                    let uu____64684 = (env1.solver).snapshot msg  in
                    (match uu____64684 with
                     | (solver_depth,()) ->
                         let uu____64741 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____64741 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_64808 = env1  in
                                 {
                                   solver = (uu___885_64808.solver);
                                   range = (uu___885_64808.range);
                                   curmodule = (uu___885_64808.curmodule);
                                   gamma = (uu___885_64808.gamma);
                                   gamma_sig = (uu___885_64808.gamma_sig);
                                   gamma_cache = (uu___885_64808.gamma_cache);
                                   modules = (uu___885_64808.modules);
                                   expected_typ =
                                     (uu___885_64808.expected_typ);
                                   sigtab = (uu___885_64808.sigtab);
                                   attrtab = (uu___885_64808.attrtab);
                                   is_pattern = (uu___885_64808.is_pattern);
                                   instantiate_imp =
                                     (uu___885_64808.instantiate_imp);
                                   effects = (uu___885_64808.effects);
                                   generalize = (uu___885_64808.generalize);
                                   letrecs = (uu___885_64808.letrecs);
                                   top_level = (uu___885_64808.top_level);
                                   check_uvars = (uu___885_64808.check_uvars);
                                   use_eq = (uu___885_64808.use_eq);
                                   is_iface = (uu___885_64808.is_iface);
                                   admit = (uu___885_64808.admit);
                                   lax = (uu___885_64808.lax);
                                   lax_universes =
                                     (uu___885_64808.lax_universes);
                                   phase1 = (uu___885_64808.phase1);
                                   failhard = (uu___885_64808.failhard);
                                   nosynth = (uu___885_64808.nosynth);
                                   uvar_subtyping =
                                     (uu___885_64808.uvar_subtyping);
                                   tc_term = (uu___885_64808.tc_term);
                                   type_of = (uu___885_64808.type_of);
                                   universe_of = (uu___885_64808.universe_of);
                                   check_type_of =
                                     (uu___885_64808.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_64808.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_64808.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_64808.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_64808.fv_delta_depths);
                                   proof_ns = (uu___885_64808.proof_ns);
                                   synth_hook = (uu___885_64808.synth_hook);
                                   splice = (uu___885_64808.splice);
                                   postprocess = (uu___885_64808.postprocess);
                                   is_native_tactic =
                                     (uu___885_64808.is_native_tactic);
                                   identifier_info =
                                     (uu___885_64808.identifier_info);
                                   tc_hooks = (uu___885_64808.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_64808.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____64842  ->
             let uu____64843 =
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
             match uu____64843 with
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
                             ((let uu____65023 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____65023
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____65039 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____65039
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____65071,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____65113 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____65143  ->
                  match uu____65143 with
                  | (m,uu____65151) -> FStar_Ident.lid_equals l m))
           in
        (match uu____65113 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_65166 = env  in
               {
                 solver = (uu___930_65166.solver);
                 range = (uu___930_65166.range);
                 curmodule = (uu___930_65166.curmodule);
                 gamma = (uu___930_65166.gamma);
                 gamma_sig = (uu___930_65166.gamma_sig);
                 gamma_cache = (uu___930_65166.gamma_cache);
                 modules = (uu___930_65166.modules);
                 expected_typ = (uu___930_65166.expected_typ);
                 sigtab = (uu___930_65166.sigtab);
                 attrtab = (uu___930_65166.attrtab);
                 is_pattern = (uu___930_65166.is_pattern);
                 instantiate_imp = (uu___930_65166.instantiate_imp);
                 effects = (uu___930_65166.effects);
                 generalize = (uu___930_65166.generalize);
                 letrecs = (uu___930_65166.letrecs);
                 top_level = (uu___930_65166.top_level);
                 check_uvars = (uu___930_65166.check_uvars);
                 use_eq = (uu___930_65166.use_eq);
                 is_iface = (uu___930_65166.is_iface);
                 admit = (uu___930_65166.admit);
                 lax = (uu___930_65166.lax);
                 lax_universes = (uu___930_65166.lax_universes);
                 phase1 = (uu___930_65166.phase1);
                 failhard = (uu___930_65166.failhard);
                 nosynth = (uu___930_65166.nosynth);
                 uvar_subtyping = (uu___930_65166.uvar_subtyping);
                 tc_term = (uu___930_65166.tc_term);
                 type_of = (uu___930_65166.type_of);
                 universe_of = (uu___930_65166.universe_of);
                 check_type_of = (uu___930_65166.check_type_of);
                 use_bv_sorts = (uu___930_65166.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_65166.normalized_eff_names);
                 fv_delta_depths = (uu___930_65166.fv_delta_depths);
                 proof_ns = (uu___930_65166.proof_ns);
                 synth_hook = (uu___930_65166.synth_hook);
                 splice = (uu___930_65166.splice);
                 postprocess = (uu___930_65166.postprocess);
                 is_native_tactic = (uu___930_65166.is_native_tactic);
                 identifier_info = (uu___930_65166.identifier_info);
                 tc_hooks = (uu___930_65166.tc_hooks);
                 dsenv = (uu___930_65166.dsenv);
                 nbe = (uu___930_65166.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____65183,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_65199 = env  in
               {
                 solver = (uu___939_65199.solver);
                 range = (uu___939_65199.range);
                 curmodule = (uu___939_65199.curmodule);
                 gamma = (uu___939_65199.gamma);
                 gamma_sig = (uu___939_65199.gamma_sig);
                 gamma_cache = (uu___939_65199.gamma_cache);
                 modules = (uu___939_65199.modules);
                 expected_typ = (uu___939_65199.expected_typ);
                 sigtab = (uu___939_65199.sigtab);
                 attrtab = (uu___939_65199.attrtab);
                 is_pattern = (uu___939_65199.is_pattern);
                 instantiate_imp = (uu___939_65199.instantiate_imp);
                 effects = (uu___939_65199.effects);
                 generalize = (uu___939_65199.generalize);
                 letrecs = (uu___939_65199.letrecs);
                 top_level = (uu___939_65199.top_level);
                 check_uvars = (uu___939_65199.check_uvars);
                 use_eq = (uu___939_65199.use_eq);
                 is_iface = (uu___939_65199.is_iface);
                 admit = (uu___939_65199.admit);
                 lax = (uu___939_65199.lax);
                 lax_universes = (uu___939_65199.lax_universes);
                 phase1 = (uu___939_65199.phase1);
                 failhard = (uu___939_65199.failhard);
                 nosynth = (uu___939_65199.nosynth);
                 uvar_subtyping = (uu___939_65199.uvar_subtyping);
                 tc_term = (uu___939_65199.tc_term);
                 type_of = (uu___939_65199.type_of);
                 universe_of = (uu___939_65199.universe_of);
                 check_type_of = (uu___939_65199.check_type_of);
                 use_bv_sorts = (uu___939_65199.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_65199.normalized_eff_names);
                 fv_delta_depths = (uu___939_65199.fv_delta_depths);
                 proof_ns = (uu___939_65199.proof_ns);
                 synth_hook = (uu___939_65199.synth_hook);
                 splice = (uu___939_65199.splice);
                 postprocess = (uu___939_65199.postprocess);
                 is_native_tactic = (uu___939_65199.is_native_tactic);
                 identifier_info = (uu___939_65199.identifier_info);
                 tc_hooks = (uu___939_65199.tc_hooks);
                 dsenv = (uu___939_65199.dsenv);
                 nbe = (uu___939_65199.nbe)
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
        (let uu___946_65242 = e  in
         {
           solver = (uu___946_65242.solver);
           range = r;
           curmodule = (uu___946_65242.curmodule);
           gamma = (uu___946_65242.gamma);
           gamma_sig = (uu___946_65242.gamma_sig);
           gamma_cache = (uu___946_65242.gamma_cache);
           modules = (uu___946_65242.modules);
           expected_typ = (uu___946_65242.expected_typ);
           sigtab = (uu___946_65242.sigtab);
           attrtab = (uu___946_65242.attrtab);
           is_pattern = (uu___946_65242.is_pattern);
           instantiate_imp = (uu___946_65242.instantiate_imp);
           effects = (uu___946_65242.effects);
           generalize = (uu___946_65242.generalize);
           letrecs = (uu___946_65242.letrecs);
           top_level = (uu___946_65242.top_level);
           check_uvars = (uu___946_65242.check_uvars);
           use_eq = (uu___946_65242.use_eq);
           is_iface = (uu___946_65242.is_iface);
           admit = (uu___946_65242.admit);
           lax = (uu___946_65242.lax);
           lax_universes = (uu___946_65242.lax_universes);
           phase1 = (uu___946_65242.phase1);
           failhard = (uu___946_65242.failhard);
           nosynth = (uu___946_65242.nosynth);
           uvar_subtyping = (uu___946_65242.uvar_subtyping);
           tc_term = (uu___946_65242.tc_term);
           type_of = (uu___946_65242.type_of);
           universe_of = (uu___946_65242.universe_of);
           check_type_of = (uu___946_65242.check_type_of);
           use_bv_sorts = (uu___946_65242.use_bv_sorts);
           qtbl_name_and_index = (uu___946_65242.qtbl_name_and_index);
           normalized_eff_names = (uu___946_65242.normalized_eff_names);
           fv_delta_depths = (uu___946_65242.fv_delta_depths);
           proof_ns = (uu___946_65242.proof_ns);
           synth_hook = (uu___946_65242.synth_hook);
           splice = (uu___946_65242.splice);
           postprocess = (uu___946_65242.postprocess);
           is_native_tactic = (uu___946_65242.is_native_tactic);
           identifier_info = (uu___946_65242.identifier_info);
           tc_hooks = (uu___946_65242.tc_hooks);
           dsenv = (uu___946_65242.dsenv);
           nbe = (uu___946_65242.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____65262 =
        let uu____65263 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____65263 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65262
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____65318 =
          let uu____65319 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____65319 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65318
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____65374 =
          let uu____65375 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____65375 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65374
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____65430 =
        let uu____65431 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____65431 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65430
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_65495 = env  in
      {
        solver = (uu___963_65495.solver);
        range = (uu___963_65495.range);
        curmodule = lid;
        gamma = (uu___963_65495.gamma);
        gamma_sig = (uu___963_65495.gamma_sig);
        gamma_cache = (uu___963_65495.gamma_cache);
        modules = (uu___963_65495.modules);
        expected_typ = (uu___963_65495.expected_typ);
        sigtab = (uu___963_65495.sigtab);
        attrtab = (uu___963_65495.attrtab);
        is_pattern = (uu___963_65495.is_pattern);
        instantiate_imp = (uu___963_65495.instantiate_imp);
        effects = (uu___963_65495.effects);
        generalize = (uu___963_65495.generalize);
        letrecs = (uu___963_65495.letrecs);
        top_level = (uu___963_65495.top_level);
        check_uvars = (uu___963_65495.check_uvars);
        use_eq = (uu___963_65495.use_eq);
        is_iface = (uu___963_65495.is_iface);
        admit = (uu___963_65495.admit);
        lax = (uu___963_65495.lax);
        lax_universes = (uu___963_65495.lax_universes);
        phase1 = (uu___963_65495.phase1);
        failhard = (uu___963_65495.failhard);
        nosynth = (uu___963_65495.nosynth);
        uvar_subtyping = (uu___963_65495.uvar_subtyping);
        tc_term = (uu___963_65495.tc_term);
        type_of = (uu___963_65495.type_of);
        universe_of = (uu___963_65495.universe_of);
        check_type_of = (uu___963_65495.check_type_of);
        use_bv_sorts = (uu___963_65495.use_bv_sorts);
        qtbl_name_and_index = (uu___963_65495.qtbl_name_and_index);
        normalized_eff_names = (uu___963_65495.normalized_eff_names);
        fv_delta_depths = (uu___963_65495.fv_delta_depths);
        proof_ns = (uu___963_65495.proof_ns);
        synth_hook = (uu___963_65495.synth_hook);
        splice = (uu___963_65495.splice);
        postprocess = (uu___963_65495.postprocess);
        is_native_tactic = (uu___963_65495.is_native_tactic);
        identifier_info = (uu___963_65495.identifier_info);
        tc_hooks = (uu___963_65495.tc_hooks);
        dsenv = (uu___963_65495.dsenv);
        nbe = (uu___963_65495.nbe)
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
      let uu____65526 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____65526
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65539 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____65539)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____65554 =
      let uu____65556 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____65556  in
    (FStar_Errors.Fatal_VariableNotFound, uu____65554)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____65565  ->
    let uu____65566 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____65566
  
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
      | ((formals,t),uu____65666) ->
          let vs = mk_univ_subst formals us  in
          let uu____65690 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____65690)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_65707  ->
    match uu___447_65707 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____65733  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____65753 = inst_tscheme t  in
      match uu____65753 with
      | (us,t1) ->
          let uu____65764 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____65764)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____65785  ->
          match uu____65785 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____65807 =
                         let uu____65809 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____65813 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____65817 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____65819 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____65809 uu____65813 uu____65817 uu____65819
                          in
                       failwith uu____65807)
                    else ();
                    (let uu____65824 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____65824))
               | uu____65833 ->
                   let uu____65834 =
                     let uu____65836 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____65836
                      in
                   failwith uu____65834)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____65848 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____65859 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____65870 -> false
  
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
             | ([],uu____65918) -> Maybe
             | (uu____65925,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____65945 -> No  in
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
          let uu____66039 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____66039 with
          | FStar_Pervasives_Native.None  ->
              let uu____66062 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_66106  ->
                     match uu___448_66106 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____66145 = FStar_Ident.lid_equals lid l  in
                         if uu____66145
                         then
                           let uu____66168 =
                             let uu____66187 =
                               let uu____66202 = inst_tscheme t  in
                               FStar_Util.Inl uu____66202  in
                             let uu____66217 = FStar_Ident.range_of_lid l  in
                             (uu____66187, uu____66217)  in
                           FStar_Pervasives_Native.Some uu____66168
                         else FStar_Pervasives_Native.None
                     | uu____66270 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____66062
                (fun uu____66308  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_66317  ->
                        match uu___449_66317 with
                        | (uu____66320,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____66322);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____66323;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____66324;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____66325;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____66326;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____66346 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____66346
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
                                  uu____66398 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____66405 -> cache t  in
                            let uu____66406 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____66406 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____66412 =
                                   let uu____66413 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____66413)
                                    in
                                 maybe_cache uu____66412)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____66484 = find_in_sigtab env lid  in
         match uu____66484 with
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
      let uu____66565 = lookup_qname env lid  in
      match uu____66565 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____66586,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____66700 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____66700 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____66745 =
          let uu____66748 = lookup_attr env1 attr  in se1 :: uu____66748  in
        FStar_Util.smap_add (attrtab env1) attr uu____66745  in
      FStar_List.iter
        (fun attr  ->
           let uu____66758 =
             let uu____66759 = FStar_Syntax_Subst.compress attr  in
             uu____66759.FStar_Syntax_Syntax.n  in
           match uu____66758 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____66763 =
                 let uu____66765 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____66765.FStar_Ident.str  in
               add_one1 env se uu____66763
           | uu____66766 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____66789) ->
          add_sigelts env ses
      | uu____66798 ->
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
            | uu____66813 -> ()))

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
        (fun uu___450_66845  ->
           match uu___450_66845 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____66863 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____66925,lb::[]),uu____66927) ->
            let uu____66936 =
              let uu____66945 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____66954 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____66945, uu____66954)  in
            FStar_Pervasives_Native.Some uu____66936
        | FStar_Syntax_Syntax.Sig_let ((uu____66967,lbs),uu____66969) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____67001 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____67014 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____67014
                     then
                       let uu____67027 =
                         let uu____67036 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____67045 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____67036, uu____67045)  in
                       FStar_Pervasives_Native.Some uu____67027
                     else FStar_Pervasives_Native.None)
        | uu____67068 -> FStar_Pervasives_Native.None
  
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
          let uu____67128 =
            let uu____67137 =
              let uu____67142 =
                let uu____67143 =
                  let uu____67146 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____67146
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____67143)  in
              inst_tscheme1 uu____67142  in
            (uu____67137, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67128
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____67168,uu____67169) ->
          let uu____67174 =
            let uu____67183 =
              let uu____67188 =
                let uu____67189 =
                  let uu____67192 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____67192  in
                (us, uu____67189)  in
              inst_tscheme1 uu____67188  in
            (uu____67183, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67174
      | uu____67211 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____67300 =
          match uu____67300 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____67396,uvs,t,uu____67399,uu____67400,uu____67401);
                      FStar_Syntax_Syntax.sigrng = uu____67402;
                      FStar_Syntax_Syntax.sigquals = uu____67403;
                      FStar_Syntax_Syntax.sigmeta = uu____67404;
                      FStar_Syntax_Syntax.sigattrs = uu____67405;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67428 =
                     let uu____67437 = inst_tscheme1 (uvs, t)  in
                     (uu____67437, rng)  in
                   FStar_Pervasives_Native.Some uu____67428
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____67461;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____67463;
                      FStar_Syntax_Syntax.sigattrs = uu____67464;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67481 =
                     let uu____67483 = in_cur_mod env l  in uu____67483 = Yes
                      in
                   if uu____67481
                   then
                     let uu____67495 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____67495
                      then
                        let uu____67511 =
                          let uu____67520 = inst_tscheme1 (uvs, t)  in
                          (uu____67520, rng)  in
                        FStar_Pervasives_Native.Some uu____67511
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____67553 =
                        let uu____67562 = inst_tscheme1 (uvs, t)  in
                        (uu____67562, rng)  in
                      FStar_Pervasives_Native.Some uu____67553)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67587,uu____67588);
                      FStar_Syntax_Syntax.sigrng = uu____67589;
                      FStar_Syntax_Syntax.sigquals = uu____67590;
                      FStar_Syntax_Syntax.sigmeta = uu____67591;
                      FStar_Syntax_Syntax.sigattrs = uu____67592;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____67633 =
                          let uu____67642 = inst_tscheme1 (uvs, k)  in
                          (uu____67642, rng)  in
                        FStar_Pervasives_Native.Some uu____67633
                    | uu____67663 ->
                        let uu____67664 =
                          let uu____67673 =
                            let uu____67678 =
                              let uu____67679 =
                                let uu____67682 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67682
                                 in
                              (uvs, uu____67679)  in
                            inst_tscheme1 uu____67678  in
                          (uu____67673, rng)  in
                        FStar_Pervasives_Native.Some uu____67664)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67705,uu____67706);
                      FStar_Syntax_Syntax.sigrng = uu____67707;
                      FStar_Syntax_Syntax.sigquals = uu____67708;
                      FStar_Syntax_Syntax.sigmeta = uu____67709;
                      FStar_Syntax_Syntax.sigattrs = uu____67710;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____67752 =
                          let uu____67761 = inst_tscheme_with (uvs, k) us  in
                          (uu____67761, rng)  in
                        FStar_Pervasives_Native.Some uu____67752
                    | uu____67782 ->
                        let uu____67783 =
                          let uu____67792 =
                            let uu____67797 =
                              let uu____67798 =
                                let uu____67801 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67801
                                 in
                              (uvs, uu____67798)  in
                            inst_tscheme_with uu____67797 us  in
                          (uu____67792, rng)  in
                        FStar_Pervasives_Native.Some uu____67783)
               | FStar_Util.Inr se ->
                   let uu____67837 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____67858;
                          FStar_Syntax_Syntax.sigrng = uu____67859;
                          FStar_Syntax_Syntax.sigquals = uu____67860;
                          FStar_Syntax_Syntax.sigmeta = uu____67861;
                          FStar_Syntax_Syntax.sigattrs = uu____67862;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____67877 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____67837
                     (FStar_Util.map_option
                        (fun uu____67925  ->
                           match uu____67925 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____67956 =
          let uu____67967 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____67967 mapper  in
        match uu____67956 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____68041 =
              let uu____68052 =
                let uu____68059 =
                  let uu___1290_68062 = t  in
                  let uu____68063 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_68062.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____68063;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_68062.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____68059)  in
              (uu____68052, r)  in
            FStar_Pervasives_Native.Some uu____68041
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____68112 = lookup_qname env l  in
      match uu____68112 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____68133 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____68187 = try_lookup_bv env bv  in
      match uu____68187 with
      | FStar_Pervasives_Native.None  ->
          let uu____68202 = variable_not_found bv  in
          FStar_Errors.raise_error uu____68202 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____68218 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____68219 =
            let uu____68220 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____68220  in
          (uu____68218, uu____68219)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____68242 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____68242 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____68308 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____68308  in
          let uu____68309 =
            let uu____68318 =
              let uu____68323 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____68323)  in
            (uu____68318, r1)  in
          FStar_Pervasives_Native.Some uu____68309
  
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
        let uu____68358 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____68358 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____68391,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____68416 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____68416  in
            let uu____68417 =
              let uu____68422 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____68422, r1)  in
            FStar_Pervasives_Native.Some uu____68417
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____68446 = try_lookup_lid env l  in
      match uu____68446 with
      | FStar_Pervasives_Native.None  ->
          let uu____68473 = name_not_found l  in
          let uu____68479 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____68473 uu____68479
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_68522  ->
              match uu___451_68522 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____68526 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____68547 = lookup_qname env lid  in
      match uu____68547 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68556,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68559;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____68561;
              FStar_Syntax_Syntax.sigattrs = uu____68562;_},FStar_Pervasives_Native.None
            ),uu____68563)
          ->
          let uu____68612 =
            let uu____68619 =
              let uu____68620 =
                let uu____68623 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____68623 t  in
              (uvs, uu____68620)  in
            (uu____68619, q)  in
          FStar_Pervasives_Native.Some uu____68612
      | uu____68636 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68658 = lookup_qname env lid  in
      match uu____68658 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68663,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68666;
              FStar_Syntax_Syntax.sigquals = uu____68667;
              FStar_Syntax_Syntax.sigmeta = uu____68668;
              FStar_Syntax_Syntax.sigattrs = uu____68669;_},FStar_Pervasives_Native.None
            ),uu____68670)
          ->
          let uu____68719 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68719 (uvs, t)
      | uu____68724 ->
          let uu____68725 = name_not_found lid  in
          let uu____68731 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68725 uu____68731
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68751 = lookup_qname env lid  in
      match uu____68751 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68756,uvs,t,uu____68759,uu____68760,uu____68761);
              FStar_Syntax_Syntax.sigrng = uu____68762;
              FStar_Syntax_Syntax.sigquals = uu____68763;
              FStar_Syntax_Syntax.sigmeta = uu____68764;
              FStar_Syntax_Syntax.sigattrs = uu____68765;_},FStar_Pervasives_Native.None
            ),uu____68766)
          ->
          let uu____68821 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68821 (uvs, t)
      | uu____68826 ->
          let uu____68827 = name_not_found lid  in
          let uu____68833 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68827 uu____68833
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____68856 = lookup_qname env lid  in
      match uu____68856 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____68864,uu____68865,uu____68866,uu____68867,uu____68868,dcs);
              FStar_Syntax_Syntax.sigrng = uu____68870;
              FStar_Syntax_Syntax.sigquals = uu____68871;
              FStar_Syntax_Syntax.sigmeta = uu____68872;
              FStar_Syntax_Syntax.sigattrs = uu____68873;_},uu____68874),uu____68875)
          -> (true, dcs)
      | uu____68938 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____68954 = lookup_qname env lid  in
      match uu____68954 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68955,uu____68956,uu____68957,l,uu____68959,uu____68960);
              FStar_Syntax_Syntax.sigrng = uu____68961;
              FStar_Syntax_Syntax.sigquals = uu____68962;
              FStar_Syntax_Syntax.sigmeta = uu____68963;
              FStar_Syntax_Syntax.sigattrs = uu____68964;_},uu____68965),uu____68966)
          -> l
      | uu____69023 ->
          let uu____69024 =
            let uu____69026 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____69026  in
          failwith uu____69024
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69096)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69153) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69177 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69177
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69212 -> FStar_Pervasives_Native.None)
          | uu____69221 -> FStar_Pervasives_Native.None
  
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
        let uu____69283 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____69283
  
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
        let uu____69316 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____69316
  
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
             (FStar_Util.Inl uu____69368,uu____69369) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____69418),uu____69419) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____69468 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____69486 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____69496 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____69513 ->
                  let uu____69520 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____69520
              | FStar_Syntax_Syntax.Sig_let ((uu____69521,lbs),uu____69523)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____69539 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____69539
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____69546 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____69554 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____69555 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____69562 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69563 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____69564 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69565 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____69578 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____69596 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____69596
           (fun d_opt  ->
              let uu____69609 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____69609
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____69619 =
                   let uu____69622 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____69622  in
                 match uu____69619 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____69623 =
                       let uu____69625 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____69625
                        in
                     failwith uu____69623
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____69630 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____69630
                       then
                         let uu____69633 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____69635 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____69637 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____69633 uu____69635 uu____69637
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
        (FStar_Util.Inr (se,uu____69662),uu____69663) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____69712 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____69734),uu____69735) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____69784 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____69806 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____69806
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____69829 = lookup_attrs_of_lid env fv_lid1  in
        match uu____69829 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____69853 =
                      let uu____69854 = FStar_Syntax_Util.un_uinst tm  in
                      uu____69854.FStar_Syntax_Syntax.n  in
                    match uu____69853 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____69859 -> false))
  
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
      let uu____69893 = lookup_qname env ftv  in
      match uu____69893 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69897) ->
          let uu____69942 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____69942 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____69963,t),r) ->
               let uu____69978 =
                 let uu____69979 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____69979 t  in
               FStar_Pervasives_Native.Some uu____69978)
      | uu____69980 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____69992 = try_lookup_effect_lid env ftv  in
      match uu____69992 with
      | FStar_Pervasives_Native.None  ->
          let uu____69995 = name_not_found ftv  in
          let uu____70001 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____69995 uu____70001
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
        let uu____70025 = lookup_qname env lid0  in
        match uu____70025 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____70036);
                FStar_Syntax_Syntax.sigrng = uu____70037;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____70039;
                FStar_Syntax_Syntax.sigattrs = uu____70040;_},FStar_Pervasives_Native.None
              ),uu____70041)
            ->
            let lid1 =
              let uu____70095 =
                let uu____70096 = FStar_Ident.range_of_lid lid  in
                let uu____70097 =
                  let uu____70098 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____70098  in
                FStar_Range.set_use_range uu____70096 uu____70097  in
              FStar_Ident.set_lid_range lid uu____70095  in
            let uu____70099 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_70105  ->
                      match uu___452_70105 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____70108 -> false))
               in
            if uu____70099
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____70127 =
                      let uu____70129 =
                        let uu____70131 = get_range env  in
                        FStar_Range.string_of_range uu____70131  in
                      let uu____70132 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____70134 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____70129 uu____70132 uu____70134
                       in
                    failwith uu____70127)
                  in
               match (binders, univs1) with
               | ([],uu____70155) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____70181,uu____70182::uu____70183::uu____70184) ->
                   let uu____70205 =
                     let uu____70207 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____70209 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____70207 uu____70209
                      in
                   failwith uu____70205
               | uu____70220 ->
                   let uu____70235 =
                     let uu____70240 =
                       let uu____70241 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____70241)  in
                     inst_tscheme_with uu____70240 insts  in
                   (match uu____70235 with
                    | (uu____70254,t) ->
                        let t1 =
                          let uu____70257 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____70257 t  in
                        let uu____70258 =
                          let uu____70259 = FStar_Syntax_Subst.compress t1
                             in
                          uu____70259.FStar_Syntax_Syntax.n  in
                        (match uu____70258 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____70294 -> failwith "Impossible")))
        | uu____70302 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____70326 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____70326 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____70339,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____70346 = find1 l2  in
            (match uu____70346 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____70353 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____70353 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____70357 = find1 l  in
            (match uu____70357 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____70362 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____70362
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____70377 = lookup_qname env l1  in
      match uu____70377 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____70380;
              FStar_Syntax_Syntax.sigrng = uu____70381;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____70383;
              FStar_Syntax_Syntax.sigattrs = uu____70384;_},uu____70385),uu____70386)
          -> q
      | uu____70437 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____70461 =
          let uu____70462 =
            let uu____70464 = FStar_Util.string_of_int i  in
            let uu____70466 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____70464 uu____70466
             in
          failwith uu____70462  in
        let uu____70469 = lookup_datacon env lid  in
        match uu____70469 with
        | (uu____70474,t) ->
            let uu____70476 =
              let uu____70477 = FStar_Syntax_Subst.compress t  in
              uu____70477.FStar_Syntax_Syntax.n  in
            (match uu____70476 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70481) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____70525 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____70525
                      FStar_Pervasives_Native.fst)
             | uu____70536 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70550 = lookup_qname env l  in
      match uu____70550 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____70552,uu____70553,uu____70554);
              FStar_Syntax_Syntax.sigrng = uu____70555;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70557;
              FStar_Syntax_Syntax.sigattrs = uu____70558;_},uu____70559),uu____70560)
          ->
          FStar_Util.for_some
            (fun uu___453_70613  ->
               match uu___453_70613 with
               | FStar_Syntax_Syntax.Projector uu____70615 -> true
               | uu____70621 -> false) quals
      | uu____70623 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70637 = lookup_qname env lid  in
      match uu____70637 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____70639,uu____70640,uu____70641,uu____70642,uu____70643,uu____70644);
              FStar_Syntax_Syntax.sigrng = uu____70645;
              FStar_Syntax_Syntax.sigquals = uu____70646;
              FStar_Syntax_Syntax.sigmeta = uu____70647;
              FStar_Syntax_Syntax.sigattrs = uu____70648;_},uu____70649),uu____70650)
          -> true
      | uu____70708 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70722 = lookup_qname env lid  in
      match uu____70722 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____70724,uu____70725,uu____70726,uu____70727,uu____70728,uu____70729);
              FStar_Syntax_Syntax.sigrng = uu____70730;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70732;
              FStar_Syntax_Syntax.sigattrs = uu____70733;_},uu____70734),uu____70735)
          ->
          FStar_Util.for_some
            (fun uu___454_70796  ->
               match uu___454_70796 with
               | FStar_Syntax_Syntax.RecordType uu____70798 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____70808 -> true
               | uu____70818 -> false) quals
      | uu____70820 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____70830,uu____70831);
            FStar_Syntax_Syntax.sigrng = uu____70832;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____70834;
            FStar_Syntax_Syntax.sigattrs = uu____70835;_},uu____70836),uu____70837)
        ->
        FStar_Util.for_some
          (fun uu___455_70894  ->
             match uu___455_70894 with
             | FStar_Syntax_Syntax.Action uu____70896 -> true
             | uu____70898 -> false) quals
    | uu____70900 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70914 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____70914
  
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
      let uu____70931 =
        let uu____70932 = FStar_Syntax_Util.un_uinst head1  in
        uu____70932.FStar_Syntax_Syntax.n  in
      match uu____70931 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____70938 ->
               true
           | uu____70941 -> false)
      | uu____70943 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70957 = lookup_qname env l  in
      match uu____70957 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____70960),uu____70961) ->
          FStar_Util.for_some
            (fun uu___456_71009  ->
               match uu___456_71009 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____71012 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____71014 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____71090 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____71108) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____71126 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____71134 ->
                 FStar_Pervasives_Native.Some true
             | uu____71153 -> FStar_Pervasives_Native.Some false)
         in
      let uu____71156 =
        let uu____71160 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____71160 mapper  in
      match uu____71156 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____71220 = lookup_qname env lid  in
      match uu____71220 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71224,uu____71225,tps,uu____71227,uu____71228,uu____71229);
              FStar_Syntax_Syntax.sigrng = uu____71230;
              FStar_Syntax_Syntax.sigquals = uu____71231;
              FStar_Syntax_Syntax.sigmeta = uu____71232;
              FStar_Syntax_Syntax.sigattrs = uu____71233;_},uu____71234),uu____71235)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____71301 -> FStar_Pervasives_Native.None
  
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
           (fun uu____71347  ->
              match uu____71347 with
              | (d,uu____71356) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____71372 = effect_decl_opt env l  in
      match uu____71372 with
      | FStar_Pervasives_Native.None  ->
          let uu____71387 = name_not_found l  in
          let uu____71393 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____71387 uu____71393
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____71416  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____71435  ->
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
        let uu____71467 = FStar_Ident.lid_equals l1 l2  in
        if uu____71467
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____71478 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____71478
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____71489 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____71542  ->
                        match uu____71542 with
                        | (m1,m2,uu____71556,uu____71557,uu____71558) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____71489 with
              | FStar_Pervasives_Native.None  ->
                  let uu____71575 =
                    let uu____71581 =
                      let uu____71583 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____71585 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____71583
                        uu____71585
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____71581)
                     in
                  FStar_Errors.raise_error uu____71575 env.range
              | FStar_Pervasives_Native.Some
                  (uu____71595,uu____71596,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____71630 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____71630
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
  'Auu____71650 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____71650) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____71679 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____71705  ->
                match uu____71705 with
                | (d,uu____71712) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____71679 with
      | FStar_Pervasives_Native.None  ->
          let uu____71723 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____71723
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____71738 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____71738 with
           | (uu____71753,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____71771)::(wp,uu____71773)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____71829 -> failwith "Impossible"))
  
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
          let uu____71887 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____71887
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____71892 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____71892
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
                  let uu____71903 = get_range env  in
                  let uu____71904 =
                    let uu____71911 =
                      let uu____71912 =
                        let uu____71929 =
                          let uu____71940 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____71940]  in
                        (null_wp, uu____71929)  in
                      FStar_Syntax_Syntax.Tm_app uu____71912  in
                    FStar_Syntax_Syntax.mk uu____71911  in
                  uu____71904 FStar_Pervasives_Native.None uu____71903  in
                let uu____71977 =
                  let uu____71978 =
                    let uu____71989 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____71989]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____71978;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____71977))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_72027 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_72027.order);
              joins = (uu___1944_72027.joins)
            }  in
          let uu___1947_72036 = env  in
          {
            solver = (uu___1947_72036.solver);
            range = (uu___1947_72036.range);
            curmodule = (uu___1947_72036.curmodule);
            gamma = (uu___1947_72036.gamma);
            gamma_sig = (uu___1947_72036.gamma_sig);
            gamma_cache = (uu___1947_72036.gamma_cache);
            modules = (uu___1947_72036.modules);
            expected_typ = (uu___1947_72036.expected_typ);
            sigtab = (uu___1947_72036.sigtab);
            attrtab = (uu___1947_72036.attrtab);
            is_pattern = (uu___1947_72036.is_pattern);
            instantiate_imp = (uu___1947_72036.instantiate_imp);
            effects;
            generalize = (uu___1947_72036.generalize);
            letrecs = (uu___1947_72036.letrecs);
            top_level = (uu___1947_72036.top_level);
            check_uvars = (uu___1947_72036.check_uvars);
            use_eq = (uu___1947_72036.use_eq);
            is_iface = (uu___1947_72036.is_iface);
            admit = (uu___1947_72036.admit);
            lax = (uu___1947_72036.lax);
            lax_universes = (uu___1947_72036.lax_universes);
            phase1 = (uu___1947_72036.phase1);
            failhard = (uu___1947_72036.failhard);
            nosynth = (uu___1947_72036.nosynth);
            uvar_subtyping = (uu___1947_72036.uvar_subtyping);
            tc_term = (uu___1947_72036.tc_term);
            type_of = (uu___1947_72036.type_of);
            universe_of = (uu___1947_72036.universe_of);
            check_type_of = (uu___1947_72036.check_type_of);
            use_bv_sorts = (uu___1947_72036.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_72036.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_72036.normalized_eff_names);
            fv_delta_depths = (uu___1947_72036.fv_delta_depths);
            proof_ns = (uu___1947_72036.proof_ns);
            synth_hook = (uu___1947_72036.synth_hook);
            splice = (uu___1947_72036.splice);
            postprocess = (uu___1947_72036.postprocess);
            is_native_tactic = (uu___1947_72036.is_native_tactic);
            identifier_info = (uu___1947_72036.identifier_info);
            tc_hooks = (uu___1947_72036.tc_hooks);
            dsenv = (uu___1947_72036.dsenv);
            nbe = (uu___1947_72036.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____72066 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____72066  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____72224 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____72225 = l1 u t wp e  in
                                l2 u t uu____72224 uu____72225))
                | uu____72226 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____72298 = inst_tscheme_with lift_t [u]  in
            match uu____72298 with
            | (uu____72305,lift_t1) ->
                let uu____72307 =
                  let uu____72314 =
                    let uu____72315 =
                      let uu____72332 =
                        let uu____72343 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72352 =
                          let uu____72363 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____72363]  in
                        uu____72343 :: uu____72352  in
                      (lift_t1, uu____72332)  in
                    FStar_Syntax_Syntax.Tm_app uu____72315  in
                  FStar_Syntax_Syntax.mk uu____72314  in
                uu____72307 FStar_Pervasives_Native.None
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
            let uu____72473 = inst_tscheme_with lift_t [u]  in
            match uu____72473 with
            | (uu____72480,lift_t1) ->
                let uu____72482 =
                  let uu____72489 =
                    let uu____72490 =
                      let uu____72507 =
                        let uu____72518 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72527 =
                          let uu____72538 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____72547 =
                            let uu____72558 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____72558]  in
                          uu____72538 :: uu____72547  in
                        uu____72518 :: uu____72527  in
                      (lift_t1, uu____72507)  in
                    FStar_Syntax_Syntax.Tm_app uu____72490  in
                  FStar_Syntax_Syntax.mk uu____72489  in
                uu____72482 FStar_Pervasives_Native.None
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
              let uu____72660 =
                let uu____72661 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____72661
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____72660  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____72670 =
              let uu____72672 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____72672  in
            let uu____72673 =
              let uu____72675 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____72703 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____72703)
                 in
              FStar_Util.dflt "none" uu____72675  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____72670
              uu____72673
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____72732  ->
                    match uu____72732 with
                    | (e,uu____72740) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____72763 =
            match uu____72763 with
            | (i,j) ->
                let uu____72774 = FStar_Ident.lid_equals i j  in
                if uu____72774
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _72781  -> FStar_Pervasives_Native.Some _72781)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____72810 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____72820 = FStar_Ident.lid_equals i k  in
                        if uu____72820
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____72834 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____72834
                                  then []
                                  else
                                    (let uu____72841 =
                                       let uu____72850 =
                                         find_edge order1 (i, k)  in
                                       let uu____72853 =
                                         find_edge order1 (k, j)  in
                                       (uu____72850, uu____72853)  in
                                     match uu____72841 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____72868 =
                                           compose_edges e1 e2  in
                                         [uu____72868]
                                     | uu____72869 -> [])))))
                 in
              FStar_List.append order1 uu____72810  in
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
                   let uu____72899 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____72902 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____72902
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____72899
                   then
                     let uu____72909 =
                       let uu____72915 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____72915)
                        in
                     let uu____72919 = get_range env  in
                     FStar_Errors.raise_error uu____72909 uu____72919
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____72997 = FStar_Ident.lid_equals i j
                                   in
                                if uu____72997
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____73049 =
                                              let uu____73058 =
                                                find_edge order2 (i, k)  in
                                              let uu____73061 =
                                                find_edge order2 (j, k)  in
                                              (uu____73058, uu____73061)  in
                                            match uu____73049 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____73103,uu____73104)
                                                     ->
                                                     let uu____73111 =
                                                       let uu____73118 =
                                                         let uu____73120 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73120
                                                          in
                                                       let uu____73123 =
                                                         let uu____73125 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73125
                                                          in
                                                       (uu____73118,
                                                         uu____73123)
                                                        in
                                                     (match uu____73111 with
                                                      | (true ,true ) ->
                                                          let uu____73142 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____73142
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
                                            | uu____73185 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_73258 = env.effects  in
              { decls = (uu___2074_73258.decls); order = order2; joins }  in
            let uu___2077_73259 = env  in
            {
              solver = (uu___2077_73259.solver);
              range = (uu___2077_73259.range);
              curmodule = (uu___2077_73259.curmodule);
              gamma = (uu___2077_73259.gamma);
              gamma_sig = (uu___2077_73259.gamma_sig);
              gamma_cache = (uu___2077_73259.gamma_cache);
              modules = (uu___2077_73259.modules);
              expected_typ = (uu___2077_73259.expected_typ);
              sigtab = (uu___2077_73259.sigtab);
              attrtab = (uu___2077_73259.attrtab);
              is_pattern = (uu___2077_73259.is_pattern);
              instantiate_imp = (uu___2077_73259.instantiate_imp);
              effects;
              generalize = (uu___2077_73259.generalize);
              letrecs = (uu___2077_73259.letrecs);
              top_level = (uu___2077_73259.top_level);
              check_uvars = (uu___2077_73259.check_uvars);
              use_eq = (uu___2077_73259.use_eq);
              is_iface = (uu___2077_73259.is_iface);
              admit = (uu___2077_73259.admit);
              lax = (uu___2077_73259.lax);
              lax_universes = (uu___2077_73259.lax_universes);
              phase1 = (uu___2077_73259.phase1);
              failhard = (uu___2077_73259.failhard);
              nosynth = (uu___2077_73259.nosynth);
              uvar_subtyping = (uu___2077_73259.uvar_subtyping);
              tc_term = (uu___2077_73259.tc_term);
              type_of = (uu___2077_73259.type_of);
              universe_of = (uu___2077_73259.universe_of);
              check_type_of = (uu___2077_73259.check_type_of);
              use_bv_sorts = (uu___2077_73259.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_73259.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_73259.normalized_eff_names);
              fv_delta_depths = (uu___2077_73259.fv_delta_depths);
              proof_ns = (uu___2077_73259.proof_ns);
              synth_hook = (uu___2077_73259.synth_hook);
              splice = (uu___2077_73259.splice);
              postprocess = (uu___2077_73259.postprocess);
              is_native_tactic = (uu___2077_73259.is_native_tactic);
              identifier_info = (uu___2077_73259.identifier_info);
              tc_hooks = (uu___2077_73259.tc_hooks);
              dsenv = (uu___2077_73259.dsenv);
              nbe = (uu___2077_73259.nbe)
            }))
      | uu____73260 -> env
  
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
        | uu____73289 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____73302 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____73302 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____73319 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____73319 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____73344 =
                     let uu____73350 =
                       let uu____73352 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____73360 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____73371 =
                         let uu____73373 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____73373  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____73352 uu____73360 uu____73371
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____73350)
                      in
                   FStar_Errors.raise_error uu____73344
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____73381 =
                     let uu____73392 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____73392 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____73429  ->
                        fun uu____73430  ->
                          match (uu____73429, uu____73430) with
                          | ((x,uu____73460),(t,uu____73462)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____73381
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____73493 =
                     let uu___2115_73494 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_73494.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_73494.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_73494.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_73494.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____73493
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____73506 .
    'Auu____73506 ->
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
          let uu____73536 = effect_decl_opt env effect_name  in
          match uu____73536 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____73575 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____73598 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____73637 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____73637
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____73642 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____73642
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____73657 =
                     let uu____73660 = get_range env  in
                     let uu____73661 =
                       let uu____73668 =
                         let uu____73669 =
                           let uu____73686 =
                             let uu____73697 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____73697; wp]  in
                           (repr, uu____73686)  in
                         FStar_Syntax_Syntax.Tm_app uu____73669  in
                       FStar_Syntax_Syntax.mk uu____73668  in
                     uu____73661 FStar_Pervasives_Native.None uu____73660  in
                   FStar_Pervasives_Native.Some uu____73657)
  
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
      | uu____73841 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____73856 =
        let uu____73857 = FStar_Syntax_Subst.compress t  in
        uu____73857.FStar_Syntax_Syntax.n  in
      match uu____73856 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____73861,c) ->
          is_reifiable_comp env c
      | uu____73883 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____73903 =
           let uu____73905 = is_reifiable_effect env l  in
           Prims.op_Negation uu____73905  in
         if uu____73903
         then
           let uu____73908 =
             let uu____73914 =
               let uu____73916 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____73916
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____73914)  in
           let uu____73920 = get_range env  in
           FStar_Errors.raise_error uu____73908 uu____73920
         else ());
        (let uu____73923 = effect_repr_aux true env c u_c  in
         match uu____73923 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_73959 = env  in
        {
          solver = (uu___2180_73959.solver);
          range = (uu___2180_73959.range);
          curmodule = (uu___2180_73959.curmodule);
          gamma = (uu___2180_73959.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_73959.gamma_cache);
          modules = (uu___2180_73959.modules);
          expected_typ = (uu___2180_73959.expected_typ);
          sigtab = (uu___2180_73959.sigtab);
          attrtab = (uu___2180_73959.attrtab);
          is_pattern = (uu___2180_73959.is_pattern);
          instantiate_imp = (uu___2180_73959.instantiate_imp);
          effects = (uu___2180_73959.effects);
          generalize = (uu___2180_73959.generalize);
          letrecs = (uu___2180_73959.letrecs);
          top_level = (uu___2180_73959.top_level);
          check_uvars = (uu___2180_73959.check_uvars);
          use_eq = (uu___2180_73959.use_eq);
          is_iface = (uu___2180_73959.is_iface);
          admit = (uu___2180_73959.admit);
          lax = (uu___2180_73959.lax);
          lax_universes = (uu___2180_73959.lax_universes);
          phase1 = (uu___2180_73959.phase1);
          failhard = (uu___2180_73959.failhard);
          nosynth = (uu___2180_73959.nosynth);
          uvar_subtyping = (uu___2180_73959.uvar_subtyping);
          tc_term = (uu___2180_73959.tc_term);
          type_of = (uu___2180_73959.type_of);
          universe_of = (uu___2180_73959.universe_of);
          check_type_of = (uu___2180_73959.check_type_of);
          use_bv_sorts = (uu___2180_73959.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_73959.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_73959.normalized_eff_names);
          fv_delta_depths = (uu___2180_73959.fv_delta_depths);
          proof_ns = (uu___2180_73959.proof_ns);
          synth_hook = (uu___2180_73959.synth_hook);
          splice = (uu___2180_73959.splice);
          postprocess = (uu___2180_73959.postprocess);
          is_native_tactic = (uu___2180_73959.is_native_tactic);
          identifier_info = (uu___2180_73959.identifier_info);
          tc_hooks = (uu___2180_73959.tc_hooks);
          dsenv = (uu___2180_73959.dsenv);
          nbe = (uu___2180_73959.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_73973 = env  in
      {
        solver = (uu___2187_73973.solver);
        range = (uu___2187_73973.range);
        curmodule = (uu___2187_73973.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_73973.gamma_sig);
        gamma_cache = (uu___2187_73973.gamma_cache);
        modules = (uu___2187_73973.modules);
        expected_typ = (uu___2187_73973.expected_typ);
        sigtab = (uu___2187_73973.sigtab);
        attrtab = (uu___2187_73973.attrtab);
        is_pattern = (uu___2187_73973.is_pattern);
        instantiate_imp = (uu___2187_73973.instantiate_imp);
        effects = (uu___2187_73973.effects);
        generalize = (uu___2187_73973.generalize);
        letrecs = (uu___2187_73973.letrecs);
        top_level = (uu___2187_73973.top_level);
        check_uvars = (uu___2187_73973.check_uvars);
        use_eq = (uu___2187_73973.use_eq);
        is_iface = (uu___2187_73973.is_iface);
        admit = (uu___2187_73973.admit);
        lax = (uu___2187_73973.lax);
        lax_universes = (uu___2187_73973.lax_universes);
        phase1 = (uu___2187_73973.phase1);
        failhard = (uu___2187_73973.failhard);
        nosynth = (uu___2187_73973.nosynth);
        uvar_subtyping = (uu___2187_73973.uvar_subtyping);
        tc_term = (uu___2187_73973.tc_term);
        type_of = (uu___2187_73973.type_of);
        universe_of = (uu___2187_73973.universe_of);
        check_type_of = (uu___2187_73973.check_type_of);
        use_bv_sorts = (uu___2187_73973.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_73973.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_73973.normalized_eff_names);
        fv_delta_depths = (uu___2187_73973.fv_delta_depths);
        proof_ns = (uu___2187_73973.proof_ns);
        synth_hook = (uu___2187_73973.synth_hook);
        splice = (uu___2187_73973.splice);
        postprocess = (uu___2187_73973.postprocess);
        is_native_tactic = (uu___2187_73973.is_native_tactic);
        identifier_info = (uu___2187_73973.identifier_info);
        tc_hooks = (uu___2187_73973.tc_hooks);
        dsenv = (uu___2187_73973.dsenv);
        nbe = (uu___2187_73973.nbe)
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
            (let uu___2200_74031 = env  in
             {
               solver = (uu___2200_74031.solver);
               range = (uu___2200_74031.range);
               curmodule = (uu___2200_74031.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_74031.gamma_sig);
               gamma_cache = (uu___2200_74031.gamma_cache);
               modules = (uu___2200_74031.modules);
               expected_typ = (uu___2200_74031.expected_typ);
               sigtab = (uu___2200_74031.sigtab);
               attrtab = (uu___2200_74031.attrtab);
               is_pattern = (uu___2200_74031.is_pattern);
               instantiate_imp = (uu___2200_74031.instantiate_imp);
               effects = (uu___2200_74031.effects);
               generalize = (uu___2200_74031.generalize);
               letrecs = (uu___2200_74031.letrecs);
               top_level = (uu___2200_74031.top_level);
               check_uvars = (uu___2200_74031.check_uvars);
               use_eq = (uu___2200_74031.use_eq);
               is_iface = (uu___2200_74031.is_iface);
               admit = (uu___2200_74031.admit);
               lax = (uu___2200_74031.lax);
               lax_universes = (uu___2200_74031.lax_universes);
               phase1 = (uu___2200_74031.phase1);
               failhard = (uu___2200_74031.failhard);
               nosynth = (uu___2200_74031.nosynth);
               uvar_subtyping = (uu___2200_74031.uvar_subtyping);
               tc_term = (uu___2200_74031.tc_term);
               type_of = (uu___2200_74031.type_of);
               universe_of = (uu___2200_74031.universe_of);
               check_type_of = (uu___2200_74031.check_type_of);
               use_bv_sorts = (uu___2200_74031.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_74031.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_74031.normalized_eff_names);
               fv_delta_depths = (uu___2200_74031.fv_delta_depths);
               proof_ns = (uu___2200_74031.proof_ns);
               synth_hook = (uu___2200_74031.synth_hook);
               splice = (uu___2200_74031.splice);
               postprocess = (uu___2200_74031.postprocess);
               is_native_tactic = (uu___2200_74031.is_native_tactic);
               identifier_info = (uu___2200_74031.identifier_info);
               tc_hooks = (uu___2200_74031.tc_hooks);
               dsenv = (uu___2200_74031.dsenv);
               nbe = (uu___2200_74031.nbe)
             }))
    | uu____74032 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____74061  ->
             match uu____74061 with | (x,uu____74069) -> push_bv env1 x) env
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
            let uu___2214_74104 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_74104.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_74104.FStar_Syntax_Syntax.index);
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
      (let uu___2225_74146 = env  in
       {
         solver = (uu___2225_74146.solver);
         range = (uu___2225_74146.range);
         curmodule = (uu___2225_74146.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_74146.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_74146.sigtab);
         attrtab = (uu___2225_74146.attrtab);
         is_pattern = (uu___2225_74146.is_pattern);
         instantiate_imp = (uu___2225_74146.instantiate_imp);
         effects = (uu___2225_74146.effects);
         generalize = (uu___2225_74146.generalize);
         letrecs = (uu___2225_74146.letrecs);
         top_level = (uu___2225_74146.top_level);
         check_uvars = (uu___2225_74146.check_uvars);
         use_eq = (uu___2225_74146.use_eq);
         is_iface = (uu___2225_74146.is_iface);
         admit = (uu___2225_74146.admit);
         lax = (uu___2225_74146.lax);
         lax_universes = (uu___2225_74146.lax_universes);
         phase1 = (uu___2225_74146.phase1);
         failhard = (uu___2225_74146.failhard);
         nosynth = (uu___2225_74146.nosynth);
         uvar_subtyping = (uu___2225_74146.uvar_subtyping);
         tc_term = (uu___2225_74146.tc_term);
         type_of = (uu___2225_74146.type_of);
         universe_of = (uu___2225_74146.universe_of);
         check_type_of = (uu___2225_74146.check_type_of);
         use_bv_sorts = (uu___2225_74146.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_74146.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_74146.normalized_eff_names);
         fv_delta_depths = (uu___2225_74146.fv_delta_depths);
         proof_ns = (uu___2225_74146.proof_ns);
         synth_hook = (uu___2225_74146.synth_hook);
         splice = (uu___2225_74146.splice);
         postprocess = (uu___2225_74146.postprocess);
         is_native_tactic = (uu___2225_74146.is_native_tactic);
         identifier_info = (uu___2225_74146.identifier_info);
         tc_hooks = (uu___2225_74146.tc_hooks);
         dsenv = (uu___2225_74146.dsenv);
         nbe = (uu___2225_74146.nbe)
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
        let uu____74190 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____74190 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____74218 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____74218)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_74234 = env  in
      {
        solver = (uu___2240_74234.solver);
        range = (uu___2240_74234.range);
        curmodule = (uu___2240_74234.curmodule);
        gamma = (uu___2240_74234.gamma);
        gamma_sig = (uu___2240_74234.gamma_sig);
        gamma_cache = (uu___2240_74234.gamma_cache);
        modules = (uu___2240_74234.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_74234.sigtab);
        attrtab = (uu___2240_74234.attrtab);
        is_pattern = (uu___2240_74234.is_pattern);
        instantiate_imp = (uu___2240_74234.instantiate_imp);
        effects = (uu___2240_74234.effects);
        generalize = (uu___2240_74234.generalize);
        letrecs = (uu___2240_74234.letrecs);
        top_level = (uu___2240_74234.top_level);
        check_uvars = (uu___2240_74234.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_74234.is_iface);
        admit = (uu___2240_74234.admit);
        lax = (uu___2240_74234.lax);
        lax_universes = (uu___2240_74234.lax_universes);
        phase1 = (uu___2240_74234.phase1);
        failhard = (uu___2240_74234.failhard);
        nosynth = (uu___2240_74234.nosynth);
        uvar_subtyping = (uu___2240_74234.uvar_subtyping);
        tc_term = (uu___2240_74234.tc_term);
        type_of = (uu___2240_74234.type_of);
        universe_of = (uu___2240_74234.universe_of);
        check_type_of = (uu___2240_74234.check_type_of);
        use_bv_sorts = (uu___2240_74234.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_74234.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_74234.normalized_eff_names);
        fv_delta_depths = (uu___2240_74234.fv_delta_depths);
        proof_ns = (uu___2240_74234.proof_ns);
        synth_hook = (uu___2240_74234.synth_hook);
        splice = (uu___2240_74234.splice);
        postprocess = (uu___2240_74234.postprocess);
        is_native_tactic = (uu___2240_74234.is_native_tactic);
        identifier_info = (uu___2240_74234.identifier_info);
        tc_hooks = (uu___2240_74234.tc_hooks);
        dsenv = (uu___2240_74234.dsenv);
        nbe = (uu___2240_74234.nbe)
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
    let uu____74265 = expected_typ env_  in
    ((let uu___2247_74271 = env_  in
      {
        solver = (uu___2247_74271.solver);
        range = (uu___2247_74271.range);
        curmodule = (uu___2247_74271.curmodule);
        gamma = (uu___2247_74271.gamma);
        gamma_sig = (uu___2247_74271.gamma_sig);
        gamma_cache = (uu___2247_74271.gamma_cache);
        modules = (uu___2247_74271.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_74271.sigtab);
        attrtab = (uu___2247_74271.attrtab);
        is_pattern = (uu___2247_74271.is_pattern);
        instantiate_imp = (uu___2247_74271.instantiate_imp);
        effects = (uu___2247_74271.effects);
        generalize = (uu___2247_74271.generalize);
        letrecs = (uu___2247_74271.letrecs);
        top_level = (uu___2247_74271.top_level);
        check_uvars = (uu___2247_74271.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_74271.is_iface);
        admit = (uu___2247_74271.admit);
        lax = (uu___2247_74271.lax);
        lax_universes = (uu___2247_74271.lax_universes);
        phase1 = (uu___2247_74271.phase1);
        failhard = (uu___2247_74271.failhard);
        nosynth = (uu___2247_74271.nosynth);
        uvar_subtyping = (uu___2247_74271.uvar_subtyping);
        tc_term = (uu___2247_74271.tc_term);
        type_of = (uu___2247_74271.type_of);
        universe_of = (uu___2247_74271.universe_of);
        check_type_of = (uu___2247_74271.check_type_of);
        use_bv_sorts = (uu___2247_74271.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_74271.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_74271.normalized_eff_names);
        fv_delta_depths = (uu___2247_74271.fv_delta_depths);
        proof_ns = (uu___2247_74271.proof_ns);
        synth_hook = (uu___2247_74271.synth_hook);
        splice = (uu___2247_74271.splice);
        postprocess = (uu___2247_74271.postprocess);
        is_native_tactic = (uu___2247_74271.is_native_tactic);
        identifier_info = (uu___2247_74271.identifier_info);
        tc_hooks = (uu___2247_74271.tc_hooks);
        dsenv = (uu___2247_74271.dsenv);
        nbe = (uu___2247_74271.nbe)
      }), uu____74265)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____74283 =
      let uu____74286 = FStar_Ident.id_of_text ""  in [uu____74286]  in
    FStar_Ident.lid_of_ids uu____74283  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____74293 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____74293
        then
          let uu____74298 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____74298 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_74326 = env  in
       {
         solver = (uu___2255_74326.solver);
         range = (uu___2255_74326.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_74326.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_74326.expected_typ);
         sigtab = (uu___2255_74326.sigtab);
         attrtab = (uu___2255_74326.attrtab);
         is_pattern = (uu___2255_74326.is_pattern);
         instantiate_imp = (uu___2255_74326.instantiate_imp);
         effects = (uu___2255_74326.effects);
         generalize = (uu___2255_74326.generalize);
         letrecs = (uu___2255_74326.letrecs);
         top_level = (uu___2255_74326.top_level);
         check_uvars = (uu___2255_74326.check_uvars);
         use_eq = (uu___2255_74326.use_eq);
         is_iface = (uu___2255_74326.is_iface);
         admit = (uu___2255_74326.admit);
         lax = (uu___2255_74326.lax);
         lax_universes = (uu___2255_74326.lax_universes);
         phase1 = (uu___2255_74326.phase1);
         failhard = (uu___2255_74326.failhard);
         nosynth = (uu___2255_74326.nosynth);
         uvar_subtyping = (uu___2255_74326.uvar_subtyping);
         tc_term = (uu___2255_74326.tc_term);
         type_of = (uu___2255_74326.type_of);
         universe_of = (uu___2255_74326.universe_of);
         check_type_of = (uu___2255_74326.check_type_of);
         use_bv_sorts = (uu___2255_74326.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_74326.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_74326.normalized_eff_names);
         fv_delta_depths = (uu___2255_74326.fv_delta_depths);
         proof_ns = (uu___2255_74326.proof_ns);
         synth_hook = (uu___2255_74326.synth_hook);
         splice = (uu___2255_74326.splice);
         postprocess = (uu___2255_74326.postprocess);
         is_native_tactic = (uu___2255_74326.is_native_tactic);
         identifier_info = (uu___2255_74326.identifier_info);
         tc_hooks = (uu___2255_74326.tc_hooks);
         dsenv = (uu___2255_74326.dsenv);
         nbe = (uu___2255_74326.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74378)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74382,(uu____74383,t)))::tl1
          ->
          let uu____74404 =
            let uu____74407 = FStar_Syntax_Free.uvars t  in
            ext out uu____74407  in
          aux uu____74404 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74410;
            FStar_Syntax_Syntax.index = uu____74411;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74419 =
            let uu____74422 = FStar_Syntax_Free.uvars t  in
            ext out uu____74422  in
          aux uu____74419 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74480)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74484,(uu____74485,t)))::tl1
          ->
          let uu____74506 =
            let uu____74509 = FStar_Syntax_Free.univs t  in
            ext out uu____74509  in
          aux uu____74506 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74512;
            FStar_Syntax_Syntax.index = uu____74513;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74521 =
            let uu____74524 = FStar_Syntax_Free.univs t  in
            ext out uu____74524  in
          aux uu____74521 tl1
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
          let uu____74586 = FStar_Util.set_add uname out  in
          aux uu____74586 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74589,(uu____74590,t)))::tl1
          ->
          let uu____74611 =
            let uu____74614 = FStar_Syntax_Free.univnames t  in
            ext out uu____74614  in
          aux uu____74611 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74617;
            FStar_Syntax_Syntax.index = uu____74618;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74626 =
            let uu____74629 = FStar_Syntax_Free.univnames t  in
            ext out uu____74629  in
          aux uu____74626 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_74650  ->
            match uu___457_74650 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____74654 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____74667 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____74678 =
      let uu____74687 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____74687
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____74678 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____74735 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_74748  ->
              match uu___458_74748 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____74751 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____74751
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____74757) ->
                  let uu____74774 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____74774))
       in
    FStar_All.pipe_right uu____74735 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_74788  ->
    match uu___459_74788 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____74794 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____74794
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____74817  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____74872) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____74905,uu____74906) -> false  in
      let uu____74920 =
        FStar_List.tryFind
          (fun uu____74942  ->
             match uu____74942 with | (p,uu____74953) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____74920 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____74972,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75002 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____75002
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_75024 = e  in
        {
          solver = (uu___2398_75024.solver);
          range = (uu___2398_75024.range);
          curmodule = (uu___2398_75024.curmodule);
          gamma = (uu___2398_75024.gamma);
          gamma_sig = (uu___2398_75024.gamma_sig);
          gamma_cache = (uu___2398_75024.gamma_cache);
          modules = (uu___2398_75024.modules);
          expected_typ = (uu___2398_75024.expected_typ);
          sigtab = (uu___2398_75024.sigtab);
          attrtab = (uu___2398_75024.attrtab);
          is_pattern = (uu___2398_75024.is_pattern);
          instantiate_imp = (uu___2398_75024.instantiate_imp);
          effects = (uu___2398_75024.effects);
          generalize = (uu___2398_75024.generalize);
          letrecs = (uu___2398_75024.letrecs);
          top_level = (uu___2398_75024.top_level);
          check_uvars = (uu___2398_75024.check_uvars);
          use_eq = (uu___2398_75024.use_eq);
          is_iface = (uu___2398_75024.is_iface);
          admit = (uu___2398_75024.admit);
          lax = (uu___2398_75024.lax);
          lax_universes = (uu___2398_75024.lax_universes);
          phase1 = (uu___2398_75024.phase1);
          failhard = (uu___2398_75024.failhard);
          nosynth = (uu___2398_75024.nosynth);
          uvar_subtyping = (uu___2398_75024.uvar_subtyping);
          tc_term = (uu___2398_75024.tc_term);
          type_of = (uu___2398_75024.type_of);
          universe_of = (uu___2398_75024.universe_of);
          check_type_of = (uu___2398_75024.check_type_of);
          use_bv_sorts = (uu___2398_75024.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_75024.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_75024.normalized_eff_names);
          fv_delta_depths = (uu___2398_75024.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_75024.synth_hook);
          splice = (uu___2398_75024.splice);
          postprocess = (uu___2398_75024.postprocess);
          is_native_tactic = (uu___2398_75024.is_native_tactic);
          identifier_info = (uu___2398_75024.identifier_info);
          tc_hooks = (uu___2398_75024.tc_hooks);
          dsenv = (uu___2398_75024.dsenv);
          nbe = (uu___2398_75024.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_75072 = e  in
      {
        solver = (uu___2407_75072.solver);
        range = (uu___2407_75072.range);
        curmodule = (uu___2407_75072.curmodule);
        gamma = (uu___2407_75072.gamma);
        gamma_sig = (uu___2407_75072.gamma_sig);
        gamma_cache = (uu___2407_75072.gamma_cache);
        modules = (uu___2407_75072.modules);
        expected_typ = (uu___2407_75072.expected_typ);
        sigtab = (uu___2407_75072.sigtab);
        attrtab = (uu___2407_75072.attrtab);
        is_pattern = (uu___2407_75072.is_pattern);
        instantiate_imp = (uu___2407_75072.instantiate_imp);
        effects = (uu___2407_75072.effects);
        generalize = (uu___2407_75072.generalize);
        letrecs = (uu___2407_75072.letrecs);
        top_level = (uu___2407_75072.top_level);
        check_uvars = (uu___2407_75072.check_uvars);
        use_eq = (uu___2407_75072.use_eq);
        is_iface = (uu___2407_75072.is_iface);
        admit = (uu___2407_75072.admit);
        lax = (uu___2407_75072.lax);
        lax_universes = (uu___2407_75072.lax_universes);
        phase1 = (uu___2407_75072.phase1);
        failhard = (uu___2407_75072.failhard);
        nosynth = (uu___2407_75072.nosynth);
        uvar_subtyping = (uu___2407_75072.uvar_subtyping);
        tc_term = (uu___2407_75072.tc_term);
        type_of = (uu___2407_75072.type_of);
        universe_of = (uu___2407_75072.universe_of);
        check_type_of = (uu___2407_75072.check_type_of);
        use_bv_sorts = (uu___2407_75072.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_75072.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_75072.normalized_eff_names);
        fv_delta_depths = (uu___2407_75072.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_75072.synth_hook);
        splice = (uu___2407_75072.splice);
        postprocess = (uu___2407_75072.postprocess);
        is_native_tactic = (uu___2407_75072.is_native_tactic);
        identifier_info = (uu___2407_75072.identifier_info);
        tc_hooks = (uu___2407_75072.tc_hooks);
        dsenv = (uu___2407_75072.dsenv);
        nbe = (uu___2407_75072.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____75088 = FStar_Syntax_Free.names t  in
      let uu____75091 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____75088 uu____75091
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____75114 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____75114
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____75124 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____75124
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____75145 =
      match uu____75145 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____75165 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____75165)
       in
    let uu____75173 =
      let uu____75177 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____75177 FStar_List.rev  in
    FStar_All.pipe_right uu____75173 (FStar_String.concat " ")
  
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
                  (let uu____75247 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____75247 with
                   | FStar_Pervasives_Native.Some uu____75251 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____75254 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____75264;
        univ_ineqs = uu____75265; implicits = uu____75266;_} -> true
    | uu____75278 -> false
  
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
          let uu___2451_75309 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_75309.deferred);
            univ_ineqs = (uu___2451_75309.univ_ineqs);
            implicits = (uu___2451_75309.implicits)
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
          let uu____75348 = FStar_Options.defensive ()  in
          if uu____75348
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____75354 =
              let uu____75356 =
                let uu____75358 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____75358  in
              Prims.op_Negation uu____75356  in
            (if uu____75354
             then
               let uu____75365 =
                 let uu____75371 =
                   let uu____75373 = FStar_Syntax_Print.term_to_string t  in
                   let uu____75375 =
                     let uu____75377 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____75377
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____75373 uu____75375
                    in
                 (FStar_Errors.Warning_Defensive, uu____75371)  in
               FStar_Errors.log_issue rng uu____75365
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
          let uu____75417 =
            let uu____75419 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75419  in
          if uu____75417
          then ()
          else
            (let uu____75424 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____75424 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____75450 =
            let uu____75452 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75452  in
          if uu____75450
          then ()
          else
            (let uu____75457 = bound_vars e  in
             def_check_closed_in rng msg uu____75457 t)
  
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
          let uu___2488_75496 = g  in
          let uu____75497 =
            let uu____75498 =
              let uu____75499 =
                let uu____75506 =
                  let uu____75507 =
                    let uu____75524 =
                      let uu____75535 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____75535]  in
                    (f, uu____75524)  in
                  FStar_Syntax_Syntax.Tm_app uu____75507  in
                FStar_Syntax_Syntax.mk uu____75506  in
              uu____75499 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _75572  -> FStar_TypeChecker_Common.NonTrivial _75572)
              uu____75498
             in
          {
            guard_f = uu____75497;
            deferred = (uu___2488_75496.deferred);
            univ_ineqs = (uu___2488_75496.univ_ineqs);
            implicits = (uu___2488_75496.implicits)
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
          let uu___2495_75590 = g  in
          let uu____75591 =
            let uu____75592 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75592  in
          {
            guard_f = uu____75591;
            deferred = (uu___2495_75590.deferred);
            univ_ineqs = (uu___2495_75590.univ_ineqs);
            implicits = (uu___2495_75590.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_75609 = g  in
          let uu____75610 =
            let uu____75611 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____75611  in
          {
            guard_f = uu____75610;
            deferred = (uu___2500_75609.deferred);
            univ_ineqs = (uu___2500_75609.univ_ineqs);
            implicits = (uu___2500_75609.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_75613 = g  in
          let uu____75614 =
            let uu____75615 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75615  in
          {
            guard_f = uu____75614;
            deferred = (uu___2504_75613.deferred);
            univ_ineqs = (uu___2504_75613.univ_ineqs);
            implicits = (uu___2504_75613.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____75622 ->
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
          let uu____75639 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____75639
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____75646 =
      let uu____75647 = FStar_Syntax_Util.unmeta t  in
      uu____75647.FStar_Syntax_Syntax.n  in
    match uu____75646 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____75651 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____75694 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____75694;
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
                       let uu____75789 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____75789
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_75796 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_75796.deferred);
              univ_ineqs = (uu___2559_75796.univ_ineqs);
              implicits = (uu___2559_75796.implicits)
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
               let uu____75830 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____75830
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
            let uu___2574_75857 = g  in
            let uu____75858 =
              let uu____75859 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____75859  in
            {
              guard_f = uu____75858;
              deferred = (uu___2574_75857.deferred);
              univ_ineqs = (uu___2574_75857.univ_ineqs);
              implicits = (uu___2574_75857.implicits)
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
              let uu____75917 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____75917 with
              | FStar_Pervasives_Native.Some
                  (uu____75942::(tm,uu____75944)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____76008 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____76026 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____76026;
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
                      let uu___2596_76058 = trivial_guard  in
                      {
                        guard_f = (uu___2596_76058.guard_f);
                        deferred = (uu___2596_76058.deferred);
                        univ_ineqs = (uu___2596_76058.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____76076  -> ());
    push = (fun uu____76078  -> ());
    pop = (fun uu____76081  -> ());
    snapshot =
      (fun uu____76084  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____76103  -> fun uu____76104  -> ());
    encode_sig = (fun uu____76119  -> fun uu____76120  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____76126 =
             let uu____76133 = FStar_Options.peek ()  in (e, g, uu____76133)
              in
           [uu____76126]);
    solve = (fun uu____76149  -> fun uu____76150  -> fun uu____76151  -> ());
    finish = (fun uu____76158  -> ());
    refresh = (fun uu____76160  -> ())
  } 