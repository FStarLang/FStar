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
    match projectee with | Beta  -> true | uu____51444 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____51455 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____51466 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____51478 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____51496 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____51507 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____51518 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____51529 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____51540 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____51551 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____51563 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____51584 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____51611 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____51638 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____51662 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____51673 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____51684 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____51695 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____51706 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____51717 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____51728 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____51739 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____51750 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____51761 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____51772 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____51783 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____51794 -> false
  
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
      | uu____51854 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____51880 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____51891 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____51902 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____51914 -> false
  
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
           (fun uu___446_63131  ->
              match uu___446_63131 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____63134 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____63134  in
                  let uu____63135 =
                    let uu____63136 = FStar_Syntax_Subst.compress y  in
                    uu____63136.FStar_Syntax_Syntax.n  in
                  (match uu____63135 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____63140 =
                         let uu___775_63141 = y1  in
                         let uu____63142 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_63141.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_63141.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____63142
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____63140
                   | uu____63145 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_63159 = env  in
      let uu____63160 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_63159.solver);
        range = (uu___781_63159.range);
        curmodule = (uu___781_63159.curmodule);
        gamma = uu____63160;
        gamma_sig = (uu___781_63159.gamma_sig);
        gamma_cache = (uu___781_63159.gamma_cache);
        modules = (uu___781_63159.modules);
        expected_typ = (uu___781_63159.expected_typ);
        sigtab = (uu___781_63159.sigtab);
        attrtab = (uu___781_63159.attrtab);
        is_pattern = (uu___781_63159.is_pattern);
        instantiate_imp = (uu___781_63159.instantiate_imp);
        effects = (uu___781_63159.effects);
        generalize = (uu___781_63159.generalize);
        letrecs = (uu___781_63159.letrecs);
        top_level = (uu___781_63159.top_level);
        check_uvars = (uu___781_63159.check_uvars);
        use_eq = (uu___781_63159.use_eq);
        is_iface = (uu___781_63159.is_iface);
        admit = (uu___781_63159.admit);
        lax = (uu___781_63159.lax);
        lax_universes = (uu___781_63159.lax_universes);
        phase1 = (uu___781_63159.phase1);
        failhard = (uu___781_63159.failhard);
        nosynth = (uu___781_63159.nosynth);
        uvar_subtyping = (uu___781_63159.uvar_subtyping);
        tc_term = (uu___781_63159.tc_term);
        type_of = (uu___781_63159.type_of);
        universe_of = (uu___781_63159.universe_of);
        check_type_of = (uu___781_63159.check_type_of);
        use_bv_sorts = (uu___781_63159.use_bv_sorts);
        qtbl_name_and_index = (uu___781_63159.qtbl_name_and_index);
        normalized_eff_names = (uu___781_63159.normalized_eff_names);
        fv_delta_depths = (uu___781_63159.fv_delta_depths);
        proof_ns = (uu___781_63159.proof_ns);
        synth_hook = (uu___781_63159.synth_hook);
        splice = (uu___781_63159.splice);
        postprocess = (uu___781_63159.postprocess);
        is_native_tactic = (uu___781_63159.is_native_tactic);
        identifier_info = (uu___781_63159.identifier_info);
        tc_hooks = (uu___781_63159.tc_hooks);
        dsenv = (uu___781_63159.dsenv);
        nbe = (uu___781_63159.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____63168  -> fun uu____63169  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_63191 = env  in
      {
        solver = (uu___788_63191.solver);
        range = (uu___788_63191.range);
        curmodule = (uu___788_63191.curmodule);
        gamma = (uu___788_63191.gamma);
        gamma_sig = (uu___788_63191.gamma_sig);
        gamma_cache = (uu___788_63191.gamma_cache);
        modules = (uu___788_63191.modules);
        expected_typ = (uu___788_63191.expected_typ);
        sigtab = (uu___788_63191.sigtab);
        attrtab = (uu___788_63191.attrtab);
        is_pattern = (uu___788_63191.is_pattern);
        instantiate_imp = (uu___788_63191.instantiate_imp);
        effects = (uu___788_63191.effects);
        generalize = (uu___788_63191.generalize);
        letrecs = (uu___788_63191.letrecs);
        top_level = (uu___788_63191.top_level);
        check_uvars = (uu___788_63191.check_uvars);
        use_eq = (uu___788_63191.use_eq);
        is_iface = (uu___788_63191.is_iface);
        admit = (uu___788_63191.admit);
        lax = (uu___788_63191.lax);
        lax_universes = (uu___788_63191.lax_universes);
        phase1 = (uu___788_63191.phase1);
        failhard = (uu___788_63191.failhard);
        nosynth = (uu___788_63191.nosynth);
        uvar_subtyping = (uu___788_63191.uvar_subtyping);
        tc_term = (uu___788_63191.tc_term);
        type_of = (uu___788_63191.type_of);
        universe_of = (uu___788_63191.universe_of);
        check_type_of = (uu___788_63191.check_type_of);
        use_bv_sorts = (uu___788_63191.use_bv_sorts);
        qtbl_name_and_index = (uu___788_63191.qtbl_name_and_index);
        normalized_eff_names = (uu___788_63191.normalized_eff_names);
        fv_delta_depths = (uu___788_63191.fv_delta_depths);
        proof_ns = (uu___788_63191.proof_ns);
        synth_hook = (uu___788_63191.synth_hook);
        splice = (uu___788_63191.splice);
        postprocess = (uu___788_63191.postprocess);
        is_native_tactic = (uu___788_63191.is_native_tactic);
        identifier_info = (uu___788_63191.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_63191.dsenv);
        nbe = (uu___788_63191.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_63203 = e  in
      let uu____63204 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_63203.solver);
        range = (uu___792_63203.range);
        curmodule = (uu___792_63203.curmodule);
        gamma = (uu___792_63203.gamma);
        gamma_sig = (uu___792_63203.gamma_sig);
        gamma_cache = (uu___792_63203.gamma_cache);
        modules = (uu___792_63203.modules);
        expected_typ = (uu___792_63203.expected_typ);
        sigtab = (uu___792_63203.sigtab);
        attrtab = (uu___792_63203.attrtab);
        is_pattern = (uu___792_63203.is_pattern);
        instantiate_imp = (uu___792_63203.instantiate_imp);
        effects = (uu___792_63203.effects);
        generalize = (uu___792_63203.generalize);
        letrecs = (uu___792_63203.letrecs);
        top_level = (uu___792_63203.top_level);
        check_uvars = (uu___792_63203.check_uvars);
        use_eq = (uu___792_63203.use_eq);
        is_iface = (uu___792_63203.is_iface);
        admit = (uu___792_63203.admit);
        lax = (uu___792_63203.lax);
        lax_universes = (uu___792_63203.lax_universes);
        phase1 = (uu___792_63203.phase1);
        failhard = (uu___792_63203.failhard);
        nosynth = (uu___792_63203.nosynth);
        uvar_subtyping = (uu___792_63203.uvar_subtyping);
        tc_term = (uu___792_63203.tc_term);
        type_of = (uu___792_63203.type_of);
        universe_of = (uu___792_63203.universe_of);
        check_type_of = (uu___792_63203.check_type_of);
        use_bv_sorts = (uu___792_63203.use_bv_sorts);
        qtbl_name_and_index = (uu___792_63203.qtbl_name_and_index);
        normalized_eff_names = (uu___792_63203.normalized_eff_names);
        fv_delta_depths = (uu___792_63203.fv_delta_depths);
        proof_ns = (uu___792_63203.proof_ns);
        synth_hook = (uu___792_63203.synth_hook);
        splice = (uu___792_63203.splice);
        postprocess = (uu___792_63203.postprocess);
        is_native_tactic = (uu___792_63203.is_native_tactic);
        identifier_info = (uu___792_63203.identifier_info);
        tc_hooks = (uu___792_63203.tc_hooks);
        dsenv = uu____63204;
        nbe = (uu___792_63203.nbe)
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
      | (NoDelta ,uu____63233) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____63236,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____63238,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____63241 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____63255 . unit -> 'Auu____63255 FStar_Util.smap =
  fun uu____63262  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____63268 . unit -> 'Auu____63268 FStar_Util.smap =
  fun uu____63275  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____63413 = new_gamma_cache ()  in
                  let uu____63416 = new_sigtab ()  in
                  let uu____63419 = new_sigtab ()  in
                  let uu____63426 =
                    let uu____63441 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____63441, FStar_Pervasives_Native.None)  in
                  let uu____63462 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____63466 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____63470 = FStar_Options.using_facts_from ()  in
                  let uu____63471 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____63474 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____63413;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____63416;
                    attrtab = uu____63419;
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
                    qtbl_name_and_index = uu____63426;
                    normalized_eff_names = uu____63462;
                    fv_delta_depths = uu____63466;
                    proof_ns = uu____63470;
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
                    is_native_tactic = (fun uu____63536  -> false);
                    identifier_info = uu____63471;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____63474;
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
  fun uu____63615  ->
    let uu____63616 = FStar_ST.op_Bang query_indices  in
    match uu____63616 with
    | [] -> failwith "Empty query indices!"
    | uu____63671 ->
        let uu____63681 =
          let uu____63691 =
            let uu____63699 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____63699  in
          let uu____63753 = FStar_ST.op_Bang query_indices  in uu____63691 ::
            uu____63753
           in
        FStar_ST.op_Colon_Equals query_indices uu____63681
  
let (pop_query_indices : unit -> unit) =
  fun uu____63849  ->
    let uu____63850 = FStar_ST.op_Bang query_indices  in
    match uu____63850 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____63977  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____64014  ->
    match uu____64014 with
    | (l,n1) ->
        let uu____64024 = FStar_ST.op_Bang query_indices  in
        (match uu____64024 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____64146 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____64169  ->
    let uu____64170 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____64170
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____64238 =
       let uu____64241 = FStar_ST.op_Bang stack  in env :: uu____64241  in
     FStar_ST.op_Colon_Equals stack uu____64238);
    (let uu___860_64290 = env  in
     let uu____64291 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____64294 = FStar_Util.smap_copy (sigtab env)  in
     let uu____64297 = FStar_Util.smap_copy (attrtab env)  in
     let uu____64304 =
       let uu____64319 =
         let uu____64323 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____64323  in
       let uu____64355 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____64319, uu____64355)  in
     let uu____64404 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____64407 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____64410 =
       let uu____64413 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____64413  in
     {
       solver = (uu___860_64290.solver);
       range = (uu___860_64290.range);
       curmodule = (uu___860_64290.curmodule);
       gamma = (uu___860_64290.gamma);
       gamma_sig = (uu___860_64290.gamma_sig);
       gamma_cache = uu____64291;
       modules = (uu___860_64290.modules);
       expected_typ = (uu___860_64290.expected_typ);
       sigtab = uu____64294;
       attrtab = uu____64297;
       is_pattern = (uu___860_64290.is_pattern);
       instantiate_imp = (uu___860_64290.instantiate_imp);
       effects = (uu___860_64290.effects);
       generalize = (uu___860_64290.generalize);
       letrecs = (uu___860_64290.letrecs);
       top_level = (uu___860_64290.top_level);
       check_uvars = (uu___860_64290.check_uvars);
       use_eq = (uu___860_64290.use_eq);
       is_iface = (uu___860_64290.is_iface);
       admit = (uu___860_64290.admit);
       lax = (uu___860_64290.lax);
       lax_universes = (uu___860_64290.lax_universes);
       phase1 = (uu___860_64290.phase1);
       failhard = (uu___860_64290.failhard);
       nosynth = (uu___860_64290.nosynth);
       uvar_subtyping = (uu___860_64290.uvar_subtyping);
       tc_term = (uu___860_64290.tc_term);
       type_of = (uu___860_64290.type_of);
       universe_of = (uu___860_64290.universe_of);
       check_type_of = (uu___860_64290.check_type_of);
       use_bv_sorts = (uu___860_64290.use_bv_sorts);
       qtbl_name_and_index = uu____64304;
       normalized_eff_names = uu____64404;
       fv_delta_depths = uu____64407;
       proof_ns = (uu___860_64290.proof_ns);
       synth_hook = (uu___860_64290.synth_hook);
       splice = (uu___860_64290.splice);
       postprocess = (uu___860_64290.postprocess);
       is_native_tactic = (uu___860_64290.is_native_tactic);
       identifier_info = uu____64410;
       tc_hooks = (uu___860_64290.tc_hooks);
       dsenv = (uu___860_64290.dsenv);
       nbe = (uu___860_64290.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____64438  ->
    let uu____64439 = FStar_ST.op_Bang stack  in
    match uu____64439 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____64493 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____64583  ->
           let uu____64584 = snapshot_stack env  in
           match uu____64584 with
           | (stack_depth,env1) ->
               let uu____64618 = snapshot_query_indices ()  in
               (match uu____64618 with
                | (query_indices_depth,()) ->
                    let uu____64651 = (env1.solver).snapshot msg  in
                    (match uu____64651 with
                     | (solver_depth,()) ->
                         let uu____64708 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____64708 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_64775 = env1  in
                                 {
                                   solver = (uu___885_64775.solver);
                                   range = (uu___885_64775.range);
                                   curmodule = (uu___885_64775.curmodule);
                                   gamma = (uu___885_64775.gamma);
                                   gamma_sig = (uu___885_64775.gamma_sig);
                                   gamma_cache = (uu___885_64775.gamma_cache);
                                   modules = (uu___885_64775.modules);
                                   expected_typ =
                                     (uu___885_64775.expected_typ);
                                   sigtab = (uu___885_64775.sigtab);
                                   attrtab = (uu___885_64775.attrtab);
                                   is_pattern = (uu___885_64775.is_pattern);
                                   instantiate_imp =
                                     (uu___885_64775.instantiate_imp);
                                   effects = (uu___885_64775.effects);
                                   generalize = (uu___885_64775.generalize);
                                   letrecs = (uu___885_64775.letrecs);
                                   top_level = (uu___885_64775.top_level);
                                   check_uvars = (uu___885_64775.check_uvars);
                                   use_eq = (uu___885_64775.use_eq);
                                   is_iface = (uu___885_64775.is_iface);
                                   admit = (uu___885_64775.admit);
                                   lax = (uu___885_64775.lax);
                                   lax_universes =
                                     (uu___885_64775.lax_universes);
                                   phase1 = (uu___885_64775.phase1);
                                   failhard = (uu___885_64775.failhard);
                                   nosynth = (uu___885_64775.nosynth);
                                   uvar_subtyping =
                                     (uu___885_64775.uvar_subtyping);
                                   tc_term = (uu___885_64775.tc_term);
                                   type_of = (uu___885_64775.type_of);
                                   universe_of = (uu___885_64775.universe_of);
                                   check_type_of =
                                     (uu___885_64775.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_64775.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_64775.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_64775.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_64775.fv_delta_depths);
                                   proof_ns = (uu___885_64775.proof_ns);
                                   synth_hook = (uu___885_64775.synth_hook);
                                   splice = (uu___885_64775.splice);
                                   postprocess = (uu___885_64775.postprocess);
                                   is_native_tactic =
                                     (uu___885_64775.is_native_tactic);
                                   identifier_info =
                                     (uu___885_64775.identifier_info);
                                   tc_hooks = (uu___885_64775.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_64775.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____64809  ->
             let uu____64810 =
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
             match uu____64810 with
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
                             ((let uu____64990 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____64990
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____65006 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____65006
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____65038,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____65080 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____65110  ->
                  match uu____65110 with
                  | (m,uu____65118) -> FStar_Ident.lid_equals l m))
           in
        (match uu____65080 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_65133 = env  in
               {
                 solver = (uu___930_65133.solver);
                 range = (uu___930_65133.range);
                 curmodule = (uu___930_65133.curmodule);
                 gamma = (uu___930_65133.gamma);
                 gamma_sig = (uu___930_65133.gamma_sig);
                 gamma_cache = (uu___930_65133.gamma_cache);
                 modules = (uu___930_65133.modules);
                 expected_typ = (uu___930_65133.expected_typ);
                 sigtab = (uu___930_65133.sigtab);
                 attrtab = (uu___930_65133.attrtab);
                 is_pattern = (uu___930_65133.is_pattern);
                 instantiate_imp = (uu___930_65133.instantiate_imp);
                 effects = (uu___930_65133.effects);
                 generalize = (uu___930_65133.generalize);
                 letrecs = (uu___930_65133.letrecs);
                 top_level = (uu___930_65133.top_level);
                 check_uvars = (uu___930_65133.check_uvars);
                 use_eq = (uu___930_65133.use_eq);
                 is_iface = (uu___930_65133.is_iface);
                 admit = (uu___930_65133.admit);
                 lax = (uu___930_65133.lax);
                 lax_universes = (uu___930_65133.lax_universes);
                 phase1 = (uu___930_65133.phase1);
                 failhard = (uu___930_65133.failhard);
                 nosynth = (uu___930_65133.nosynth);
                 uvar_subtyping = (uu___930_65133.uvar_subtyping);
                 tc_term = (uu___930_65133.tc_term);
                 type_of = (uu___930_65133.type_of);
                 universe_of = (uu___930_65133.universe_of);
                 check_type_of = (uu___930_65133.check_type_of);
                 use_bv_sorts = (uu___930_65133.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_65133.normalized_eff_names);
                 fv_delta_depths = (uu___930_65133.fv_delta_depths);
                 proof_ns = (uu___930_65133.proof_ns);
                 synth_hook = (uu___930_65133.synth_hook);
                 splice = (uu___930_65133.splice);
                 postprocess = (uu___930_65133.postprocess);
                 is_native_tactic = (uu___930_65133.is_native_tactic);
                 identifier_info = (uu___930_65133.identifier_info);
                 tc_hooks = (uu___930_65133.tc_hooks);
                 dsenv = (uu___930_65133.dsenv);
                 nbe = (uu___930_65133.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____65150,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_65166 = env  in
               {
                 solver = (uu___939_65166.solver);
                 range = (uu___939_65166.range);
                 curmodule = (uu___939_65166.curmodule);
                 gamma = (uu___939_65166.gamma);
                 gamma_sig = (uu___939_65166.gamma_sig);
                 gamma_cache = (uu___939_65166.gamma_cache);
                 modules = (uu___939_65166.modules);
                 expected_typ = (uu___939_65166.expected_typ);
                 sigtab = (uu___939_65166.sigtab);
                 attrtab = (uu___939_65166.attrtab);
                 is_pattern = (uu___939_65166.is_pattern);
                 instantiate_imp = (uu___939_65166.instantiate_imp);
                 effects = (uu___939_65166.effects);
                 generalize = (uu___939_65166.generalize);
                 letrecs = (uu___939_65166.letrecs);
                 top_level = (uu___939_65166.top_level);
                 check_uvars = (uu___939_65166.check_uvars);
                 use_eq = (uu___939_65166.use_eq);
                 is_iface = (uu___939_65166.is_iface);
                 admit = (uu___939_65166.admit);
                 lax = (uu___939_65166.lax);
                 lax_universes = (uu___939_65166.lax_universes);
                 phase1 = (uu___939_65166.phase1);
                 failhard = (uu___939_65166.failhard);
                 nosynth = (uu___939_65166.nosynth);
                 uvar_subtyping = (uu___939_65166.uvar_subtyping);
                 tc_term = (uu___939_65166.tc_term);
                 type_of = (uu___939_65166.type_of);
                 universe_of = (uu___939_65166.universe_of);
                 check_type_of = (uu___939_65166.check_type_of);
                 use_bv_sorts = (uu___939_65166.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_65166.normalized_eff_names);
                 fv_delta_depths = (uu___939_65166.fv_delta_depths);
                 proof_ns = (uu___939_65166.proof_ns);
                 synth_hook = (uu___939_65166.synth_hook);
                 splice = (uu___939_65166.splice);
                 postprocess = (uu___939_65166.postprocess);
                 is_native_tactic = (uu___939_65166.is_native_tactic);
                 identifier_info = (uu___939_65166.identifier_info);
                 tc_hooks = (uu___939_65166.tc_hooks);
                 dsenv = (uu___939_65166.dsenv);
                 nbe = (uu___939_65166.nbe)
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
        (let uu___946_65209 = e  in
         {
           solver = (uu___946_65209.solver);
           range = r;
           curmodule = (uu___946_65209.curmodule);
           gamma = (uu___946_65209.gamma);
           gamma_sig = (uu___946_65209.gamma_sig);
           gamma_cache = (uu___946_65209.gamma_cache);
           modules = (uu___946_65209.modules);
           expected_typ = (uu___946_65209.expected_typ);
           sigtab = (uu___946_65209.sigtab);
           attrtab = (uu___946_65209.attrtab);
           is_pattern = (uu___946_65209.is_pattern);
           instantiate_imp = (uu___946_65209.instantiate_imp);
           effects = (uu___946_65209.effects);
           generalize = (uu___946_65209.generalize);
           letrecs = (uu___946_65209.letrecs);
           top_level = (uu___946_65209.top_level);
           check_uvars = (uu___946_65209.check_uvars);
           use_eq = (uu___946_65209.use_eq);
           is_iface = (uu___946_65209.is_iface);
           admit = (uu___946_65209.admit);
           lax = (uu___946_65209.lax);
           lax_universes = (uu___946_65209.lax_universes);
           phase1 = (uu___946_65209.phase1);
           failhard = (uu___946_65209.failhard);
           nosynth = (uu___946_65209.nosynth);
           uvar_subtyping = (uu___946_65209.uvar_subtyping);
           tc_term = (uu___946_65209.tc_term);
           type_of = (uu___946_65209.type_of);
           universe_of = (uu___946_65209.universe_of);
           check_type_of = (uu___946_65209.check_type_of);
           use_bv_sorts = (uu___946_65209.use_bv_sorts);
           qtbl_name_and_index = (uu___946_65209.qtbl_name_and_index);
           normalized_eff_names = (uu___946_65209.normalized_eff_names);
           fv_delta_depths = (uu___946_65209.fv_delta_depths);
           proof_ns = (uu___946_65209.proof_ns);
           synth_hook = (uu___946_65209.synth_hook);
           splice = (uu___946_65209.splice);
           postprocess = (uu___946_65209.postprocess);
           is_native_tactic = (uu___946_65209.is_native_tactic);
           identifier_info = (uu___946_65209.identifier_info);
           tc_hooks = (uu___946_65209.tc_hooks);
           dsenv = (uu___946_65209.dsenv);
           nbe = (uu___946_65209.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____65229 =
        let uu____65230 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____65230 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65229
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____65285 =
          let uu____65286 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____65286 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65285
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____65341 =
          let uu____65342 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____65342 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65341
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____65397 =
        let uu____65398 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____65398 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65397
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_65462 = env  in
      {
        solver = (uu___963_65462.solver);
        range = (uu___963_65462.range);
        curmodule = lid;
        gamma = (uu___963_65462.gamma);
        gamma_sig = (uu___963_65462.gamma_sig);
        gamma_cache = (uu___963_65462.gamma_cache);
        modules = (uu___963_65462.modules);
        expected_typ = (uu___963_65462.expected_typ);
        sigtab = (uu___963_65462.sigtab);
        attrtab = (uu___963_65462.attrtab);
        is_pattern = (uu___963_65462.is_pattern);
        instantiate_imp = (uu___963_65462.instantiate_imp);
        effects = (uu___963_65462.effects);
        generalize = (uu___963_65462.generalize);
        letrecs = (uu___963_65462.letrecs);
        top_level = (uu___963_65462.top_level);
        check_uvars = (uu___963_65462.check_uvars);
        use_eq = (uu___963_65462.use_eq);
        is_iface = (uu___963_65462.is_iface);
        admit = (uu___963_65462.admit);
        lax = (uu___963_65462.lax);
        lax_universes = (uu___963_65462.lax_universes);
        phase1 = (uu___963_65462.phase1);
        failhard = (uu___963_65462.failhard);
        nosynth = (uu___963_65462.nosynth);
        uvar_subtyping = (uu___963_65462.uvar_subtyping);
        tc_term = (uu___963_65462.tc_term);
        type_of = (uu___963_65462.type_of);
        universe_of = (uu___963_65462.universe_of);
        check_type_of = (uu___963_65462.check_type_of);
        use_bv_sorts = (uu___963_65462.use_bv_sorts);
        qtbl_name_and_index = (uu___963_65462.qtbl_name_and_index);
        normalized_eff_names = (uu___963_65462.normalized_eff_names);
        fv_delta_depths = (uu___963_65462.fv_delta_depths);
        proof_ns = (uu___963_65462.proof_ns);
        synth_hook = (uu___963_65462.synth_hook);
        splice = (uu___963_65462.splice);
        postprocess = (uu___963_65462.postprocess);
        is_native_tactic = (uu___963_65462.is_native_tactic);
        identifier_info = (uu___963_65462.identifier_info);
        tc_hooks = (uu___963_65462.tc_hooks);
        dsenv = (uu___963_65462.dsenv);
        nbe = (uu___963_65462.nbe)
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
      let uu____65493 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____65493
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65506 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____65506)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____65521 =
      let uu____65523 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____65523  in
    (FStar_Errors.Fatal_VariableNotFound, uu____65521)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____65532  ->
    let uu____65533 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____65533
  
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
      | ((formals,t),uu____65633) ->
          let vs = mk_univ_subst formals us  in
          let uu____65657 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____65657)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_65674  ->
    match uu___447_65674 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____65700  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____65720 = inst_tscheme t  in
      match uu____65720 with
      | (us,t1) ->
          let uu____65731 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____65731)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____65752  ->
          match uu____65752 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____65774 =
                         let uu____65776 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____65780 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____65784 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____65786 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____65776 uu____65780 uu____65784 uu____65786
                          in
                       failwith uu____65774)
                    else ();
                    (let uu____65791 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____65791))
               | uu____65800 ->
                   let uu____65801 =
                     let uu____65803 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____65803
                      in
                   failwith uu____65801)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____65815 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____65826 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____65837 -> false
  
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
             | ([],uu____65885) -> Maybe
             | (uu____65892,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____65912 -> No  in
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
          let uu____66006 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____66006 with
          | FStar_Pervasives_Native.None  ->
              let uu____66029 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_66073  ->
                     match uu___448_66073 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____66112 = FStar_Ident.lid_equals lid l  in
                         if uu____66112
                         then
                           let uu____66135 =
                             let uu____66154 =
                               let uu____66169 = inst_tscheme t  in
                               FStar_Util.Inl uu____66169  in
                             let uu____66184 = FStar_Ident.range_of_lid l  in
                             (uu____66154, uu____66184)  in
                           FStar_Pervasives_Native.Some uu____66135
                         else FStar_Pervasives_Native.None
                     | uu____66237 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____66029
                (fun uu____66275  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_66284  ->
                        match uu___449_66284 with
                        | (uu____66287,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____66289);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____66290;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____66291;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____66292;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____66293;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____66313 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____66313
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
                                  uu____66365 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____66372 -> cache t  in
                            let uu____66373 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____66373 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____66379 =
                                   let uu____66380 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____66380)
                                    in
                                 maybe_cache uu____66379)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____66451 = find_in_sigtab env lid  in
         match uu____66451 with
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
      let uu____66532 = lookup_qname env lid  in
      match uu____66532 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____66553,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____66667 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____66667 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____66712 =
          let uu____66715 = lookup_attr env1 attr  in se1 :: uu____66715  in
        FStar_Util.smap_add (attrtab env1) attr uu____66712  in
      FStar_List.iter
        (fun attr  ->
           let uu____66725 =
             let uu____66726 = FStar_Syntax_Subst.compress attr  in
             uu____66726.FStar_Syntax_Syntax.n  in
           match uu____66725 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____66730 =
                 let uu____66732 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____66732.FStar_Ident.str  in
               add_one1 env se uu____66730
           | uu____66733 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____66756) ->
          add_sigelts env ses
      | uu____66765 ->
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
            | uu____66780 -> ()))

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
        (fun uu___450_66812  ->
           match uu___450_66812 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____66830 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____66892,lb::[]),uu____66894) ->
            let uu____66903 =
              let uu____66912 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____66921 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____66912, uu____66921)  in
            FStar_Pervasives_Native.Some uu____66903
        | FStar_Syntax_Syntax.Sig_let ((uu____66934,lbs),uu____66936) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____66968 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____66981 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____66981
                     then
                       let uu____66994 =
                         let uu____67003 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____67012 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____67003, uu____67012)  in
                       FStar_Pervasives_Native.Some uu____66994
                     else FStar_Pervasives_Native.None)
        | uu____67035 -> FStar_Pervasives_Native.None
  
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
          let uu____67095 =
            let uu____67104 =
              let uu____67109 =
                let uu____67110 =
                  let uu____67113 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____67113
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____67110)  in
              inst_tscheme1 uu____67109  in
            (uu____67104, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67095
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____67135,uu____67136) ->
          let uu____67141 =
            let uu____67150 =
              let uu____67155 =
                let uu____67156 =
                  let uu____67159 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____67159  in
                (us, uu____67156)  in
              inst_tscheme1 uu____67155  in
            (uu____67150, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67141
      | uu____67178 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____67267 =
          match uu____67267 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____67363,uvs,t,uu____67366,uu____67367,uu____67368);
                      FStar_Syntax_Syntax.sigrng = uu____67369;
                      FStar_Syntax_Syntax.sigquals = uu____67370;
                      FStar_Syntax_Syntax.sigmeta = uu____67371;
                      FStar_Syntax_Syntax.sigattrs = uu____67372;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67395 =
                     let uu____67404 = inst_tscheme1 (uvs, t)  in
                     (uu____67404, rng)  in
                   FStar_Pervasives_Native.Some uu____67395
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____67428;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____67430;
                      FStar_Syntax_Syntax.sigattrs = uu____67431;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67448 =
                     let uu____67450 = in_cur_mod env l  in uu____67450 = Yes
                      in
                   if uu____67448
                   then
                     let uu____67462 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____67462
                      then
                        let uu____67478 =
                          let uu____67487 = inst_tscheme1 (uvs, t)  in
                          (uu____67487, rng)  in
                        FStar_Pervasives_Native.Some uu____67478
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____67520 =
                        let uu____67529 = inst_tscheme1 (uvs, t)  in
                        (uu____67529, rng)  in
                      FStar_Pervasives_Native.Some uu____67520)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67554,uu____67555);
                      FStar_Syntax_Syntax.sigrng = uu____67556;
                      FStar_Syntax_Syntax.sigquals = uu____67557;
                      FStar_Syntax_Syntax.sigmeta = uu____67558;
                      FStar_Syntax_Syntax.sigattrs = uu____67559;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____67600 =
                          let uu____67609 = inst_tscheme1 (uvs, k)  in
                          (uu____67609, rng)  in
                        FStar_Pervasives_Native.Some uu____67600
                    | uu____67630 ->
                        let uu____67631 =
                          let uu____67640 =
                            let uu____67645 =
                              let uu____67646 =
                                let uu____67649 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67649
                                 in
                              (uvs, uu____67646)  in
                            inst_tscheme1 uu____67645  in
                          (uu____67640, rng)  in
                        FStar_Pervasives_Native.Some uu____67631)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67672,uu____67673);
                      FStar_Syntax_Syntax.sigrng = uu____67674;
                      FStar_Syntax_Syntax.sigquals = uu____67675;
                      FStar_Syntax_Syntax.sigmeta = uu____67676;
                      FStar_Syntax_Syntax.sigattrs = uu____67677;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____67719 =
                          let uu____67728 = inst_tscheme_with (uvs, k) us  in
                          (uu____67728, rng)  in
                        FStar_Pervasives_Native.Some uu____67719
                    | uu____67749 ->
                        let uu____67750 =
                          let uu____67759 =
                            let uu____67764 =
                              let uu____67765 =
                                let uu____67768 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67768
                                 in
                              (uvs, uu____67765)  in
                            inst_tscheme_with uu____67764 us  in
                          (uu____67759, rng)  in
                        FStar_Pervasives_Native.Some uu____67750)
               | FStar_Util.Inr se ->
                   let uu____67804 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____67825;
                          FStar_Syntax_Syntax.sigrng = uu____67826;
                          FStar_Syntax_Syntax.sigquals = uu____67827;
                          FStar_Syntax_Syntax.sigmeta = uu____67828;
                          FStar_Syntax_Syntax.sigattrs = uu____67829;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____67844 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____67804
                     (FStar_Util.map_option
                        (fun uu____67892  ->
                           match uu____67892 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____67923 =
          let uu____67934 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____67934 mapper  in
        match uu____67923 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____68008 =
              let uu____68019 =
                let uu____68026 =
                  let uu___1290_68029 = t  in
                  let uu____68030 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_68029.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____68030;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_68029.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____68026)  in
              (uu____68019, r)  in
            FStar_Pervasives_Native.Some uu____68008
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____68079 = lookup_qname env l  in
      match uu____68079 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____68100 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____68154 = try_lookup_bv env bv  in
      match uu____68154 with
      | FStar_Pervasives_Native.None  ->
          let uu____68169 = variable_not_found bv  in
          FStar_Errors.raise_error uu____68169 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____68185 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____68186 =
            let uu____68187 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____68187  in
          (uu____68185, uu____68186)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____68209 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____68209 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____68275 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____68275  in
          let uu____68276 =
            let uu____68285 =
              let uu____68290 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____68290)  in
            (uu____68285, r1)  in
          FStar_Pervasives_Native.Some uu____68276
  
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
        let uu____68325 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____68325 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____68358,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____68383 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____68383  in
            let uu____68384 =
              let uu____68389 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____68389, r1)  in
            FStar_Pervasives_Native.Some uu____68384
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____68413 = try_lookup_lid env l  in
      match uu____68413 with
      | FStar_Pervasives_Native.None  ->
          let uu____68440 = name_not_found l  in
          let uu____68446 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____68440 uu____68446
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_68489  ->
              match uu___451_68489 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____68493 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____68514 = lookup_qname env lid  in
      match uu____68514 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68523,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68526;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____68528;
              FStar_Syntax_Syntax.sigattrs = uu____68529;_},FStar_Pervasives_Native.None
            ),uu____68530)
          ->
          let uu____68579 =
            let uu____68586 =
              let uu____68587 =
                let uu____68590 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____68590 t  in
              (uvs, uu____68587)  in
            (uu____68586, q)  in
          FStar_Pervasives_Native.Some uu____68579
      | uu____68603 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68625 = lookup_qname env lid  in
      match uu____68625 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68630,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68633;
              FStar_Syntax_Syntax.sigquals = uu____68634;
              FStar_Syntax_Syntax.sigmeta = uu____68635;
              FStar_Syntax_Syntax.sigattrs = uu____68636;_},FStar_Pervasives_Native.None
            ),uu____68637)
          ->
          let uu____68686 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68686 (uvs, t)
      | uu____68691 ->
          let uu____68692 = name_not_found lid  in
          let uu____68698 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68692 uu____68698
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68718 = lookup_qname env lid  in
      match uu____68718 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68723,uvs,t,uu____68726,uu____68727,uu____68728);
              FStar_Syntax_Syntax.sigrng = uu____68729;
              FStar_Syntax_Syntax.sigquals = uu____68730;
              FStar_Syntax_Syntax.sigmeta = uu____68731;
              FStar_Syntax_Syntax.sigattrs = uu____68732;_},FStar_Pervasives_Native.None
            ),uu____68733)
          ->
          let uu____68788 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68788 (uvs, t)
      | uu____68793 ->
          let uu____68794 = name_not_found lid  in
          let uu____68800 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68794 uu____68800
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____68823 = lookup_qname env lid  in
      match uu____68823 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____68831,uu____68832,uu____68833,uu____68834,uu____68835,dcs);
              FStar_Syntax_Syntax.sigrng = uu____68837;
              FStar_Syntax_Syntax.sigquals = uu____68838;
              FStar_Syntax_Syntax.sigmeta = uu____68839;
              FStar_Syntax_Syntax.sigattrs = uu____68840;_},uu____68841),uu____68842)
          -> (true, dcs)
      | uu____68905 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____68921 = lookup_qname env lid  in
      match uu____68921 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68922,uu____68923,uu____68924,l,uu____68926,uu____68927);
              FStar_Syntax_Syntax.sigrng = uu____68928;
              FStar_Syntax_Syntax.sigquals = uu____68929;
              FStar_Syntax_Syntax.sigmeta = uu____68930;
              FStar_Syntax_Syntax.sigattrs = uu____68931;_},uu____68932),uu____68933)
          -> l
      | uu____68990 ->
          let uu____68991 =
            let uu____68993 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____68993  in
          failwith uu____68991
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69063)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69120) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69144 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69144
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69179 -> FStar_Pervasives_Native.None)
          | uu____69188 -> FStar_Pervasives_Native.None
  
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
        let uu____69250 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____69250
  
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
        let uu____69283 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____69283
  
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
             (FStar_Util.Inl uu____69335,uu____69336) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____69385),uu____69386) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____69435 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____69453 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____69463 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____69480 ->
                  let uu____69487 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____69487
              | FStar_Syntax_Syntax.Sig_let ((uu____69488,lbs),uu____69490)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____69506 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____69506
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____69513 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____69521 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____69522 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____69529 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69530 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____69531 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69532 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____69545 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____69563 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____69563
           (fun d_opt  ->
              let uu____69576 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____69576
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____69586 =
                   let uu____69589 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____69589  in
                 match uu____69586 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____69590 =
                       let uu____69592 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____69592
                        in
                     failwith uu____69590
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____69597 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____69597
                       then
                         let uu____69600 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____69602 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____69604 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____69600 uu____69602 uu____69604
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
        (FStar_Util.Inr (se,uu____69629),uu____69630) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____69679 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____69701),uu____69702) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____69751 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____69773 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____69773
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____69796 = lookup_attrs_of_lid env fv_lid1  in
        match uu____69796 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____69820 =
                      let uu____69821 = FStar_Syntax_Util.un_uinst tm  in
                      uu____69821.FStar_Syntax_Syntax.n  in
                    match uu____69820 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____69826 -> false))
  
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
      let uu____69860 = lookup_qname env ftv  in
      match uu____69860 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69864) ->
          let uu____69909 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____69909 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____69930,t),r) ->
               let uu____69945 =
                 let uu____69946 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____69946 t  in
               FStar_Pervasives_Native.Some uu____69945)
      | uu____69947 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____69959 = try_lookup_effect_lid env ftv  in
      match uu____69959 with
      | FStar_Pervasives_Native.None  ->
          let uu____69962 = name_not_found ftv  in
          let uu____69968 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____69962 uu____69968
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
        let uu____69992 = lookup_qname env lid0  in
        match uu____69992 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____70003);
                FStar_Syntax_Syntax.sigrng = uu____70004;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____70006;
                FStar_Syntax_Syntax.sigattrs = uu____70007;_},FStar_Pervasives_Native.None
              ),uu____70008)
            ->
            let lid1 =
              let uu____70062 =
                let uu____70063 = FStar_Ident.range_of_lid lid  in
                let uu____70064 =
                  let uu____70065 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____70065  in
                FStar_Range.set_use_range uu____70063 uu____70064  in
              FStar_Ident.set_lid_range lid uu____70062  in
            let uu____70066 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_70072  ->
                      match uu___452_70072 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____70075 -> false))
               in
            if uu____70066
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____70094 =
                      let uu____70096 =
                        let uu____70098 = get_range env  in
                        FStar_Range.string_of_range uu____70098  in
                      let uu____70099 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____70101 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____70096 uu____70099 uu____70101
                       in
                    failwith uu____70094)
                  in
               match (binders, univs1) with
               | ([],uu____70122) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____70148,uu____70149::uu____70150::uu____70151) ->
                   let uu____70172 =
                     let uu____70174 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____70176 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____70174 uu____70176
                      in
                   failwith uu____70172
               | uu____70187 ->
                   let uu____70202 =
                     let uu____70207 =
                       let uu____70208 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____70208)  in
                     inst_tscheme_with uu____70207 insts  in
                   (match uu____70202 with
                    | (uu____70221,t) ->
                        let t1 =
                          let uu____70224 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____70224 t  in
                        let uu____70225 =
                          let uu____70226 = FStar_Syntax_Subst.compress t1
                             in
                          uu____70226.FStar_Syntax_Syntax.n  in
                        (match uu____70225 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____70261 -> failwith "Impossible")))
        | uu____70269 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____70293 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____70293 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____70306,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____70313 = find1 l2  in
            (match uu____70313 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____70320 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____70320 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____70324 = find1 l  in
            (match uu____70324 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____70329 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____70329
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____70344 = lookup_qname env l1  in
      match uu____70344 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____70347;
              FStar_Syntax_Syntax.sigrng = uu____70348;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____70350;
              FStar_Syntax_Syntax.sigattrs = uu____70351;_},uu____70352),uu____70353)
          -> q
      | uu____70404 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____70428 =
          let uu____70429 =
            let uu____70431 = FStar_Util.string_of_int i  in
            let uu____70433 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____70431 uu____70433
             in
          failwith uu____70429  in
        let uu____70436 = lookup_datacon env lid  in
        match uu____70436 with
        | (uu____70441,t) ->
            let uu____70443 =
              let uu____70444 = FStar_Syntax_Subst.compress t  in
              uu____70444.FStar_Syntax_Syntax.n  in
            (match uu____70443 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70448) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____70492 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____70492
                      FStar_Pervasives_Native.fst)
             | uu____70503 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70517 = lookup_qname env l  in
      match uu____70517 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____70519,uu____70520,uu____70521);
              FStar_Syntax_Syntax.sigrng = uu____70522;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70524;
              FStar_Syntax_Syntax.sigattrs = uu____70525;_},uu____70526),uu____70527)
          ->
          FStar_Util.for_some
            (fun uu___453_70580  ->
               match uu___453_70580 with
               | FStar_Syntax_Syntax.Projector uu____70582 -> true
               | uu____70588 -> false) quals
      | uu____70590 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70604 = lookup_qname env lid  in
      match uu____70604 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____70606,uu____70607,uu____70608,uu____70609,uu____70610,uu____70611);
              FStar_Syntax_Syntax.sigrng = uu____70612;
              FStar_Syntax_Syntax.sigquals = uu____70613;
              FStar_Syntax_Syntax.sigmeta = uu____70614;
              FStar_Syntax_Syntax.sigattrs = uu____70615;_},uu____70616),uu____70617)
          -> true
      | uu____70675 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70689 = lookup_qname env lid  in
      match uu____70689 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____70691,uu____70692,uu____70693,uu____70694,uu____70695,uu____70696);
              FStar_Syntax_Syntax.sigrng = uu____70697;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70699;
              FStar_Syntax_Syntax.sigattrs = uu____70700;_},uu____70701),uu____70702)
          ->
          FStar_Util.for_some
            (fun uu___454_70763  ->
               match uu___454_70763 with
               | FStar_Syntax_Syntax.RecordType uu____70765 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____70775 -> true
               | uu____70785 -> false) quals
      | uu____70787 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____70797,uu____70798);
            FStar_Syntax_Syntax.sigrng = uu____70799;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____70801;
            FStar_Syntax_Syntax.sigattrs = uu____70802;_},uu____70803),uu____70804)
        ->
        FStar_Util.for_some
          (fun uu___455_70861  ->
             match uu___455_70861 with
             | FStar_Syntax_Syntax.Action uu____70863 -> true
             | uu____70865 -> false) quals
    | uu____70867 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70881 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____70881
  
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
      let uu____70898 =
        let uu____70899 = FStar_Syntax_Util.un_uinst head1  in
        uu____70899.FStar_Syntax_Syntax.n  in
      match uu____70898 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____70905 ->
               true
           | uu____70908 -> false)
      | uu____70910 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70924 = lookup_qname env l  in
      match uu____70924 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____70927),uu____70928) ->
          FStar_Util.for_some
            (fun uu___456_70976  ->
               match uu___456_70976 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____70979 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____70981 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____71057 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____71075) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____71093 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____71101 ->
                 FStar_Pervasives_Native.Some true
             | uu____71120 -> FStar_Pervasives_Native.Some false)
         in
      let uu____71123 =
        let uu____71127 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____71127 mapper  in
      match uu____71123 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____71187 = lookup_qname env lid  in
      match uu____71187 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71191,uu____71192,tps,uu____71194,uu____71195,uu____71196);
              FStar_Syntax_Syntax.sigrng = uu____71197;
              FStar_Syntax_Syntax.sigquals = uu____71198;
              FStar_Syntax_Syntax.sigmeta = uu____71199;
              FStar_Syntax_Syntax.sigattrs = uu____71200;_},uu____71201),uu____71202)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____71268 -> FStar_Pervasives_Native.None
  
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
           (fun uu____71314  ->
              match uu____71314 with
              | (d,uu____71323) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____71339 = effect_decl_opt env l  in
      match uu____71339 with
      | FStar_Pervasives_Native.None  ->
          let uu____71354 = name_not_found l  in
          let uu____71360 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____71354 uu____71360
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____71383  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____71402  ->
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
        let uu____71434 = FStar_Ident.lid_equals l1 l2  in
        if uu____71434
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____71445 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____71445
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____71456 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____71509  ->
                        match uu____71509 with
                        | (m1,m2,uu____71523,uu____71524,uu____71525) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____71456 with
              | FStar_Pervasives_Native.None  ->
                  let uu____71542 =
                    let uu____71548 =
                      let uu____71550 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____71552 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____71550
                        uu____71552
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____71548)
                     in
                  FStar_Errors.raise_error uu____71542 env.range
              | FStar_Pervasives_Native.Some
                  (uu____71562,uu____71563,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____71597 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____71597
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
  'Auu____71617 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____71617) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____71646 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____71672  ->
                match uu____71672 with
                | (d,uu____71679) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____71646 with
      | FStar_Pervasives_Native.None  ->
          let uu____71690 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____71690
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____71705 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____71705 with
           | (uu____71720,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____71738)::(wp,uu____71740)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____71796 -> failwith "Impossible"))
  
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
          let uu____71854 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____71854
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____71859 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____71859
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
                  let uu____71870 = get_range env  in
                  let uu____71871 =
                    let uu____71878 =
                      let uu____71879 =
                        let uu____71896 =
                          let uu____71907 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____71907]  in
                        (null_wp, uu____71896)  in
                      FStar_Syntax_Syntax.Tm_app uu____71879  in
                    FStar_Syntax_Syntax.mk uu____71878  in
                  uu____71871 FStar_Pervasives_Native.None uu____71870  in
                let uu____71944 =
                  let uu____71945 =
                    let uu____71956 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____71956]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____71945;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____71944))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_71994 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_71994.order);
              joins = (uu___1944_71994.joins)
            }  in
          let uu___1947_72003 = env  in
          {
            solver = (uu___1947_72003.solver);
            range = (uu___1947_72003.range);
            curmodule = (uu___1947_72003.curmodule);
            gamma = (uu___1947_72003.gamma);
            gamma_sig = (uu___1947_72003.gamma_sig);
            gamma_cache = (uu___1947_72003.gamma_cache);
            modules = (uu___1947_72003.modules);
            expected_typ = (uu___1947_72003.expected_typ);
            sigtab = (uu___1947_72003.sigtab);
            attrtab = (uu___1947_72003.attrtab);
            is_pattern = (uu___1947_72003.is_pattern);
            instantiate_imp = (uu___1947_72003.instantiate_imp);
            effects;
            generalize = (uu___1947_72003.generalize);
            letrecs = (uu___1947_72003.letrecs);
            top_level = (uu___1947_72003.top_level);
            check_uvars = (uu___1947_72003.check_uvars);
            use_eq = (uu___1947_72003.use_eq);
            is_iface = (uu___1947_72003.is_iface);
            admit = (uu___1947_72003.admit);
            lax = (uu___1947_72003.lax);
            lax_universes = (uu___1947_72003.lax_universes);
            phase1 = (uu___1947_72003.phase1);
            failhard = (uu___1947_72003.failhard);
            nosynth = (uu___1947_72003.nosynth);
            uvar_subtyping = (uu___1947_72003.uvar_subtyping);
            tc_term = (uu___1947_72003.tc_term);
            type_of = (uu___1947_72003.type_of);
            universe_of = (uu___1947_72003.universe_of);
            check_type_of = (uu___1947_72003.check_type_of);
            use_bv_sorts = (uu___1947_72003.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_72003.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_72003.normalized_eff_names);
            fv_delta_depths = (uu___1947_72003.fv_delta_depths);
            proof_ns = (uu___1947_72003.proof_ns);
            synth_hook = (uu___1947_72003.synth_hook);
            splice = (uu___1947_72003.splice);
            postprocess = (uu___1947_72003.postprocess);
            is_native_tactic = (uu___1947_72003.is_native_tactic);
            identifier_info = (uu___1947_72003.identifier_info);
            tc_hooks = (uu___1947_72003.tc_hooks);
            dsenv = (uu___1947_72003.dsenv);
            nbe = (uu___1947_72003.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____72033 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____72033  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____72191 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____72192 = l1 u t wp e  in
                                l2 u t uu____72191 uu____72192))
                | uu____72193 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____72265 = inst_tscheme_with lift_t [u]  in
            match uu____72265 with
            | (uu____72272,lift_t1) ->
                let uu____72274 =
                  let uu____72281 =
                    let uu____72282 =
                      let uu____72299 =
                        let uu____72310 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72319 =
                          let uu____72330 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____72330]  in
                        uu____72310 :: uu____72319  in
                      (lift_t1, uu____72299)  in
                    FStar_Syntax_Syntax.Tm_app uu____72282  in
                  FStar_Syntax_Syntax.mk uu____72281  in
                uu____72274 FStar_Pervasives_Native.None
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
            let uu____72440 = inst_tscheme_with lift_t [u]  in
            match uu____72440 with
            | (uu____72447,lift_t1) ->
                let uu____72449 =
                  let uu____72456 =
                    let uu____72457 =
                      let uu____72474 =
                        let uu____72485 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72494 =
                          let uu____72505 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____72514 =
                            let uu____72525 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____72525]  in
                          uu____72505 :: uu____72514  in
                        uu____72485 :: uu____72494  in
                      (lift_t1, uu____72474)  in
                    FStar_Syntax_Syntax.Tm_app uu____72457  in
                  FStar_Syntax_Syntax.mk uu____72456  in
                uu____72449 FStar_Pervasives_Native.None
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
              let uu____72627 =
                let uu____72628 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____72628
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____72627  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____72637 =
              let uu____72639 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____72639  in
            let uu____72640 =
              let uu____72642 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____72670 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____72670)
                 in
              FStar_Util.dflt "none" uu____72642  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____72637
              uu____72640
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____72699  ->
                    match uu____72699 with
                    | (e,uu____72707) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____72730 =
            match uu____72730 with
            | (i,j) ->
                let uu____72741 = FStar_Ident.lid_equals i j  in
                if uu____72741
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _72748  -> FStar_Pervasives_Native.Some _72748)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____72777 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____72787 = FStar_Ident.lid_equals i k  in
                        if uu____72787
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____72801 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____72801
                                  then []
                                  else
                                    (let uu____72808 =
                                       let uu____72817 =
                                         find_edge order1 (i, k)  in
                                       let uu____72820 =
                                         find_edge order1 (k, j)  in
                                       (uu____72817, uu____72820)  in
                                     match uu____72808 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____72835 =
                                           compose_edges e1 e2  in
                                         [uu____72835]
                                     | uu____72836 -> [])))))
                 in
              FStar_List.append order1 uu____72777  in
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
                   let uu____72866 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____72869 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____72869
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____72866
                   then
                     let uu____72876 =
                       let uu____72882 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____72882)
                        in
                     let uu____72886 = get_range env  in
                     FStar_Errors.raise_error uu____72876 uu____72886
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____72964 = FStar_Ident.lid_equals i j
                                   in
                                if uu____72964
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____73016 =
                                              let uu____73025 =
                                                find_edge order2 (i, k)  in
                                              let uu____73028 =
                                                find_edge order2 (j, k)  in
                                              (uu____73025, uu____73028)  in
                                            match uu____73016 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____73070,uu____73071)
                                                     ->
                                                     let uu____73078 =
                                                       let uu____73085 =
                                                         let uu____73087 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73087
                                                          in
                                                       let uu____73090 =
                                                         let uu____73092 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73092
                                                          in
                                                       (uu____73085,
                                                         uu____73090)
                                                        in
                                                     (match uu____73078 with
                                                      | (true ,true ) ->
                                                          let uu____73109 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____73109
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
                                            | uu____73152 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_73225 = env.effects  in
              { decls = (uu___2074_73225.decls); order = order2; joins }  in
            let uu___2077_73226 = env  in
            {
              solver = (uu___2077_73226.solver);
              range = (uu___2077_73226.range);
              curmodule = (uu___2077_73226.curmodule);
              gamma = (uu___2077_73226.gamma);
              gamma_sig = (uu___2077_73226.gamma_sig);
              gamma_cache = (uu___2077_73226.gamma_cache);
              modules = (uu___2077_73226.modules);
              expected_typ = (uu___2077_73226.expected_typ);
              sigtab = (uu___2077_73226.sigtab);
              attrtab = (uu___2077_73226.attrtab);
              is_pattern = (uu___2077_73226.is_pattern);
              instantiate_imp = (uu___2077_73226.instantiate_imp);
              effects;
              generalize = (uu___2077_73226.generalize);
              letrecs = (uu___2077_73226.letrecs);
              top_level = (uu___2077_73226.top_level);
              check_uvars = (uu___2077_73226.check_uvars);
              use_eq = (uu___2077_73226.use_eq);
              is_iface = (uu___2077_73226.is_iface);
              admit = (uu___2077_73226.admit);
              lax = (uu___2077_73226.lax);
              lax_universes = (uu___2077_73226.lax_universes);
              phase1 = (uu___2077_73226.phase1);
              failhard = (uu___2077_73226.failhard);
              nosynth = (uu___2077_73226.nosynth);
              uvar_subtyping = (uu___2077_73226.uvar_subtyping);
              tc_term = (uu___2077_73226.tc_term);
              type_of = (uu___2077_73226.type_of);
              universe_of = (uu___2077_73226.universe_of);
              check_type_of = (uu___2077_73226.check_type_of);
              use_bv_sorts = (uu___2077_73226.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_73226.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_73226.normalized_eff_names);
              fv_delta_depths = (uu___2077_73226.fv_delta_depths);
              proof_ns = (uu___2077_73226.proof_ns);
              synth_hook = (uu___2077_73226.synth_hook);
              splice = (uu___2077_73226.splice);
              postprocess = (uu___2077_73226.postprocess);
              is_native_tactic = (uu___2077_73226.is_native_tactic);
              identifier_info = (uu___2077_73226.identifier_info);
              tc_hooks = (uu___2077_73226.tc_hooks);
              dsenv = (uu___2077_73226.dsenv);
              nbe = (uu___2077_73226.nbe)
            }))
      | uu____73227 -> env
  
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
        | uu____73256 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____73269 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____73269 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____73286 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____73286 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____73311 =
                     let uu____73317 =
                       let uu____73319 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____73327 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____73338 =
                         let uu____73340 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____73340  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____73319 uu____73327 uu____73338
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____73317)
                      in
                   FStar_Errors.raise_error uu____73311
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____73348 =
                     let uu____73359 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____73359 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____73396  ->
                        fun uu____73397  ->
                          match (uu____73396, uu____73397) with
                          | ((x,uu____73427),(t,uu____73429)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____73348
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____73460 =
                     let uu___2115_73461 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_73461.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_73461.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_73461.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_73461.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____73460
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____73473 .
    'Auu____73473 ->
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
          let uu____73503 = effect_decl_opt env effect_name  in
          match uu____73503 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____73542 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____73565 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____73604 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____73604
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____73609 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____73609
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____73624 =
                     let uu____73627 = get_range env  in
                     let uu____73628 =
                       let uu____73635 =
                         let uu____73636 =
                           let uu____73653 =
                             let uu____73664 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____73664; wp]  in
                           (repr, uu____73653)  in
                         FStar_Syntax_Syntax.Tm_app uu____73636  in
                       FStar_Syntax_Syntax.mk uu____73635  in
                     uu____73628 FStar_Pervasives_Native.None uu____73627  in
                   FStar_Pervasives_Native.Some uu____73624)
  
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
      | uu____73808 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____73823 =
        let uu____73824 = FStar_Syntax_Subst.compress t  in
        uu____73824.FStar_Syntax_Syntax.n  in
      match uu____73823 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____73828,c) ->
          is_reifiable_comp env c
      | uu____73850 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____73870 =
           let uu____73872 = is_reifiable_effect env l  in
           Prims.op_Negation uu____73872  in
         if uu____73870
         then
           let uu____73875 =
             let uu____73881 =
               let uu____73883 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____73883
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____73881)  in
           let uu____73887 = get_range env  in
           FStar_Errors.raise_error uu____73875 uu____73887
         else ());
        (let uu____73890 = effect_repr_aux true env c u_c  in
         match uu____73890 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_73926 = env  in
        {
          solver = (uu___2180_73926.solver);
          range = (uu___2180_73926.range);
          curmodule = (uu___2180_73926.curmodule);
          gamma = (uu___2180_73926.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_73926.gamma_cache);
          modules = (uu___2180_73926.modules);
          expected_typ = (uu___2180_73926.expected_typ);
          sigtab = (uu___2180_73926.sigtab);
          attrtab = (uu___2180_73926.attrtab);
          is_pattern = (uu___2180_73926.is_pattern);
          instantiate_imp = (uu___2180_73926.instantiate_imp);
          effects = (uu___2180_73926.effects);
          generalize = (uu___2180_73926.generalize);
          letrecs = (uu___2180_73926.letrecs);
          top_level = (uu___2180_73926.top_level);
          check_uvars = (uu___2180_73926.check_uvars);
          use_eq = (uu___2180_73926.use_eq);
          is_iface = (uu___2180_73926.is_iface);
          admit = (uu___2180_73926.admit);
          lax = (uu___2180_73926.lax);
          lax_universes = (uu___2180_73926.lax_universes);
          phase1 = (uu___2180_73926.phase1);
          failhard = (uu___2180_73926.failhard);
          nosynth = (uu___2180_73926.nosynth);
          uvar_subtyping = (uu___2180_73926.uvar_subtyping);
          tc_term = (uu___2180_73926.tc_term);
          type_of = (uu___2180_73926.type_of);
          universe_of = (uu___2180_73926.universe_of);
          check_type_of = (uu___2180_73926.check_type_of);
          use_bv_sorts = (uu___2180_73926.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_73926.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_73926.normalized_eff_names);
          fv_delta_depths = (uu___2180_73926.fv_delta_depths);
          proof_ns = (uu___2180_73926.proof_ns);
          synth_hook = (uu___2180_73926.synth_hook);
          splice = (uu___2180_73926.splice);
          postprocess = (uu___2180_73926.postprocess);
          is_native_tactic = (uu___2180_73926.is_native_tactic);
          identifier_info = (uu___2180_73926.identifier_info);
          tc_hooks = (uu___2180_73926.tc_hooks);
          dsenv = (uu___2180_73926.dsenv);
          nbe = (uu___2180_73926.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_73940 = env  in
      {
        solver = (uu___2187_73940.solver);
        range = (uu___2187_73940.range);
        curmodule = (uu___2187_73940.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_73940.gamma_sig);
        gamma_cache = (uu___2187_73940.gamma_cache);
        modules = (uu___2187_73940.modules);
        expected_typ = (uu___2187_73940.expected_typ);
        sigtab = (uu___2187_73940.sigtab);
        attrtab = (uu___2187_73940.attrtab);
        is_pattern = (uu___2187_73940.is_pattern);
        instantiate_imp = (uu___2187_73940.instantiate_imp);
        effects = (uu___2187_73940.effects);
        generalize = (uu___2187_73940.generalize);
        letrecs = (uu___2187_73940.letrecs);
        top_level = (uu___2187_73940.top_level);
        check_uvars = (uu___2187_73940.check_uvars);
        use_eq = (uu___2187_73940.use_eq);
        is_iface = (uu___2187_73940.is_iface);
        admit = (uu___2187_73940.admit);
        lax = (uu___2187_73940.lax);
        lax_universes = (uu___2187_73940.lax_universes);
        phase1 = (uu___2187_73940.phase1);
        failhard = (uu___2187_73940.failhard);
        nosynth = (uu___2187_73940.nosynth);
        uvar_subtyping = (uu___2187_73940.uvar_subtyping);
        tc_term = (uu___2187_73940.tc_term);
        type_of = (uu___2187_73940.type_of);
        universe_of = (uu___2187_73940.universe_of);
        check_type_of = (uu___2187_73940.check_type_of);
        use_bv_sorts = (uu___2187_73940.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_73940.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_73940.normalized_eff_names);
        fv_delta_depths = (uu___2187_73940.fv_delta_depths);
        proof_ns = (uu___2187_73940.proof_ns);
        synth_hook = (uu___2187_73940.synth_hook);
        splice = (uu___2187_73940.splice);
        postprocess = (uu___2187_73940.postprocess);
        is_native_tactic = (uu___2187_73940.is_native_tactic);
        identifier_info = (uu___2187_73940.identifier_info);
        tc_hooks = (uu___2187_73940.tc_hooks);
        dsenv = (uu___2187_73940.dsenv);
        nbe = (uu___2187_73940.nbe)
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
            (let uu___2200_73998 = env  in
             {
               solver = (uu___2200_73998.solver);
               range = (uu___2200_73998.range);
               curmodule = (uu___2200_73998.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_73998.gamma_sig);
               gamma_cache = (uu___2200_73998.gamma_cache);
               modules = (uu___2200_73998.modules);
               expected_typ = (uu___2200_73998.expected_typ);
               sigtab = (uu___2200_73998.sigtab);
               attrtab = (uu___2200_73998.attrtab);
               is_pattern = (uu___2200_73998.is_pattern);
               instantiate_imp = (uu___2200_73998.instantiate_imp);
               effects = (uu___2200_73998.effects);
               generalize = (uu___2200_73998.generalize);
               letrecs = (uu___2200_73998.letrecs);
               top_level = (uu___2200_73998.top_level);
               check_uvars = (uu___2200_73998.check_uvars);
               use_eq = (uu___2200_73998.use_eq);
               is_iface = (uu___2200_73998.is_iface);
               admit = (uu___2200_73998.admit);
               lax = (uu___2200_73998.lax);
               lax_universes = (uu___2200_73998.lax_universes);
               phase1 = (uu___2200_73998.phase1);
               failhard = (uu___2200_73998.failhard);
               nosynth = (uu___2200_73998.nosynth);
               uvar_subtyping = (uu___2200_73998.uvar_subtyping);
               tc_term = (uu___2200_73998.tc_term);
               type_of = (uu___2200_73998.type_of);
               universe_of = (uu___2200_73998.universe_of);
               check_type_of = (uu___2200_73998.check_type_of);
               use_bv_sorts = (uu___2200_73998.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_73998.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_73998.normalized_eff_names);
               fv_delta_depths = (uu___2200_73998.fv_delta_depths);
               proof_ns = (uu___2200_73998.proof_ns);
               synth_hook = (uu___2200_73998.synth_hook);
               splice = (uu___2200_73998.splice);
               postprocess = (uu___2200_73998.postprocess);
               is_native_tactic = (uu___2200_73998.is_native_tactic);
               identifier_info = (uu___2200_73998.identifier_info);
               tc_hooks = (uu___2200_73998.tc_hooks);
               dsenv = (uu___2200_73998.dsenv);
               nbe = (uu___2200_73998.nbe)
             }))
    | uu____73999 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____74028  ->
             match uu____74028 with | (x,uu____74036) -> push_bv env1 x) env
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
            let uu___2214_74071 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_74071.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_74071.FStar_Syntax_Syntax.index);
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
      (let uu___2225_74113 = env  in
       {
         solver = (uu___2225_74113.solver);
         range = (uu___2225_74113.range);
         curmodule = (uu___2225_74113.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_74113.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_74113.sigtab);
         attrtab = (uu___2225_74113.attrtab);
         is_pattern = (uu___2225_74113.is_pattern);
         instantiate_imp = (uu___2225_74113.instantiate_imp);
         effects = (uu___2225_74113.effects);
         generalize = (uu___2225_74113.generalize);
         letrecs = (uu___2225_74113.letrecs);
         top_level = (uu___2225_74113.top_level);
         check_uvars = (uu___2225_74113.check_uvars);
         use_eq = (uu___2225_74113.use_eq);
         is_iface = (uu___2225_74113.is_iface);
         admit = (uu___2225_74113.admit);
         lax = (uu___2225_74113.lax);
         lax_universes = (uu___2225_74113.lax_universes);
         phase1 = (uu___2225_74113.phase1);
         failhard = (uu___2225_74113.failhard);
         nosynth = (uu___2225_74113.nosynth);
         uvar_subtyping = (uu___2225_74113.uvar_subtyping);
         tc_term = (uu___2225_74113.tc_term);
         type_of = (uu___2225_74113.type_of);
         universe_of = (uu___2225_74113.universe_of);
         check_type_of = (uu___2225_74113.check_type_of);
         use_bv_sorts = (uu___2225_74113.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_74113.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_74113.normalized_eff_names);
         fv_delta_depths = (uu___2225_74113.fv_delta_depths);
         proof_ns = (uu___2225_74113.proof_ns);
         synth_hook = (uu___2225_74113.synth_hook);
         splice = (uu___2225_74113.splice);
         postprocess = (uu___2225_74113.postprocess);
         is_native_tactic = (uu___2225_74113.is_native_tactic);
         identifier_info = (uu___2225_74113.identifier_info);
         tc_hooks = (uu___2225_74113.tc_hooks);
         dsenv = (uu___2225_74113.dsenv);
         nbe = (uu___2225_74113.nbe)
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
        let uu____74157 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____74157 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____74185 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____74185)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_74201 = env  in
      {
        solver = (uu___2240_74201.solver);
        range = (uu___2240_74201.range);
        curmodule = (uu___2240_74201.curmodule);
        gamma = (uu___2240_74201.gamma);
        gamma_sig = (uu___2240_74201.gamma_sig);
        gamma_cache = (uu___2240_74201.gamma_cache);
        modules = (uu___2240_74201.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_74201.sigtab);
        attrtab = (uu___2240_74201.attrtab);
        is_pattern = (uu___2240_74201.is_pattern);
        instantiate_imp = (uu___2240_74201.instantiate_imp);
        effects = (uu___2240_74201.effects);
        generalize = (uu___2240_74201.generalize);
        letrecs = (uu___2240_74201.letrecs);
        top_level = (uu___2240_74201.top_level);
        check_uvars = (uu___2240_74201.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_74201.is_iface);
        admit = (uu___2240_74201.admit);
        lax = (uu___2240_74201.lax);
        lax_universes = (uu___2240_74201.lax_universes);
        phase1 = (uu___2240_74201.phase1);
        failhard = (uu___2240_74201.failhard);
        nosynth = (uu___2240_74201.nosynth);
        uvar_subtyping = (uu___2240_74201.uvar_subtyping);
        tc_term = (uu___2240_74201.tc_term);
        type_of = (uu___2240_74201.type_of);
        universe_of = (uu___2240_74201.universe_of);
        check_type_of = (uu___2240_74201.check_type_of);
        use_bv_sorts = (uu___2240_74201.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_74201.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_74201.normalized_eff_names);
        fv_delta_depths = (uu___2240_74201.fv_delta_depths);
        proof_ns = (uu___2240_74201.proof_ns);
        synth_hook = (uu___2240_74201.synth_hook);
        splice = (uu___2240_74201.splice);
        postprocess = (uu___2240_74201.postprocess);
        is_native_tactic = (uu___2240_74201.is_native_tactic);
        identifier_info = (uu___2240_74201.identifier_info);
        tc_hooks = (uu___2240_74201.tc_hooks);
        dsenv = (uu___2240_74201.dsenv);
        nbe = (uu___2240_74201.nbe)
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
    let uu____74232 = expected_typ env_  in
    ((let uu___2247_74238 = env_  in
      {
        solver = (uu___2247_74238.solver);
        range = (uu___2247_74238.range);
        curmodule = (uu___2247_74238.curmodule);
        gamma = (uu___2247_74238.gamma);
        gamma_sig = (uu___2247_74238.gamma_sig);
        gamma_cache = (uu___2247_74238.gamma_cache);
        modules = (uu___2247_74238.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_74238.sigtab);
        attrtab = (uu___2247_74238.attrtab);
        is_pattern = (uu___2247_74238.is_pattern);
        instantiate_imp = (uu___2247_74238.instantiate_imp);
        effects = (uu___2247_74238.effects);
        generalize = (uu___2247_74238.generalize);
        letrecs = (uu___2247_74238.letrecs);
        top_level = (uu___2247_74238.top_level);
        check_uvars = (uu___2247_74238.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_74238.is_iface);
        admit = (uu___2247_74238.admit);
        lax = (uu___2247_74238.lax);
        lax_universes = (uu___2247_74238.lax_universes);
        phase1 = (uu___2247_74238.phase1);
        failhard = (uu___2247_74238.failhard);
        nosynth = (uu___2247_74238.nosynth);
        uvar_subtyping = (uu___2247_74238.uvar_subtyping);
        tc_term = (uu___2247_74238.tc_term);
        type_of = (uu___2247_74238.type_of);
        universe_of = (uu___2247_74238.universe_of);
        check_type_of = (uu___2247_74238.check_type_of);
        use_bv_sorts = (uu___2247_74238.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_74238.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_74238.normalized_eff_names);
        fv_delta_depths = (uu___2247_74238.fv_delta_depths);
        proof_ns = (uu___2247_74238.proof_ns);
        synth_hook = (uu___2247_74238.synth_hook);
        splice = (uu___2247_74238.splice);
        postprocess = (uu___2247_74238.postprocess);
        is_native_tactic = (uu___2247_74238.is_native_tactic);
        identifier_info = (uu___2247_74238.identifier_info);
        tc_hooks = (uu___2247_74238.tc_hooks);
        dsenv = (uu___2247_74238.dsenv);
        nbe = (uu___2247_74238.nbe)
      }), uu____74232)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____74250 =
      let uu____74253 = FStar_Ident.id_of_text ""  in [uu____74253]  in
    FStar_Ident.lid_of_ids uu____74250  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____74260 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____74260
        then
          let uu____74265 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____74265 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_74293 = env  in
       {
         solver = (uu___2255_74293.solver);
         range = (uu___2255_74293.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_74293.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_74293.expected_typ);
         sigtab = (uu___2255_74293.sigtab);
         attrtab = (uu___2255_74293.attrtab);
         is_pattern = (uu___2255_74293.is_pattern);
         instantiate_imp = (uu___2255_74293.instantiate_imp);
         effects = (uu___2255_74293.effects);
         generalize = (uu___2255_74293.generalize);
         letrecs = (uu___2255_74293.letrecs);
         top_level = (uu___2255_74293.top_level);
         check_uvars = (uu___2255_74293.check_uvars);
         use_eq = (uu___2255_74293.use_eq);
         is_iface = (uu___2255_74293.is_iface);
         admit = (uu___2255_74293.admit);
         lax = (uu___2255_74293.lax);
         lax_universes = (uu___2255_74293.lax_universes);
         phase1 = (uu___2255_74293.phase1);
         failhard = (uu___2255_74293.failhard);
         nosynth = (uu___2255_74293.nosynth);
         uvar_subtyping = (uu___2255_74293.uvar_subtyping);
         tc_term = (uu___2255_74293.tc_term);
         type_of = (uu___2255_74293.type_of);
         universe_of = (uu___2255_74293.universe_of);
         check_type_of = (uu___2255_74293.check_type_of);
         use_bv_sorts = (uu___2255_74293.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_74293.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_74293.normalized_eff_names);
         fv_delta_depths = (uu___2255_74293.fv_delta_depths);
         proof_ns = (uu___2255_74293.proof_ns);
         synth_hook = (uu___2255_74293.synth_hook);
         splice = (uu___2255_74293.splice);
         postprocess = (uu___2255_74293.postprocess);
         is_native_tactic = (uu___2255_74293.is_native_tactic);
         identifier_info = (uu___2255_74293.identifier_info);
         tc_hooks = (uu___2255_74293.tc_hooks);
         dsenv = (uu___2255_74293.dsenv);
         nbe = (uu___2255_74293.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74345)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74349,(uu____74350,t)))::tl1
          ->
          let uu____74371 =
            let uu____74374 = FStar_Syntax_Free.uvars t  in
            ext out uu____74374  in
          aux uu____74371 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74377;
            FStar_Syntax_Syntax.index = uu____74378;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74386 =
            let uu____74389 = FStar_Syntax_Free.uvars t  in
            ext out uu____74389  in
          aux uu____74386 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74447)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74451,(uu____74452,t)))::tl1
          ->
          let uu____74473 =
            let uu____74476 = FStar_Syntax_Free.univs t  in
            ext out uu____74476  in
          aux uu____74473 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74479;
            FStar_Syntax_Syntax.index = uu____74480;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74488 =
            let uu____74491 = FStar_Syntax_Free.univs t  in
            ext out uu____74491  in
          aux uu____74488 tl1
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
          let uu____74553 = FStar_Util.set_add uname out  in
          aux uu____74553 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74556,(uu____74557,t)))::tl1
          ->
          let uu____74578 =
            let uu____74581 = FStar_Syntax_Free.univnames t  in
            ext out uu____74581  in
          aux uu____74578 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74584;
            FStar_Syntax_Syntax.index = uu____74585;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74593 =
            let uu____74596 = FStar_Syntax_Free.univnames t  in
            ext out uu____74596  in
          aux uu____74593 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_74617  ->
            match uu___457_74617 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____74621 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____74634 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____74645 =
      let uu____74654 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____74654
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____74645 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____74702 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_74715  ->
              match uu___458_74715 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____74718 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____74718
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____74724) ->
                  let uu____74741 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____74741))
       in
    FStar_All.pipe_right uu____74702 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_74755  ->
    match uu___459_74755 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____74761 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____74761
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____74784  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____74839) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____74872,uu____74873) -> false  in
      let uu____74887 =
        FStar_List.tryFind
          (fun uu____74909  ->
             match uu____74909 with | (p,uu____74920) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____74887 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____74939,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____74969 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____74969
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_74991 = e  in
        {
          solver = (uu___2398_74991.solver);
          range = (uu___2398_74991.range);
          curmodule = (uu___2398_74991.curmodule);
          gamma = (uu___2398_74991.gamma);
          gamma_sig = (uu___2398_74991.gamma_sig);
          gamma_cache = (uu___2398_74991.gamma_cache);
          modules = (uu___2398_74991.modules);
          expected_typ = (uu___2398_74991.expected_typ);
          sigtab = (uu___2398_74991.sigtab);
          attrtab = (uu___2398_74991.attrtab);
          is_pattern = (uu___2398_74991.is_pattern);
          instantiate_imp = (uu___2398_74991.instantiate_imp);
          effects = (uu___2398_74991.effects);
          generalize = (uu___2398_74991.generalize);
          letrecs = (uu___2398_74991.letrecs);
          top_level = (uu___2398_74991.top_level);
          check_uvars = (uu___2398_74991.check_uvars);
          use_eq = (uu___2398_74991.use_eq);
          is_iface = (uu___2398_74991.is_iface);
          admit = (uu___2398_74991.admit);
          lax = (uu___2398_74991.lax);
          lax_universes = (uu___2398_74991.lax_universes);
          phase1 = (uu___2398_74991.phase1);
          failhard = (uu___2398_74991.failhard);
          nosynth = (uu___2398_74991.nosynth);
          uvar_subtyping = (uu___2398_74991.uvar_subtyping);
          tc_term = (uu___2398_74991.tc_term);
          type_of = (uu___2398_74991.type_of);
          universe_of = (uu___2398_74991.universe_of);
          check_type_of = (uu___2398_74991.check_type_of);
          use_bv_sorts = (uu___2398_74991.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_74991.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_74991.normalized_eff_names);
          fv_delta_depths = (uu___2398_74991.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_74991.synth_hook);
          splice = (uu___2398_74991.splice);
          postprocess = (uu___2398_74991.postprocess);
          is_native_tactic = (uu___2398_74991.is_native_tactic);
          identifier_info = (uu___2398_74991.identifier_info);
          tc_hooks = (uu___2398_74991.tc_hooks);
          dsenv = (uu___2398_74991.dsenv);
          nbe = (uu___2398_74991.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_75039 = e  in
      {
        solver = (uu___2407_75039.solver);
        range = (uu___2407_75039.range);
        curmodule = (uu___2407_75039.curmodule);
        gamma = (uu___2407_75039.gamma);
        gamma_sig = (uu___2407_75039.gamma_sig);
        gamma_cache = (uu___2407_75039.gamma_cache);
        modules = (uu___2407_75039.modules);
        expected_typ = (uu___2407_75039.expected_typ);
        sigtab = (uu___2407_75039.sigtab);
        attrtab = (uu___2407_75039.attrtab);
        is_pattern = (uu___2407_75039.is_pattern);
        instantiate_imp = (uu___2407_75039.instantiate_imp);
        effects = (uu___2407_75039.effects);
        generalize = (uu___2407_75039.generalize);
        letrecs = (uu___2407_75039.letrecs);
        top_level = (uu___2407_75039.top_level);
        check_uvars = (uu___2407_75039.check_uvars);
        use_eq = (uu___2407_75039.use_eq);
        is_iface = (uu___2407_75039.is_iface);
        admit = (uu___2407_75039.admit);
        lax = (uu___2407_75039.lax);
        lax_universes = (uu___2407_75039.lax_universes);
        phase1 = (uu___2407_75039.phase1);
        failhard = (uu___2407_75039.failhard);
        nosynth = (uu___2407_75039.nosynth);
        uvar_subtyping = (uu___2407_75039.uvar_subtyping);
        tc_term = (uu___2407_75039.tc_term);
        type_of = (uu___2407_75039.type_of);
        universe_of = (uu___2407_75039.universe_of);
        check_type_of = (uu___2407_75039.check_type_of);
        use_bv_sorts = (uu___2407_75039.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_75039.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_75039.normalized_eff_names);
        fv_delta_depths = (uu___2407_75039.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_75039.synth_hook);
        splice = (uu___2407_75039.splice);
        postprocess = (uu___2407_75039.postprocess);
        is_native_tactic = (uu___2407_75039.is_native_tactic);
        identifier_info = (uu___2407_75039.identifier_info);
        tc_hooks = (uu___2407_75039.tc_hooks);
        dsenv = (uu___2407_75039.dsenv);
        nbe = (uu___2407_75039.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____75055 = FStar_Syntax_Free.names t  in
      let uu____75058 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____75055 uu____75058
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____75081 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____75081
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____75091 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____75091
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____75112 =
      match uu____75112 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____75132 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____75132)
       in
    let uu____75140 =
      let uu____75144 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____75144 FStar_List.rev  in
    FStar_All.pipe_right uu____75140 (FStar_String.concat " ")
  
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
                  (let uu____75214 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____75214 with
                   | FStar_Pervasives_Native.Some uu____75218 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____75221 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____75231;
        univ_ineqs = uu____75232; implicits = uu____75233;_} -> true
    | uu____75245 -> false
  
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
          let uu___2451_75276 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_75276.deferred);
            univ_ineqs = (uu___2451_75276.univ_ineqs);
            implicits = (uu___2451_75276.implicits)
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
          let uu____75315 = FStar_Options.defensive ()  in
          if uu____75315
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____75321 =
              let uu____75323 =
                let uu____75325 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____75325  in
              Prims.op_Negation uu____75323  in
            (if uu____75321
             then
               let uu____75332 =
                 let uu____75338 =
                   let uu____75340 = FStar_Syntax_Print.term_to_string t  in
                   let uu____75342 =
                     let uu____75344 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____75344
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____75340 uu____75342
                    in
                 (FStar_Errors.Warning_Defensive, uu____75338)  in
               FStar_Errors.log_issue rng uu____75332
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
          let uu____75384 =
            let uu____75386 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75386  in
          if uu____75384
          then ()
          else
            (let uu____75391 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____75391 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____75417 =
            let uu____75419 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75419  in
          if uu____75417
          then ()
          else
            (let uu____75424 = bound_vars e  in
             def_check_closed_in rng msg uu____75424 t)
  
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
          let uu___2488_75463 = g  in
          let uu____75464 =
            let uu____75465 =
              let uu____75466 =
                let uu____75473 =
                  let uu____75474 =
                    let uu____75491 =
                      let uu____75502 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____75502]  in
                    (f, uu____75491)  in
                  FStar_Syntax_Syntax.Tm_app uu____75474  in
                FStar_Syntax_Syntax.mk uu____75473  in
              uu____75466 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _75539  -> FStar_TypeChecker_Common.NonTrivial _75539)
              uu____75465
             in
          {
            guard_f = uu____75464;
            deferred = (uu___2488_75463.deferred);
            univ_ineqs = (uu___2488_75463.univ_ineqs);
            implicits = (uu___2488_75463.implicits)
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
          let uu___2495_75557 = g  in
          let uu____75558 =
            let uu____75559 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75559  in
          {
            guard_f = uu____75558;
            deferred = (uu___2495_75557.deferred);
            univ_ineqs = (uu___2495_75557.univ_ineqs);
            implicits = (uu___2495_75557.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_75576 = g  in
          let uu____75577 =
            let uu____75578 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____75578  in
          {
            guard_f = uu____75577;
            deferred = (uu___2500_75576.deferred);
            univ_ineqs = (uu___2500_75576.univ_ineqs);
            implicits = (uu___2500_75576.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_75580 = g  in
          let uu____75581 =
            let uu____75582 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75582  in
          {
            guard_f = uu____75581;
            deferred = (uu___2504_75580.deferred);
            univ_ineqs = (uu___2504_75580.univ_ineqs);
            implicits = (uu___2504_75580.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____75589 ->
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
          let uu____75606 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____75606
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____75613 =
      let uu____75614 = FStar_Syntax_Util.unmeta t  in
      uu____75614.FStar_Syntax_Syntax.n  in
    match uu____75613 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____75618 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____75661 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____75661;
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
                       let uu____75756 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____75756
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_75763 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_75763.deferred);
              univ_ineqs = (uu___2559_75763.univ_ineqs);
              implicits = (uu___2559_75763.implicits)
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
               let uu____75797 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____75797
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
            let uu___2574_75824 = g  in
            let uu____75825 =
              let uu____75826 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____75826  in
            {
              guard_f = uu____75825;
              deferred = (uu___2574_75824.deferred);
              univ_ineqs = (uu___2574_75824.univ_ineqs);
              implicits = (uu___2574_75824.implicits)
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
              let uu____75884 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____75884 with
              | FStar_Pervasives_Native.Some
                  (uu____75909::(tm,uu____75911)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____75975 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____75993 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____75993;
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
                      let uu___2596_76025 = trivial_guard  in
                      {
                        guard_f = (uu___2596_76025.guard_f);
                        deferred = (uu___2596_76025.deferred);
                        univ_ineqs = (uu___2596_76025.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____76043  -> ());
    push = (fun uu____76045  -> ());
    pop = (fun uu____76048  -> ());
    snapshot =
      (fun uu____76051  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____76070  -> fun uu____76071  -> ());
    encode_sig = (fun uu____76086  -> fun uu____76087  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____76093 =
             let uu____76100 = FStar_Options.peek ()  in (e, g, uu____76100)
              in
           [uu____76093]);
    solve = (fun uu____76116  -> fun uu____76117  -> fun uu____76118  -> ());
    finish = (fun uu____76125  -> ());
    refresh = (fun uu____76127  -> ())
  } 