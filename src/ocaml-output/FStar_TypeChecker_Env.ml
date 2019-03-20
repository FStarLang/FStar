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
    match projectee with | Beta  -> true | uu____51458 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____51469 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____51480 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____51492 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____51510 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____51521 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____51532 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____51543 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____51554 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____51565 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____51577 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____51598 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____51625 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____51652 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____51676 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____51687 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____51698 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____51709 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____51720 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____51731 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____51742 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____51753 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____51764 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____51775 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____51786 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____51797 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____51808 -> false
  
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
      | uu____51868 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____51894 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____51905 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____51916 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____51928 -> false
  
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
           (fun uu___446_63145  ->
              match uu___446_63145 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____63148 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____63148  in
                  let uu____63149 =
                    let uu____63150 = FStar_Syntax_Subst.compress y  in
                    uu____63150.FStar_Syntax_Syntax.n  in
                  (match uu____63149 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____63154 =
                         let uu___775_63155 = y1  in
                         let uu____63156 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_63155.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_63155.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____63156
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____63154
                   | uu____63159 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_63173 = env  in
      let uu____63174 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_63173.solver);
        range = (uu___781_63173.range);
        curmodule = (uu___781_63173.curmodule);
        gamma = uu____63174;
        gamma_sig = (uu___781_63173.gamma_sig);
        gamma_cache = (uu___781_63173.gamma_cache);
        modules = (uu___781_63173.modules);
        expected_typ = (uu___781_63173.expected_typ);
        sigtab = (uu___781_63173.sigtab);
        attrtab = (uu___781_63173.attrtab);
        is_pattern = (uu___781_63173.is_pattern);
        instantiate_imp = (uu___781_63173.instantiate_imp);
        effects = (uu___781_63173.effects);
        generalize = (uu___781_63173.generalize);
        letrecs = (uu___781_63173.letrecs);
        top_level = (uu___781_63173.top_level);
        check_uvars = (uu___781_63173.check_uvars);
        use_eq = (uu___781_63173.use_eq);
        is_iface = (uu___781_63173.is_iface);
        admit = (uu___781_63173.admit);
        lax = (uu___781_63173.lax);
        lax_universes = (uu___781_63173.lax_universes);
        phase1 = (uu___781_63173.phase1);
        failhard = (uu___781_63173.failhard);
        nosynth = (uu___781_63173.nosynth);
        uvar_subtyping = (uu___781_63173.uvar_subtyping);
        tc_term = (uu___781_63173.tc_term);
        type_of = (uu___781_63173.type_of);
        universe_of = (uu___781_63173.universe_of);
        check_type_of = (uu___781_63173.check_type_of);
        use_bv_sorts = (uu___781_63173.use_bv_sorts);
        qtbl_name_and_index = (uu___781_63173.qtbl_name_and_index);
        normalized_eff_names = (uu___781_63173.normalized_eff_names);
        fv_delta_depths = (uu___781_63173.fv_delta_depths);
        proof_ns = (uu___781_63173.proof_ns);
        synth_hook = (uu___781_63173.synth_hook);
        splice = (uu___781_63173.splice);
        postprocess = (uu___781_63173.postprocess);
        is_native_tactic = (uu___781_63173.is_native_tactic);
        identifier_info = (uu___781_63173.identifier_info);
        tc_hooks = (uu___781_63173.tc_hooks);
        dsenv = (uu___781_63173.dsenv);
        nbe = (uu___781_63173.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____63182  -> fun uu____63183  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_63205 = env  in
      {
        solver = (uu___788_63205.solver);
        range = (uu___788_63205.range);
        curmodule = (uu___788_63205.curmodule);
        gamma = (uu___788_63205.gamma);
        gamma_sig = (uu___788_63205.gamma_sig);
        gamma_cache = (uu___788_63205.gamma_cache);
        modules = (uu___788_63205.modules);
        expected_typ = (uu___788_63205.expected_typ);
        sigtab = (uu___788_63205.sigtab);
        attrtab = (uu___788_63205.attrtab);
        is_pattern = (uu___788_63205.is_pattern);
        instantiate_imp = (uu___788_63205.instantiate_imp);
        effects = (uu___788_63205.effects);
        generalize = (uu___788_63205.generalize);
        letrecs = (uu___788_63205.letrecs);
        top_level = (uu___788_63205.top_level);
        check_uvars = (uu___788_63205.check_uvars);
        use_eq = (uu___788_63205.use_eq);
        is_iface = (uu___788_63205.is_iface);
        admit = (uu___788_63205.admit);
        lax = (uu___788_63205.lax);
        lax_universes = (uu___788_63205.lax_universes);
        phase1 = (uu___788_63205.phase1);
        failhard = (uu___788_63205.failhard);
        nosynth = (uu___788_63205.nosynth);
        uvar_subtyping = (uu___788_63205.uvar_subtyping);
        tc_term = (uu___788_63205.tc_term);
        type_of = (uu___788_63205.type_of);
        universe_of = (uu___788_63205.universe_of);
        check_type_of = (uu___788_63205.check_type_of);
        use_bv_sorts = (uu___788_63205.use_bv_sorts);
        qtbl_name_and_index = (uu___788_63205.qtbl_name_and_index);
        normalized_eff_names = (uu___788_63205.normalized_eff_names);
        fv_delta_depths = (uu___788_63205.fv_delta_depths);
        proof_ns = (uu___788_63205.proof_ns);
        synth_hook = (uu___788_63205.synth_hook);
        splice = (uu___788_63205.splice);
        postprocess = (uu___788_63205.postprocess);
        is_native_tactic = (uu___788_63205.is_native_tactic);
        identifier_info = (uu___788_63205.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_63205.dsenv);
        nbe = (uu___788_63205.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_63217 = e  in
      let uu____63218 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_63217.solver);
        range = (uu___792_63217.range);
        curmodule = (uu___792_63217.curmodule);
        gamma = (uu___792_63217.gamma);
        gamma_sig = (uu___792_63217.gamma_sig);
        gamma_cache = (uu___792_63217.gamma_cache);
        modules = (uu___792_63217.modules);
        expected_typ = (uu___792_63217.expected_typ);
        sigtab = (uu___792_63217.sigtab);
        attrtab = (uu___792_63217.attrtab);
        is_pattern = (uu___792_63217.is_pattern);
        instantiate_imp = (uu___792_63217.instantiate_imp);
        effects = (uu___792_63217.effects);
        generalize = (uu___792_63217.generalize);
        letrecs = (uu___792_63217.letrecs);
        top_level = (uu___792_63217.top_level);
        check_uvars = (uu___792_63217.check_uvars);
        use_eq = (uu___792_63217.use_eq);
        is_iface = (uu___792_63217.is_iface);
        admit = (uu___792_63217.admit);
        lax = (uu___792_63217.lax);
        lax_universes = (uu___792_63217.lax_universes);
        phase1 = (uu___792_63217.phase1);
        failhard = (uu___792_63217.failhard);
        nosynth = (uu___792_63217.nosynth);
        uvar_subtyping = (uu___792_63217.uvar_subtyping);
        tc_term = (uu___792_63217.tc_term);
        type_of = (uu___792_63217.type_of);
        universe_of = (uu___792_63217.universe_of);
        check_type_of = (uu___792_63217.check_type_of);
        use_bv_sorts = (uu___792_63217.use_bv_sorts);
        qtbl_name_and_index = (uu___792_63217.qtbl_name_and_index);
        normalized_eff_names = (uu___792_63217.normalized_eff_names);
        fv_delta_depths = (uu___792_63217.fv_delta_depths);
        proof_ns = (uu___792_63217.proof_ns);
        synth_hook = (uu___792_63217.synth_hook);
        splice = (uu___792_63217.splice);
        postprocess = (uu___792_63217.postprocess);
        is_native_tactic = (uu___792_63217.is_native_tactic);
        identifier_info = (uu___792_63217.identifier_info);
        tc_hooks = (uu___792_63217.tc_hooks);
        dsenv = uu____63218;
        nbe = (uu___792_63217.nbe)
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
      | (NoDelta ,uu____63247) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____63250,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____63252,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____63255 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____63269 . unit -> 'Auu____63269 FStar_Util.smap =
  fun uu____63276  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____63282 . unit -> 'Auu____63282 FStar_Util.smap =
  fun uu____63289  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____63427 = new_gamma_cache ()  in
                  let uu____63430 = new_sigtab ()  in
                  let uu____63433 = new_sigtab ()  in
                  let uu____63440 =
                    let uu____63455 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____63455, FStar_Pervasives_Native.None)  in
                  let uu____63476 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____63480 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____63484 = FStar_Options.using_facts_from ()  in
                  let uu____63485 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____63488 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____63427;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____63430;
                    attrtab = uu____63433;
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
                    qtbl_name_and_index = uu____63440;
                    normalized_eff_names = uu____63476;
                    fv_delta_depths = uu____63480;
                    proof_ns = uu____63484;
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
                    is_native_tactic = (fun uu____63550  -> false);
                    identifier_info = uu____63485;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____63488;
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
  fun uu____63629  ->
    let uu____63630 = FStar_ST.op_Bang query_indices  in
    match uu____63630 with
    | [] -> failwith "Empty query indices!"
    | uu____63685 ->
        let uu____63695 =
          let uu____63705 =
            let uu____63713 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____63713  in
          let uu____63767 = FStar_ST.op_Bang query_indices  in uu____63705 ::
            uu____63767
           in
        FStar_ST.op_Colon_Equals query_indices uu____63695
  
let (pop_query_indices : unit -> unit) =
  fun uu____63863  ->
    let uu____63864 = FStar_ST.op_Bang query_indices  in
    match uu____63864 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____63991  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____64028  ->
    match uu____64028 with
    | (l,n1) ->
        let uu____64038 = FStar_ST.op_Bang query_indices  in
        (match uu____64038 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____64160 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____64183  ->
    let uu____64184 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____64184
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____64252 =
       let uu____64255 = FStar_ST.op_Bang stack  in env :: uu____64255  in
     FStar_ST.op_Colon_Equals stack uu____64252);
    (let uu___860_64304 = env  in
     let uu____64305 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____64308 = FStar_Util.smap_copy (sigtab env)  in
     let uu____64311 = FStar_Util.smap_copy (attrtab env)  in
     let uu____64318 =
       let uu____64333 =
         let uu____64337 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____64337  in
       let uu____64369 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____64333, uu____64369)  in
     let uu____64418 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____64421 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____64424 =
       let uu____64427 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____64427  in
     {
       solver = (uu___860_64304.solver);
       range = (uu___860_64304.range);
       curmodule = (uu___860_64304.curmodule);
       gamma = (uu___860_64304.gamma);
       gamma_sig = (uu___860_64304.gamma_sig);
       gamma_cache = uu____64305;
       modules = (uu___860_64304.modules);
       expected_typ = (uu___860_64304.expected_typ);
       sigtab = uu____64308;
       attrtab = uu____64311;
       is_pattern = (uu___860_64304.is_pattern);
       instantiate_imp = (uu___860_64304.instantiate_imp);
       effects = (uu___860_64304.effects);
       generalize = (uu___860_64304.generalize);
       letrecs = (uu___860_64304.letrecs);
       top_level = (uu___860_64304.top_level);
       check_uvars = (uu___860_64304.check_uvars);
       use_eq = (uu___860_64304.use_eq);
       is_iface = (uu___860_64304.is_iface);
       admit = (uu___860_64304.admit);
       lax = (uu___860_64304.lax);
       lax_universes = (uu___860_64304.lax_universes);
       phase1 = (uu___860_64304.phase1);
       failhard = (uu___860_64304.failhard);
       nosynth = (uu___860_64304.nosynth);
       uvar_subtyping = (uu___860_64304.uvar_subtyping);
       tc_term = (uu___860_64304.tc_term);
       type_of = (uu___860_64304.type_of);
       universe_of = (uu___860_64304.universe_of);
       check_type_of = (uu___860_64304.check_type_of);
       use_bv_sorts = (uu___860_64304.use_bv_sorts);
       qtbl_name_and_index = uu____64318;
       normalized_eff_names = uu____64418;
       fv_delta_depths = uu____64421;
       proof_ns = (uu___860_64304.proof_ns);
       synth_hook = (uu___860_64304.synth_hook);
       splice = (uu___860_64304.splice);
       postprocess = (uu___860_64304.postprocess);
       is_native_tactic = (uu___860_64304.is_native_tactic);
       identifier_info = uu____64424;
       tc_hooks = (uu___860_64304.tc_hooks);
       dsenv = (uu___860_64304.dsenv);
       nbe = (uu___860_64304.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____64452  ->
    let uu____64453 = FStar_ST.op_Bang stack  in
    match uu____64453 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____64507 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____64597  ->
           let uu____64598 = snapshot_stack env  in
           match uu____64598 with
           | (stack_depth,env1) ->
               let uu____64632 = snapshot_query_indices ()  in
               (match uu____64632 with
                | (query_indices_depth,()) ->
                    let uu____64665 = (env1.solver).snapshot msg  in
                    (match uu____64665 with
                     | (solver_depth,()) ->
                         let uu____64722 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____64722 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_64789 = env1  in
                                 {
                                   solver = (uu___885_64789.solver);
                                   range = (uu___885_64789.range);
                                   curmodule = (uu___885_64789.curmodule);
                                   gamma = (uu___885_64789.gamma);
                                   gamma_sig = (uu___885_64789.gamma_sig);
                                   gamma_cache = (uu___885_64789.gamma_cache);
                                   modules = (uu___885_64789.modules);
                                   expected_typ =
                                     (uu___885_64789.expected_typ);
                                   sigtab = (uu___885_64789.sigtab);
                                   attrtab = (uu___885_64789.attrtab);
                                   is_pattern = (uu___885_64789.is_pattern);
                                   instantiate_imp =
                                     (uu___885_64789.instantiate_imp);
                                   effects = (uu___885_64789.effects);
                                   generalize = (uu___885_64789.generalize);
                                   letrecs = (uu___885_64789.letrecs);
                                   top_level = (uu___885_64789.top_level);
                                   check_uvars = (uu___885_64789.check_uvars);
                                   use_eq = (uu___885_64789.use_eq);
                                   is_iface = (uu___885_64789.is_iface);
                                   admit = (uu___885_64789.admit);
                                   lax = (uu___885_64789.lax);
                                   lax_universes =
                                     (uu___885_64789.lax_universes);
                                   phase1 = (uu___885_64789.phase1);
                                   failhard = (uu___885_64789.failhard);
                                   nosynth = (uu___885_64789.nosynth);
                                   uvar_subtyping =
                                     (uu___885_64789.uvar_subtyping);
                                   tc_term = (uu___885_64789.tc_term);
                                   type_of = (uu___885_64789.type_of);
                                   universe_of = (uu___885_64789.universe_of);
                                   check_type_of =
                                     (uu___885_64789.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_64789.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_64789.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_64789.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_64789.fv_delta_depths);
                                   proof_ns = (uu___885_64789.proof_ns);
                                   synth_hook = (uu___885_64789.synth_hook);
                                   splice = (uu___885_64789.splice);
                                   postprocess = (uu___885_64789.postprocess);
                                   is_native_tactic =
                                     (uu___885_64789.is_native_tactic);
                                   identifier_info =
                                     (uu___885_64789.identifier_info);
                                   tc_hooks = (uu___885_64789.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_64789.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____64823  ->
             let uu____64824 =
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
             match uu____64824 with
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
                             ((let uu____65004 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____65004
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____65020 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____65020
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____65052,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____65094 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____65124  ->
                  match uu____65124 with
                  | (m,uu____65132) -> FStar_Ident.lid_equals l m))
           in
        (match uu____65094 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_65147 = env  in
               {
                 solver = (uu___930_65147.solver);
                 range = (uu___930_65147.range);
                 curmodule = (uu___930_65147.curmodule);
                 gamma = (uu___930_65147.gamma);
                 gamma_sig = (uu___930_65147.gamma_sig);
                 gamma_cache = (uu___930_65147.gamma_cache);
                 modules = (uu___930_65147.modules);
                 expected_typ = (uu___930_65147.expected_typ);
                 sigtab = (uu___930_65147.sigtab);
                 attrtab = (uu___930_65147.attrtab);
                 is_pattern = (uu___930_65147.is_pattern);
                 instantiate_imp = (uu___930_65147.instantiate_imp);
                 effects = (uu___930_65147.effects);
                 generalize = (uu___930_65147.generalize);
                 letrecs = (uu___930_65147.letrecs);
                 top_level = (uu___930_65147.top_level);
                 check_uvars = (uu___930_65147.check_uvars);
                 use_eq = (uu___930_65147.use_eq);
                 is_iface = (uu___930_65147.is_iface);
                 admit = (uu___930_65147.admit);
                 lax = (uu___930_65147.lax);
                 lax_universes = (uu___930_65147.lax_universes);
                 phase1 = (uu___930_65147.phase1);
                 failhard = (uu___930_65147.failhard);
                 nosynth = (uu___930_65147.nosynth);
                 uvar_subtyping = (uu___930_65147.uvar_subtyping);
                 tc_term = (uu___930_65147.tc_term);
                 type_of = (uu___930_65147.type_of);
                 universe_of = (uu___930_65147.universe_of);
                 check_type_of = (uu___930_65147.check_type_of);
                 use_bv_sorts = (uu___930_65147.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_65147.normalized_eff_names);
                 fv_delta_depths = (uu___930_65147.fv_delta_depths);
                 proof_ns = (uu___930_65147.proof_ns);
                 synth_hook = (uu___930_65147.synth_hook);
                 splice = (uu___930_65147.splice);
                 postprocess = (uu___930_65147.postprocess);
                 is_native_tactic = (uu___930_65147.is_native_tactic);
                 identifier_info = (uu___930_65147.identifier_info);
                 tc_hooks = (uu___930_65147.tc_hooks);
                 dsenv = (uu___930_65147.dsenv);
                 nbe = (uu___930_65147.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____65164,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_65180 = env  in
               {
                 solver = (uu___939_65180.solver);
                 range = (uu___939_65180.range);
                 curmodule = (uu___939_65180.curmodule);
                 gamma = (uu___939_65180.gamma);
                 gamma_sig = (uu___939_65180.gamma_sig);
                 gamma_cache = (uu___939_65180.gamma_cache);
                 modules = (uu___939_65180.modules);
                 expected_typ = (uu___939_65180.expected_typ);
                 sigtab = (uu___939_65180.sigtab);
                 attrtab = (uu___939_65180.attrtab);
                 is_pattern = (uu___939_65180.is_pattern);
                 instantiate_imp = (uu___939_65180.instantiate_imp);
                 effects = (uu___939_65180.effects);
                 generalize = (uu___939_65180.generalize);
                 letrecs = (uu___939_65180.letrecs);
                 top_level = (uu___939_65180.top_level);
                 check_uvars = (uu___939_65180.check_uvars);
                 use_eq = (uu___939_65180.use_eq);
                 is_iface = (uu___939_65180.is_iface);
                 admit = (uu___939_65180.admit);
                 lax = (uu___939_65180.lax);
                 lax_universes = (uu___939_65180.lax_universes);
                 phase1 = (uu___939_65180.phase1);
                 failhard = (uu___939_65180.failhard);
                 nosynth = (uu___939_65180.nosynth);
                 uvar_subtyping = (uu___939_65180.uvar_subtyping);
                 tc_term = (uu___939_65180.tc_term);
                 type_of = (uu___939_65180.type_of);
                 universe_of = (uu___939_65180.universe_of);
                 check_type_of = (uu___939_65180.check_type_of);
                 use_bv_sorts = (uu___939_65180.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_65180.normalized_eff_names);
                 fv_delta_depths = (uu___939_65180.fv_delta_depths);
                 proof_ns = (uu___939_65180.proof_ns);
                 synth_hook = (uu___939_65180.synth_hook);
                 splice = (uu___939_65180.splice);
                 postprocess = (uu___939_65180.postprocess);
                 is_native_tactic = (uu___939_65180.is_native_tactic);
                 identifier_info = (uu___939_65180.identifier_info);
                 tc_hooks = (uu___939_65180.tc_hooks);
                 dsenv = (uu___939_65180.dsenv);
                 nbe = (uu___939_65180.nbe)
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
        (let uu___946_65223 = e  in
         {
           solver = (uu___946_65223.solver);
           range = r;
           curmodule = (uu___946_65223.curmodule);
           gamma = (uu___946_65223.gamma);
           gamma_sig = (uu___946_65223.gamma_sig);
           gamma_cache = (uu___946_65223.gamma_cache);
           modules = (uu___946_65223.modules);
           expected_typ = (uu___946_65223.expected_typ);
           sigtab = (uu___946_65223.sigtab);
           attrtab = (uu___946_65223.attrtab);
           is_pattern = (uu___946_65223.is_pattern);
           instantiate_imp = (uu___946_65223.instantiate_imp);
           effects = (uu___946_65223.effects);
           generalize = (uu___946_65223.generalize);
           letrecs = (uu___946_65223.letrecs);
           top_level = (uu___946_65223.top_level);
           check_uvars = (uu___946_65223.check_uvars);
           use_eq = (uu___946_65223.use_eq);
           is_iface = (uu___946_65223.is_iface);
           admit = (uu___946_65223.admit);
           lax = (uu___946_65223.lax);
           lax_universes = (uu___946_65223.lax_universes);
           phase1 = (uu___946_65223.phase1);
           failhard = (uu___946_65223.failhard);
           nosynth = (uu___946_65223.nosynth);
           uvar_subtyping = (uu___946_65223.uvar_subtyping);
           tc_term = (uu___946_65223.tc_term);
           type_of = (uu___946_65223.type_of);
           universe_of = (uu___946_65223.universe_of);
           check_type_of = (uu___946_65223.check_type_of);
           use_bv_sorts = (uu___946_65223.use_bv_sorts);
           qtbl_name_and_index = (uu___946_65223.qtbl_name_and_index);
           normalized_eff_names = (uu___946_65223.normalized_eff_names);
           fv_delta_depths = (uu___946_65223.fv_delta_depths);
           proof_ns = (uu___946_65223.proof_ns);
           synth_hook = (uu___946_65223.synth_hook);
           splice = (uu___946_65223.splice);
           postprocess = (uu___946_65223.postprocess);
           is_native_tactic = (uu___946_65223.is_native_tactic);
           identifier_info = (uu___946_65223.identifier_info);
           tc_hooks = (uu___946_65223.tc_hooks);
           dsenv = (uu___946_65223.dsenv);
           nbe = (uu___946_65223.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____65243 =
        let uu____65244 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____65244 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65243
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____65299 =
          let uu____65300 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____65300 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65299
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____65355 =
          let uu____65356 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____65356 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65355
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____65411 =
        let uu____65412 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____65412 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65411
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_65476 = env  in
      {
        solver = (uu___963_65476.solver);
        range = (uu___963_65476.range);
        curmodule = lid;
        gamma = (uu___963_65476.gamma);
        gamma_sig = (uu___963_65476.gamma_sig);
        gamma_cache = (uu___963_65476.gamma_cache);
        modules = (uu___963_65476.modules);
        expected_typ = (uu___963_65476.expected_typ);
        sigtab = (uu___963_65476.sigtab);
        attrtab = (uu___963_65476.attrtab);
        is_pattern = (uu___963_65476.is_pattern);
        instantiate_imp = (uu___963_65476.instantiate_imp);
        effects = (uu___963_65476.effects);
        generalize = (uu___963_65476.generalize);
        letrecs = (uu___963_65476.letrecs);
        top_level = (uu___963_65476.top_level);
        check_uvars = (uu___963_65476.check_uvars);
        use_eq = (uu___963_65476.use_eq);
        is_iface = (uu___963_65476.is_iface);
        admit = (uu___963_65476.admit);
        lax = (uu___963_65476.lax);
        lax_universes = (uu___963_65476.lax_universes);
        phase1 = (uu___963_65476.phase1);
        failhard = (uu___963_65476.failhard);
        nosynth = (uu___963_65476.nosynth);
        uvar_subtyping = (uu___963_65476.uvar_subtyping);
        tc_term = (uu___963_65476.tc_term);
        type_of = (uu___963_65476.type_of);
        universe_of = (uu___963_65476.universe_of);
        check_type_of = (uu___963_65476.check_type_of);
        use_bv_sorts = (uu___963_65476.use_bv_sorts);
        qtbl_name_and_index = (uu___963_65476.qtbl_name_and_index);
        normalized_eff_names = (uu___963_65476.normalized_eff_names);
        fv_delta_depths = (uu___963_65476.fv_delta_depths);
        proof_ns = (uu___963_65476.proof_ns);
        synth_hook = (uu___963_65476.synth_hook);
        splice = (uu___963_65476.splice);
        postprocess = (uu___963_65476.postprocess);
        is_native_tactic = (uu___963_65476.is_native_tactic);
        identifier_info = (uu___963_65476.identifier_info);
        tc_hooks = (uu___963_65476.tc_hooks);
        dsenv = (uu___963_65476.dsenv);
        nbe = (uu___963_65476.nbe)
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
      let uu____65507 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____65507
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65520 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____65520)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____65535 =
      let uu____65537 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____65537  in
    (FStar_Errors.Fatal_VariableNotFound, uu____65535)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____65546  ->
    let uu____65547 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____65547
  
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
      | ((formals,t),uu____65647) ->
          let vs = mk_univ_subst formals us  in
          let uu____65671 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____65671)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_65688  ->
    match uu___447_65688 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____65714  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____65734 = inst_tscheme t  in
      match uu____65734 with
      | (us,t1) ->
          let uu____65745 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____65745)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____65766  ->
          match uu____65766 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____65788 =
                         let uu____65790 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____65794 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____65798 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____65800 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____65790 uu____65794 uu____65798 uu____65800
                          in
                       failwith uu____65788)
                    else ();
                    (let uu____65805 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____65805))
               | uu____65814 ->
                   let uu____65815 =
                     let uu____65817 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____65817
                      in
                   failwith uu____65815)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____65829 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____65840 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____65851 -> false
  
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
             | ([],uu____65899) -> Maybe
             | (uu____65906,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____65926 -> No  in
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
          let uu____66020 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____66020 with
          | FStar_Pervasives_Native.None  ->
              let uu____66043 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_66087  ->
                     match uu___448_66087 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____66126 = FStar_Ident.lid_equals lid l  in
                         if uu____66126
                         then
                           let uu____66149 =
                             let uu____66168 =
                               let uu____66183 = inst_tscheme t  in
                               FStar_Util.Inl uu____66183  in
                             let uu____66198 = FStar_Ident.range_of_lid l  in
                             (uu____66168, uu____66198)  in
                           FStar_Pervasives_Native.Some uu____66149
                         else FStar_Pervasives_Native.None
                     | uu____66251 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____66043
                (fun uu____66289  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_66298  ->
                        match uu___449_66298 with
                        | (uu____66301,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____66303);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____66304;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____66305;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____66306;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____66307;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____66327 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____66327
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
                                  uu____66379 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____66386 -> cache t  in
                            let uu____66387 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____66387 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____66393 =
                                   let uu____66394 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____66394)
                                    in
                                 maybe_cache uu____66393)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____66465 = find_in_sigtab env lid  in
         match uu____66465 with
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
      let uu____66546 = lookup_qname env lid  in
      match uu____66546 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____66567,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____66681 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____66681 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____66726 =
          let uu____66729 = lookup_attr env1 attr  in se1 :: uu____66729  in
        FStar_Util.smap_add (attrtab env1) attr uu____66726  in
      FStar_List.iter
        (fun attr  ->
           let uu____66739 =
             let uu____66740 = FStar_Syntax_Subst.compress attr  in
             uu____66740.FStar_Syntax_Syntax.n  in
           match uu____66739 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____66744 =
                 let uu____66746 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____66746.FStar_Ident.str  in
               add_one1 env se uu____66744
           | uu____66747 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____66770) ->
          add_sigelts env ses
      | uu____66779 ->
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
            | uu____66794 -> ()))

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
        (fun uu___450_66826  ->
           match uu___450_66826 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____66844 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____66906,lb::[]),uu____66908) ->
            let uu____66917 =
              let uu____66926 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____66935 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____66926, uu____66935)  in
            FStar_Pervasives_Native.Some uu____66917
        | FStar_Syntax_Syntax.Sig_let ((uu____66948,lbs),uu____66950) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____66982 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____66995 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____66995
                     then
                       let uu____67008 =
                         let uu____67017 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____67026 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____67017, uu____67026)  in
                       FStar_Pervasives_Native.Some uu____67008
                     else FStar_Pervasives_Native.None)
        | uu____67049 -> FStar_Pervasives_Native.None
  
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
          let uu____67109 =
            let uu____67118 =
              let uu____67123 =
                let uu____67124 =
                  let uu____67127 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____67127
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____67124)  in
              inst_tscheme1 uu____67123  in
            (uu____67118, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67109
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____67149,uu____67150) ->
          let uu____67155 =
            let uu____67164 =
              let uu____67169 =
                let uu____67170 =
                  let uu____67173 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____67173  in
                (us, uu____67170)  in
              inst_tscheme1 uu____67169  in
            (uu____67164, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67155
      | uu____67192 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____67281 =
          match uu____67281 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____67377,uvs,t,uu____67380,uu____67381,uu____67382);
                      FStar_Syntax_Syntax.sigrng = uu____67383;
                      FStar_Syntax_Syntax.sigquals = uu____67384;
                      FStar_Syntax_Syntax.sigmeta = uu____67385;
                      FStar_Syntax_Syntax.sigattrs = uu____67386;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67409 =
                     let uu____67418 = inst_tscheme1 (uvs, t)  in
                     (uu____67418, rng)  in
                   FStar_Pervasives_Native.Some uu____67409
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____67442;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____67444;
                      FStar_Syntax_Syntax.sigattrs = uu____67445;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67462 =
                     let uu____67464 = in_cur_mod env l  in uu____67464 = Yes
                      in
                   if uu____67462
                   then
                     let uu____67476 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____67476
                      then
                        let uu____67492 =
                          let uu____67501 = inst_tscheme1 (uvs, t)  in
                          (uu____67501, rng)  in
                        FStar_Pervasives_Native.Some uu____67492
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____67534 =
                        let uu____67543 = inst_tscheme1 (uvs, t)  in
                        (uu____67543, rng)  in
                      FStar_Pervasives_Native.Some uu____67534)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67568,uu____67569);
                      FStar_Syntax_Syntax.sigrng = uu____67570;
                      FStar_Syntax_Syntax.sigquals = uu____67571;
                      FStar_Syntax_Syntax.sigmeta = uu____67572;
                      FStar_Syntax_Syntax.sigattrs = uu____67573;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____67614 =
                          let uu____67623 = inst_tscheme1 (uvs, k)  in
                          (uu____67623, rng)  in
                        FStar_Pervasives_Native.Some uu____67614
                    | uu____67644 ->
                        let uu____67645 =
                          let uu____67654 =
                            let uu____67659 =
                              let uu____67660 =
                                let uu____67663 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67663
                                 in
                              (uvs, uu____67660)  in
                            inst_tscheme1 uu____67659  in
                          (uu____67654, rng)  in
                        FStar_Pervasives_Native.Some uu____67645)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67686,uu____67687);
                      FStar_Syntax_Syntax.sigrng = uu____67688;
                      FStar_Syntax_Syntax.sigquals = uu____67689;
                      FStar_Syntax_Syntax.sigmeta = uu____67690;
                      FStar_Syntax_Syntax.sigattrs = uu____67691;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____67733 =
                          let uu____67742 = inst_tscheme_with (uvs, k) us  in
                          (uu____67742, rng)  in
                        FStar_Pervasives_Native.Some uu____67733
                    | uu____67763 ->
                        let uu____67764 =
                          let uu____67773 =
                            let uu____67778 =
                              let uu____67779 =
                                let uu____67782 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67782
                                 in
                              (uvs, uu____67779)  in
                            inst_tscheme_with uu____67778 us  in
                          (uu____67773, rng)  in
                        FStar_Pervasives_Native.Some uu____67764)
               | FStar_Util.Inr se ->
                   let uu____67818 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____67839;
                          FStar_Syntax_Syntax.sigrng = uu____67840;
                          FStar_Syntax_Syntax.sigquals = uu____67841;
                          FStar_Syntax_Syntax.sigmeta = uu____67842;
                          FStar_Syntax_Syntax.sigattrs = uu____67843;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____67858 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____67818
                     (FStar_Util.map_option
                        (fun uu____67906  ->
                           match uu____67906 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____67937 =
          let uu____67948 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____67948 mapper  in
        match uu____67937 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____68022 =
              let uu____68033 =
                let uu____68040 =
                  let uu___1290_68043 = t  in
                  let uu____68044 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_68043.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____68044;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_68043.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____68040)  in
              (uu____68033, r)  in
            FStar_Pervasives_Native.Some uu____68022
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____68093 = lookup_qname env l  in
      match uu____68093 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____68114 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____68168 = try_lookup_bv env bv  in
      match uu____68168 with
      | FStar_Pervasives_Native.None  ->
          let uu____68183 = variable_not_found bv  in
          FStar_Errors.raise_error uu____68183 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____68199 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____68200 =
            let uu____68201 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____68201  in
          (uu____68199, uu____68200)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____68223 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____68223 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____68289 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____68289  in
          let uu____68290 =
            let uu____68299 =
              let uu____68304 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____68304)  in
            (uu____68299, r1)  in
          FStar_Pervasives_Native.Some uu____68290
  
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
        let uu____68339 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____68339 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____68372,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____68397 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____68397  in
            let uu____68398 =
              let uu____68403 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____68403, r1)  in
            FStar_Pervasives_Native.Some uu____68398
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____68427 = try_lookup_lid env l  in
      match uu____68427 with
      | FStar_Pervasives_Native.None  ->
          let uu____68454 = name_not_found l  in
          let uu____68460 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____68454 uu____68460
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_68503  ->
              match uu___451_68503 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____68507 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____68528 = lookup_qname env lid  in
      match uu____68528 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68537,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68540;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____68542;
              FStar_Syntax_Syntax.sigattrs = uu____68543;_},FStar_Pervasives_Native.None
            ),uu____68544)
          ->
          let uu____68593 =
            let uu____68600 =
              let uu____68601 =
                let uu____68604 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____68604 t  in
              (uvs, uu____68601)  in
            (uu____68600, q)  in
          FStar_Pervasives_Native.Some uu____68593
      | uu____68617 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68639 = lookup_qname env lid  in
      match uu____68639 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68644,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68647;
              FStar_Syntax_Syntax.sigquals = uu____68648;
              FStar_Syntax_Syntax.sigmeta = uu____68649;
              FStar_Syntax_Syntax.sigattrs = uu____68650;_},FStar_Pervasives_Native.None
            ),uu____68651)
          ->
          let uu____68700 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68700 (uvs, t)
      | uu____68705 ->
          let uu____68706 = name_not_found lid  in
          let uu____68712 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68706 uu____68712
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68732 = lookup_qname env lid  in
      match uu____68732 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68737,uvs,t,uu____68740,uu____68741,uu____68742);
              FStar_Syntax_Syntax.sigrng = uu____68743;
              FStar_Syntax_Syntax.sigquals = uu____68744;
              FStar_Syntax_Syntax.sigmeta = uu____68745;
              FStar_Syntax_Syntax.sigattrs = uu____68746;_},FStar_Pervasives_Native.None
            ),uu____68747)
          ->
          let uu____68802 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68802 (uvs, t)
      | uu____68807 ->
          let uu____68808 = name_not_found lid  in
          let uu____68814 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68808 uu____68814
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____68837 = lookup_qname env lid  in
      match uu____68837 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____68845,uu____68846,uu____68847,uu____68848,uu____68849,dcs);
              FStar_Syntax_Syntax.sigrng = uu____68851;
              FStar_Syntax_Syntax.sigquals = uu____68852;
              FStar_Syntax_Syntax.sigmeta = uu____68853;
              FStar_Syntax_Syntax.sigattrs = uu____68854;_},uu____68855),uu____68856)
          -> (true, dcs)
      | uu____68919 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____68935 = lookup_qname env lid  in
      match uu____68935 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68936,uu____68937,uu____68938,l,uu____68940,uu____68941);
              FStar_Syntax_Syntax.sigrng = uu____68942;
              FStar_Syntax_Syntax.sigquals = uu____68943;
              FStar_Syntax_Syntax.sigmeta = uu____68944;
              FStar_Syntax_Syntax.sigattrs = uu____68945;_},uu____68946),uu____68947)
          -> l
      | uu____69004 ->
          let uu____69005 =
            let uu____69007 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____69007  in
          failwith uu____69005
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69077)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69134) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69158 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69158
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69193 -> FStar_Pervasives_Native.None)
          | uu____69202 -> FStar_Pervasives_Native.None
  
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
        let uu____69264 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____69264
  
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
        let uu____69297 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____69297
  
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
             (FStar_Util.Inl uu____69349,uu____69350) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____69399),uu____69400) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____69449 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____69467 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____69477 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____69494 ->
                  let uu____69501 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____69501
              | FStar_Syntax_Syntax.Sig_let ((uu____69502,lbs),uu____69504)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____69520 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____69520
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____69527 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____69535 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____69536 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____69543 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69544 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____69545 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69546 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____69559 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____69577 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____69577
           (fun d_opt  ->
              let uu____69590 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____69590
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____69600 =
                   let uu____69603 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____69603  in
                 match uu____69600 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____69604 =
                       let uu____69606 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____69606
                        in
                     failwith uu____69604
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____69611 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____69611
                       then
                         let uu____69614 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____69616 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____69618 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____69614 uu____69616 uu____69618
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
        (FStar_Util.Inr (se,uu____69643),uu____69644) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____69693 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____69715),uu____69716) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____69765 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____69787 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____69787
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____69810 = lookup_attrs_of_lid env fv_lid1  in
        match uu____69810 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____69834 =
                      let uu____69835 = FStar_Syntax_Util.un_uinst tm  in
                      uu____69835.FStar_Syntax_Syntax.n  in
                    match uu____69834 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____69840 -> false))
  
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
      let uu____69874 = lookup_qname env ftv  in
      match uu____69874 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69878) ->
          let uu____69923 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____69923 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____69944,t),r) ->
               let uu____69959 =
                 let uu____69960 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____69960 t  in
               FStar_Pervasives_Native.Some uu____69959)
      | uu____69961 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____69973 = try_lookup_effect_lid env ftv  in
      match uu____69973 with
      | FStar_Pervasives_Native.None  ->
          let uu____69976 = name_not_found ftv  in
          let uu____69982 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____69976 uu____69982
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
        let uu____70006 = lookup_qname env lid0  in
        match uu____70006 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____70017);
                FStar_Syntax_Syntax.sigrng = uu____70018;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____70020;
                FStar_Syntax_Syntax.sigattrs = uu____70021;_},FStar_Pervasives_Native.None
              ),uu____70022)
            ->
            let lid1 =
              let uu____70076 =
                let uu____70077 = FStar_Ident.range_of_lid lid  in
                let uu____70078 =
                  let uu____70079 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____70079  in
                FStar_Range.set_use_range uu____70077 uu____70078  in
              FStar_Ident.set_lid_range lid uu____70076  in
            let uu____70080 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_70086  ->
                      match uu___452_70086 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____70089 -> false))
               in
            if uu____70080
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____70108 =
                      let uu____70110 =
                        let uu____70112 = get_range env  in
                        FStar_Range.string_of_range uu____70112  in
                      let uu____70113 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____70115 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____70110 uu____70113 uu____70115
                       in
                    failwith uu____70108)
                  in
               match (binders, univs1) with
               | ([],uu____70136) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____70162,uu____70163::uu____70164::uu____70165) ->
                   let uu____70186 =
                     let uu____70188 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____70190 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____70188 uu____70190
                      in
                   failwith uu____70186
               | uu____70201 ->
                   let uu____70216 =
                     let uu____70221 =
                       let uu____70222 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____70222)  in
                     inst_tscheme_with uu____70221 insts  in
                   (match uu____70216 with
                    | (uu____70235,t) ->
                        let t1 =
                          let uu____70238 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____70238 t  in
                        let uu____70239 =
                          let uu____70240 = FStar_Syntax_Subst.compress t1
                             in
                          uu____70240.FStar_Syntax_Syntax.n  in
                        (match uu____70239 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____70275 -> failwith "Impossible")))
        | uu____70283 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____70307 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____70307 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____70320,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____70327 = find1 l2  in
            (match uu____70327 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____70334 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____70334 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____70338 = find1 l  in
            (match uu____70338 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____70343 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____70343
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____70358 = lookup_qname env l1  in
      match uu____70358 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____70361;
              FStar_Syntax_Syntax.sigrng = uu____70362;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____70364;
              FStar_Syntax_Syntax.sigattrs = uu____70365;_},uu____70366),uu____70367)
          -> q
      | uu____70418 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____70442 =
          let uu____70443 =
            let uu____70445 = FStar_Util.string_of_int i  in
            let uu____70447 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____70445 uu____70447
             in
          failwith uu____70443  in
        let uu____70450 = lookup_datacon env lid  in
        match uu____70450 with
        | (uu____70455,t) ->
            let uu____70457 =
              let uu____70458 = FStar_Syntax_Subst.compress t  in
              uu____70458.FStar_Syntax_Syntax.n  in
            (match uu____70457 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70462) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____70506 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____70506
                      FStar_Pervasives_Native.fst)
             | uu____70517 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70531 = lookup_qname env l  in
      match uu____70531 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____70533,uu____70534,uu____70535);
              FStar_Syntax_Syntax.sigrng = uu____70536;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70538;
              FStar_Syntax_Syntax.sigattrs = uu____70539;_},uu____70540),uu____70541)
          ->
          FStar_Util.for_some
            (fun uu___453_70594  ->
               match uu___453_70594 with
               | FStar_Syntax_Syntax.Projector uu____70596 -> true
               | uu____70602 -> false) quals
      | uu____70604 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70618 = lookup_qname env lid  in
      match uu____70618 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____70620,uu____70621,uu____70622,uu____70623,uu____70624,uu____70625);
              FStar_Syntax_Syntax.sigrng = uu____70626;
              FStar_Syntax_Syntax.sigquals = uu____70627;
              FStar_Syntax_Syntax.sigmeta = uu____70628;
              FStar_Syntax_Syntax.sigattrs = uu____70629;_},uu____70630),uu____70631)
          -> true
      | uu____70689 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70703 = lookup_qname env lid  in
      match uu____70703 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____70705,uu____70706,uu____70707,uu____70708,uu____70709,uu____70710);
              FStar_Syntax_Syntax.sigrng = uu____70711;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70713;
              FStar_Syntax_Syntax.sigattrs = uu____70714;_},uu____70715),uu____70716)
          ->
          FStar_Util.for_some
            (fun uu___454_70777  ->
               match uu___454_70777 with
               | FStar_Syntax_Syntax.RecordType uu____70779 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____70789 -> true
               | uu____70799 -> false) quals
      | uu____70801 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____70811,uu____70812);
            FStar_Syntax_Syntax.sigrng = uu____70813;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____70815;
            FStar_Syntax_Syntax.sigattrs = uu____70816;_},uu____70817),uu____70818)
        ->
        FStar_Util.for_some
          (fun uu___455_70875  ->
             match uu___455_70875 with
             | FStar_Syntax_Syntax.Action uu____70877 -> true
             | uu____70879 -> false) quals
    | uu____70881 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70895 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____70895
  
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
      let uu____70912 =
        let uu____70913 = FStar_Syntax_Util.un_uinst head1  in
        uu____70913.FStar_Syntax_Syntax.n  in
      match uu____70912 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____70919 ->
               true
           | uu____70922 -> false)
      | uu____70924 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70938 = lookup_qname env l  in
      match uu____70938 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____70941),uu____70942) ->
          FStar_Util.for_some
            (fun uu___456_70990  ->
               match uu___456_70990 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____70993 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____70995 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____71071 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____71089) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____71107 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____71115 ->
                 FStar_Pervasives_Native.Some true
             | uu____71134 -> FStar_Pervasives_Native.Some false)
         in
      let uu____71137 =
        let uu____71141 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____71141 mapper  in
      match uu____71137 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____71201 = lookup_qname env lid  in
      match uu____71201 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71205,uu____71206,tps,uu____71208,uu____71209,uu____71210);
              FStar_Syntax_Syntax.sigrng = uu____71211;
              FStar_Syntax_Syntax.sigquals = uu____71212;
              FStar_Syntax_Syntax.sigmeta = uu____71213;
              FStar_Syntax_Syntax.sigattrs = uu____71214;_},uu____71215),uu____71216)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____71282 -> FStar_Pervasives_Native.None
  
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
           (fun uu____71328  ->
              match uu____71328 with
              | (d,uu____71337) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____71353 = effect_decl_opt env l  in
      match uu____71353 with
      | FStar_Pervasives_Native.None  ->
          let uu____71368 = name_not_found l  in
          let uu____71374 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____71368 uu____71374
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____71397  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____71416  ->
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
        let uu____71448 = FStar_Ident.lid_equals l1 l2  in
        if uu____71448
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____71459 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____71459
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____71470 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____71523  ->
                        match uu____71523 with
                        | (m1,m2,uu____71537,uu____71538,uu____71539) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____71470 with
              | FStar_Pervasives_Native.None  ->
                  let uu____71556 =
                    let uu____71562 =
                      let uu____71564 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____71566 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____71564
                        uu____71566
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____71562)
                     in
                  FStar_Errors.raise_error uu____71556 env.range
              | FStar_Pervasives_Native.Some
                  (uu____71576,uu____71577,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____71611 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____71611
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
  'Auu____71631 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____71631) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____71660 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____71686  ->
                match uu____71686 with
                | (d,uu____71693) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____71660 with
      | FStar_Pervasives_Native.None  ->
          let uu____71704 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____71704
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____71719 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____71719 with
           | (uu____71734,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____71752)::(wp,uu____71754)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____71810 -> failwith "Impossible"))
  
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
          let uu____71868 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____71868
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____71873 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____71873
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
                  let uu____71884 = get_range env  in
                  let uu____71885 =
                    let uu____71892 =
                      let uu____71893 =
                        let uu____71910 =
                          let uu____71921 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____71921]  in
                        (null_wp, uu____71910)  in
                      FStar_Syntax_Syntax.Tm_app uu____71893  in
                    FStar_Syntax_Syntax.mk uu____71892  in
                  uu____71885 FStar_Pervasives_Native.None uu____71884  in
                let uu____71958 =
                  let uu____71959 =
                    let uu____71970 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____71970]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____71959;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____71958))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_72008 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_72008.order);
              joins = (uu___1944_72008.joins)
            }  in
          let uu___1947_72017 = env  in
          {
            solver = (uu___1947_72017.solver);
            range = (uu___1947_72017.range);
            curmodule = (uu___1947_72017.curmodule);
            gamma = (uu___1947_72017.gamma);
            gamma_sig = (uu___1947_72017.gamma_sig);
            gamma_cache = (uu___1947_72017.gamma_cache);
            modules = (uu___1947_72017.modules);
            expected_typ = (uu___1947_72017.expected_typ);
            sigtab = (uu___1947_72017.sigtab);
            attrtab = (uu___1947_72017.attrtab);
            is_pattern = (uu___1947_72017.is_pattern);
            instantiate_imp = (uu___1947_72017.instantiate_imp);
            effects;
            generalize = (uu___1947_72017.generalize);
            letrecs = (uu___1947_72017.letrecs);
            top_level = (uu___1947_72017.top_level);
            check_uvars = (uu___1947_72017.check_uvars);
            use_eq = (uu___1947_72017.use_eq);
            is_iface = (uu___1947_72017.is_iface);
            admit = (uu___1947_72017.admit);
            lax = (uu___1947_72017.lax);
            lax_universes = (uu___1947_72017.lax_universes);
            phase1 = (uu___1947_72017.phase1);
            failhard = (uu___1947_72017.failhard);
            nosynth = (uu___1947_72017.nosynth);
            uvar_subtyping = (uu___1947_72017.uvar_subtyping);
            tc_term = (uu___1947_72017.tc_term);
            type_of = (uu___1947_72017.type_of);
            universe_of = (uu___1947_72017.universe_of);
            check_type_of = (uu___1947_72017.check_type_of);
            use_bv_sorts = (uu___1947_72017.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_72017.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_72017.normalized_eff_names);
            fv_delta_depths = (uu___1947_72017.fv_delta_depths);
            proof_ns = (uu___1947_72017.proof_ns);
            synth_hook = (uu___1947_72017.synth_hook);
            splice = (uu___1947_72017.splice);
            postprocess = (uu___1947_72017.postprocess);
            is_native_tactic = (uu___1947_72017.is_native_tactic);
            identifier_info = (uu___1947_72017.identifier_info);
            tc_hooks = (uu___1947_72017.tc_hooks);
            dsenv = (uu___1947_72017.dsenv);
            nbe = (uu___1947_72017.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____72047 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____72047  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____72205 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____72206 = l1 u t wp e  in
                                l2 u t uu____72205 uu____72206))
                | uu____72207 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____72279 = inst_tscheme_with lift_t [u]  in
            match uu____72279 with
            | (uu____72286,lift_t1) ->
                let uu____72288 =
                  let uu____72295 =
                    let uu____72296 =
                      let uu____72313 =
                        let uu____72324 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72333 =
                          let uu____72344 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____72344]  in
                        uu____72324 :: uu____72333  in
                      (lift_t1, uu____72313)  in
                    FStar_Syntax_Syntax.Tm_app uu____72296  in
                  FStar_Syntax_Syntax.mk uu____72295  in
                uu____72288 FStar_Pervasives_Native.None
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
            let uu____72454 = inst_tscheme_with lift_t [u]  in
            match uu____72454 with
            | (uu____72461,lift_t1) ->
                let uu____72463 =
                  let uu____72470 =
                    let uu____72471 =
                      let uu____72488 =
                        let uu____72499 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72508 =
                          let uu____72519 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____72528 =
                            let uu____72539 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____72539]  in
                          uu____72519 :: uu____72528  in
                        uu____72499 :: uu____72508  in
                      (lift_t1, uu____72488)  in
                    FStar_Syntax_Syntax.Tm_app uu____72471  in
                  FStar_Syntax_Syntax.mk uu____72470  in
                uu____72463 FStar_Pervasives_Native.None
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
              let uu____72641 =
                let uu____72642 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____72642
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____72641  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____72651 =
              let uu____72653 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____72653  in
            let uu____72654 =
              let uu____72656 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____72684 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____72684)
                 in
              FStar_Util.dflt "none" uu____72656  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____72651
              uu____72654
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____72713  ->
                    match uu____72713 with
                    | (e,uu____72721) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____72744 =
            match uu____72744 with
            | (i,j) ->
                let uu____72755 = FStar_Ident.lid_equals i j  in
                if uu____72755
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _72762  -> FStar_Pervasives_Native.Some _72762)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____72791 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____72801 = FStar_Ident.lid_equals i k  in
                        if uu____72801
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____72815 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____72815
                                  then []
                                  else
                                    (let uu____72822 =
                                       let uu____72831 =
                                         find_edge order1 (i, k)  in
                                       let uu____72834 =
                                         find_edge order1 (k, j)  in
                                       (uu____72831, uu____72834)  in
                                     match uu____72822 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____72849 =
                                           compose_edges e1 e2  in
                                         [uu____72849]
                                     | uu____72850 -> [])))))
                 in
              FStar_List.append order1 uu____72791  in
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
                   let uu____72880 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____72883 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____72883
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____72880
                   then
                     let uu____72890 =
                       let uu____72896 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____72896)
                        in
                     let uu____72900 = get_range env  in
                     FStar_Errors.raise_error uu____72890 uu____72900
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____72978 = FStar_Ident.lid_equals i j
                                   in
                                if uu____72978
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____73030 =
                                              let uu____73039 =
                                                find_edge order2 (i, k)  in
                                              let uu____73042 =
                                                find_edge order2 (j, k)  in
                                              (uu____73039, uu____73042)  in
                                            match uu____73030 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____73084,uu____73085)
                                                     ->
                                                     let uu____73092 =
                                                       let uu____73099 =
                                                         let uu____73101 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73101
                                                          in
                                                       let uu____73104 =
                                                         let uu____73106 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73106
                                                          in
                                                       (uu____73099,
                                                         uu____73104)
                                                        in
                                                     (match uu____73092 with
                                                      | (true ,true ) ->
                                                          let uu____73123 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____73123
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
                                            | uu____73166 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_73239 = env.effects  in
              { decls = (uu___2074_73239.decls); order = order2; joins }  in
            let uu___2077_73240 = env  in
            {
              solver = (uu___2077_73240.solver);
              range = (uu___2077_73240.range);
              curmodule = (uu___2077_73240.curmodule);
              gamma = (uu___2077_73240.gamma);
              gamma_sig = (uu___2077_73240.gamma_sig);
              gamma_cache = (uu___2077_73240.gamma_cache);
              modules = (uu___2077_73240.modules);
              expected_typ = (uu___2077_73240.expected_typ);
              sigtab = (uu___2077_73240.sigtab);
              attrtab = (uu___2077_73240.attrtab);
              is_pattern = (uu___2077_73240.is_pattern);
              instantiate_imp = (uu___2077_73240.instantiate_imp);
              effects;
              generalize = (uu___2077_73240.generalize);
              letrecs = (uu___2077_73240.letrecs);
              top_level = (uu___2077_73240.top_level);
              check_uvars = (uu___2077_73240.check_uvars);
              use_eq = (uu___2077_73240.use_eq);
              is_iface = (uu___2077_73240.is_iface);
              admit = (uu___2077_73240.admit);
              lax = (uu___2077_73240.lax);
              lax_universes = (uu___2077_73240.lax_universes);
              phase1 = (uu___2077_73240.phase1);
              failhard = (uu___2077_73240.failhard);
              nosynth = (uu___2077_73240.nosynth);
              uvar_subtyping = (uu___2077_73240.uvar_subtyping);
              tc_term = (uu___2077_73240.tc_term);
              type_of = (uu___2077_73240.type_of);
              universe_of = (uu___2077_73240.universe_of);
              check_type_of = (uu___2077_73240.check_type_of);
              use_bv_sorts = (uu___2077_73240.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_73240.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_73240.normalized_eff_names);
              fv_delta_depths = (uu___2077_73240.fv_delta_depths);
              proof_ns = (uu___2077_73240.proof_ns);
              synth_hook = (uu___2077_73240.synth_hook);
              splice = (uu___2077_73240.splice);
              postprocess = (uu___2077_73240.postprocess);
              is_native_tactic = (uu___2077_73240.is_native_tactic);
              identifier_info = (uu___2077_73240.identifier_info);
              tc_hooks = (uu___2077_73240.tc_hooks);
              dsenv = (uu___2077_73240.dsenv);
              nbe = (uu___2077_73240.nbe)
            }))
      | uu____73241 -> env
  
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
        | uu____73270 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____73283 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____73283 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____73300 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____73300 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____73325 =
                     let uu____73331 =
                       let uu____73333 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____73341 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____73352 =
                         let uu____73354 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____73354  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____73333 uu____73341 uu____73352
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____73331)
                      in
                   FStar_Errors.raise_error uu____73325
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____73362 =
                     let uu____73373 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____73373 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____73410  ->
                        fun uu____73411  ->
                          match (uu____73410, uu____73411) with
                          | ((x,uu____73441),(t,uu____73443)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____73362
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____73474 =
                     let uu___2115_73475 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_73475.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_73475.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_73475.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_73475.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____73474
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____73487 .
    'Auu____73487 ->
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
          let uu____73517 = effect_decl_opt env effect_name  in
          match uu____73517 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____73556 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____73579 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____73618 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____73618
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____73623 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____73623
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____73638 =
                     let uu____73641 = get_range env  in
                     let uu____73642 =
                       let uu____73649 =
                         let uu____73650 =
                           let uu____73667 =
                             let uu____73678 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____73678; wp]  in
                           (repr, uu____73667)  in
                         FStar_Syntax_Syntax.Tm_app uu____73650  in
                       FStar_Syntax_Syntax.mk uu____73649  in
                     uu____73642 FStar_Pervasives_Native.None uu____73641  in
                   FStar_Pervasives_Native.Some uu____73638)
  
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
      | uu____73822 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____73837 =
        let uu____73838 = FStar_Syntax_Subst.compress t  in
        uu____73838.FStar_Syntax_Syntax.n  in
      match uu____73837 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____73842,c) ->
          is_reifiable_comp env c
      | uu____73864 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____73884 =
           let uu____73886 = is_reifiable_effect env l  in
           Prims.op_Negation uu____73886  in
         if uu____73884
         then
           let uu____73889 =
             let uu____73895 =
               let uu____73897 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____73897
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____73895)  in
           let uu____73901 = get_range env  in
           FStar_Errors.raise_error uu____73889 uu____73901
         else ());
        (let uu____73904 = effect_repr_aux true env c u_c  in
         match uu____73904 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_73940 = env  in
        {
          solver = (uu___2180_73940.solver);
          range = (uu___2180_73940.range);
          curmodule = (uu___2180_73940.curmodule);
          gamma = (uu___2180_73940.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_73940.gamma_cache);
          modules = (uu___2180_73940.modules);
          expected_typ = (uu___2180_73940.expected_typ);
          sigtab = (uu___2180_73940.sigtab);
          attrtab = (uu___2180_73940.attrtab);
          is_pattern = (uu___2180_73940.is_pattern);
          instantiate_imp = (uu___2180_73940.instantiate_imp);
          effects = (uu___2180_73940.effects);
          generalize = (uu___2180_73940.generalize);
          letrecs = (uu___2180_73940.letrecs);
          top_level = (uu___2180_73940.top_level);
          check_uvars = (uu___2180_73940.check_uvars);
          use_eq = (uu___2180_73940.use_eq);
          is_iface = (uu___2180_73940.is_iface);
          admit = (uu___2180_73940.admit);
          lax = (uu___2180_73940.lax);
          lax_universes = (uu___2180_73940.lax_universes);
          phase1 = (uu___2180_73940.phase1);
          failhard = (uu___2180_73940.failhard);
          nosynth = (uu___2180_73940.nosynth);
          uvar_subtyping = (uu___2180_73940.uvar_subtyping);
          tc_term = (uu___2180_73940.tc_term);
          type_of = (uu___2180_73940.type_of);
          universe_of = (uu___2180_73940.universe_of);
          check_type_of = (uu___2180_73940.check_type_of);
          use_bv_sorts = (uu___2180_73940.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_73940.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_73940.normalized_eff_names);
          fv_delta_depths = (uu___2180_73940.fv_delta_depths);
          proof_ns = (uu___2180_73940.proof_ns);
          synth_hook = (uu___2180_73940.synth_hook);
          splice = (uu___2180_73940.splice);
          postprocess = (uu___2180_73940.postprocess);
          is_native_tactic = (uu___2180_73940.is_native_tactic);
          identifier_info = (uu___2180_73940.identifier_info);
          tc_hooks = (uu___2180_73940.tc_hooks);
          dsenv = (uu___2180_73940.dsenv);
          nbe = (uu___2180_73940.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_73954 = env  in
      {
        solver = (uu___2187_73954.solver);
        range = (uu___2187_73954.range);
        curmodule = (uu___2187_73954.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_73954.gamma_sig);
        gamma_cache = (uu___2187_73954.gamma_cache);
        modules = (uu___2187_73954.modules);
        expected_typ = (uu___2187_73954.expected_typ);
        sigtab = (uu___2187_73954.sigtab);
        attrtab = (uu___2187_73954.attrtab);
        is_pattern = (uu___2187_73954.is_pattern);
        instantiate_imp = (uu___2187_73954.instantiate_imp);
        effects = (uu___2187_73954.effects);
        generalize = (uu___2187_73954.generalize);
        letrecs = (uu___2187_73954.letrecs);
        top_level = (uu___2187_73954.top_level);
        check_uvars = (uu___2187_73954.check_uvars);
        use_eq = (uu___2187_73954.use_eq);
        is_iface = (uu___2187_73954.is_iface);
        admit = (uu___2187_73954.admit);
        lax = (uu___2187_73954.lax);
        lax_universes = (uu___2187_73954.lax_universes);
        phase1 = (uu___2187_73954.phase1);
        failhard = (uu___2187_73954.failhard);
        nosynth = (uu___2187_73954.nosynth);
        uvar_subtyping = (uu___2187_73954.uvar_subtyping);
        tc_term = (uu___2187_73954.tc_term);
        type_of = (uu___2187_73954.type_of);
        universe_of = (uu___2187_73954.universe_of);
        check_type_of = (uu___2187_73954.check_type_of);
        use_bv_sorts = (uu___2187_73954.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_73954.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_73954.normalized_eff_names);
        fv_delta_depths = (uu___2187_73954.fv_delta_depths);
        proof_ns = (uu___2187_73954.proof_ns);
        synth_hook = (uu___2187_73954.synth_hook);
        splice = (uu___2187_73954.splice);
        postprocess = (uu___2187_73954.postprocess);
        is_native_tactic = (uu___2187_73954.is_native_tactic);
        identifier_info = (uu___2187_73954.identifier_info);
        tc_hooks = (uu___2187_73954.tc_hooks);
        dsenv = (uu___2187_73954.dsenv);
        nbe = (uu___2187_73954.nbe)
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
            (let uu___2200_74012 = env  in
             {
               solver = (uu___2200_74012.solver);
               range = (uu___2200_74012.range);
               curmodule = (uu___2200_74012.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_74012.gamma_sig);
               gamma_cache = (uu___2200_74012.gamma_cache);
               modules = (uu___2200_74012.modules);
               expected_typ = (uu___2200_74012.expected_typ);
               sigtab = (uu___2200_74012.sigtab);
               attrtab = (uu___2200_74012.attrtab);
               is_pattern = (uu___2200_74012.is_pattern);
               instantiate_imp = (uu___2200_74012.instantiate_imp);
               effects = (uu___2200_74012.effects);
               generalize = (uu___2200_74012.generalize);
               letrecs = (uu___2200_74012.letrecs);
               top_level = (uu___2200_74012.top_level);
               check_uvars = (uu___2200_74012.check_uvars);
               use_eq = (uu___2200_74012.use_eq);
               is_iface = (uu___2200_74012.is_iface);
               admit = (uu___2200_74012.admit);
               lax = (uu___2200_74012.lax);
               lax_universes = (uu___2200_74012.lax_universes);
               phase1 = (uu___2200_74012.phase1);
               failhard = (uu___2200_74012.failhard);
               nosynth = (uu___2200_74012.nosynth);
               uvar_subtyping = (uu___2200_74012.uvar_subtyping);
               tc_term = (uu___2200_74012.tc_term);
               type_of = (uu___2200_74012.type_of);
               universe_of = (uu___2200_74012.universe_of);
               check_type_of = (uu___2200_74012.check_type_of);
               use_bv_sorts = (uu___2200_74012.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_74012.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_74012.normalized_eff_names);
               fv_delta_depths = (uu___2200_74012.fv_delta_depths);
               proof_ns = (uu___2200_74012.proof_ns);
               synth_hook = (uu___2200_74012.synth_hook);
               splice = (uu___2200_74012.splice);
               postprocess = (uu___2200_74012.postprocess);
               is_native_tactic = (uu___2200_74012.is_native_tactic);
               identifier_info = (uu___2200_74012.identifier_info);
               tc_hooks = (uu___2200_74012.tc_hooks);
               dsenv = (uu___2200_74012.dsenv);
               nbe = (uu___2200_74012.nbe)
             }))
    | uu____74013 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____74042  ->
             match uu____74042 with | (x,uu____74050) -> push_bv env1 x) env
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
            let uu___2214_74085 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_74085.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_74085.FStar_Syntax_Syntax.index);
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
      (let uu___2225_74127 = env  in
       {
         solver = (uu___2225_74127.solver);
         range = (uu___2225_74127.range);
         curmodule = (uu___2225_74127.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_74127.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_74127.sigtab);
         attrtab = (uu___2225_74127.attrtab);
         is_pattern = (uu___2225_74127.is_pattern);
         instantiate_imp = (uu___2225_74127.instantiate_imp);
         effects = (uu___2225_74127.effects);
         generalize = (uu___2225_74127.generalize);
         letrecs = (uu___2225_74127.letrecs);
         top_level = (uu___2225_74127.top_level);
         check_uvars = (uu___2225_74127.check_uvars);
         use_eq = (uu___2225_74127.use_eq);
         is_iface = (uu___2225_74127.is_iface);
         admit = (uu___2225_74127.admit);
         lax = (uu___2225_74127.lax);
         lax_universes = (uu___2225_74127.lax_universes);
         phase1 = (uu___2225_74127.phase1);
         failhard = (uu___2225_74127.failhard);
         nosynth = (uu___2225_74127.nosynth);
         uvar_subtyping = (uu___2225_74127.uvar_subtyping);
         tc_term = (uu___2225_74127.tc_term);
         type_of = (uu___2225_74127.type_of);
         universe_of = (uu___2225_74127.universe_of);
         check_type_of = (uu___2225_74127.check_type_of);
         use_bv_sorts = (uu___2225_74127.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_74127.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_74127.normalized_eff_names);
         fv_delta_depths = (uu___2225_74127.fv_delta_depths);
         proof_ns = (uu___2225_74127.proof_ns);
         synth_hook = (uu___2225_74127.synth_hook);
         splice = (uu___2225_74127.splice);
         postprocess = (uu___2225_74127.postprocess);
         is_native_tactic = (uu___2225_74127.is_native_tactic);
         identifier_info = (uu___2225_74127.identifier_info);
         tc_hooks = (uu___2225_74127.tc_hooks);
         dsenv = (uu___2225_74127.dsenv);
         nbe = (uu___2225_74127.nbe)
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
        let uu____74171 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____74171 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____74199 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____74199)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_74215 = env  in
      {
        solver = (uu___2240_74215.solver);
        range = (uu___2240_74215.range);
        curmodule = (uu___2240_74215.curmodule);
        gamma = (uu___2240_74215.gamma);
        gamma_sig = (uu___2240_74215.gamma_sig);
        gamma_cache = (uu___2240_74215.gamma_cache);
        modules = (uu___2240_74215.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_74215.sigtab);
        attrtab = (uu___2240_74215.attrtab);
        is_pattern = (uu___2240_74215.is_pattern);
        instantiate_imp = (uu___2240_74215.instantiate_imp);
        effects = (uu___2240_74215.effects);
        generalize = (uu___2240_74215.generalize);
        letrecs = (uu___2240_74215.letrecs);
        top_level = (uu___2240_74215.top_level);
        check_uvars = (uu___2240_74215.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_74215.is_iface);
        admit = (uu___2240_74215.admit);
        lax = (uu___2240_74215.lax);
        lax_universes = (uu___2240_74215.lax_universes);
        phase1 = (uu___2240_74215.phase1);
        failhard = (uu___2240_74215.failhard);
        nosynth = (uu___2240_74215.nosynth);
        uvar_subtyping = (uu___2240_74215.uvar_subtyping);
        tc_term = (uu___2240_74215.tc_term);
        type_of = (uu___2240_74215.type_of);
        universe_of = (uu___2240_74215.universe_of);
        check_type_of = (uu___2240_74215.check_type_of);
        use_bv_sorts = (uu___2240_74215.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_74215.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_74215.normalized_eff_names);
        fv_delta_depths = (uu___2240_74215.fv_delta_depths);
        proof_ns = (uu___2240_74215.proof_ns);
        synth_hook = (uu___2240_74215.synth_hook);
        splice = (uu___2240_74215.splice);
        postprocess = (uu___2240_74215.postprocess);
        is_native_tactic = (uu___2240_74215.is_native_tactic);
        identifier_info = (uu___2240_74215.identifier_info);
        tc_hooks = (uu___2240_74215.tc_hooks);
        dsenv = (uu___2240_74215.dsenv);
        nbe = (uu___2240_74215.nbe)
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
    let uu____74246 = expected_typ env_  in
    ((let uu___2247_74252 = env_  in
      {
        solver = (uu___2247_74252.solver);
        range = (uu___2247_74252.range);
        curmodule = (uu___2247_74252.curmodule);
        gamma = (uu___2247_74252.gamma);
        gamma_sig = (uu___2247_74252.gamma_sig);
        gamma_cache = (uu___2247_74252.gamma_cache);
        modules = (uu___2247_74252.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_74252.sigtab);
        attrtab = (uu___2247_74252.attrtab);
        is_pattern = (uu___2247_74252.is_pattern);
        instantiate_imp = (uu___2247_74252.instantiate_imp);
        effects = (uu___2247_74252.effects);
        generalize = (uu___2247_74252.generalize);
        letrecs = (uu___2247_74252.letrecs);
        top_level = (uu___2247_74252.top_level);
        check_uvars = (uu___2247_74252.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_74252.is_iface);
        admit = (uu___2247_74252.admit);
        lax = (uu___2247_74252.lax);
        lax_universes = (uu___2247_74252.lax_universes);
        phase1 = (uu___2247_74252.phase1);
        failhard = (uu___2247_74252.failhard);
        nosynth = (uu___2247_74252.nosynth);
        uvar_subtyping = (uu___2247_74252.uvar_subtyping);
        tc_term = (uu___2247_74252.tc_term);
        type_of = (uu___2247_74252.type_of);
        universe_of = (uu___2247_74252.universe_of);
        check_type_of = (uu___2247_74252.check_type_of);
        use_bv_sorts = (uu___2247_74252.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_74252.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_74252.normalized_eff_names);
        fv_delta_depths = (uu___2247_74252.fv_delta_depths);
        proof_ns = (uu___2247_74252.proof_ns);
        synth_hook = (uu___2247_74252.synth_hook);
        splice = (uu___2247_74252.splice);
        postprocess = (uu___2247_74252.postprocess);
        is_native_tactic = (uu___2247_74252.is_native_tactic);
        identifier_info = (uu___2247_74252.identifier_info);
        tc_hooks = (uu___2247_74252.tc_hooks);
        dsenv = (uu___2247_74252.dsenv);
        nbe = (uu___2247_74252.nbe)
      }), uu____74246)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____74264 =
      let uu____74267 = FStar_Ident.id_of_text ""  in [uu____74267]  in
    FStar_Ident.lid_of_ids uu____74264  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____74274 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____74274
        then
          let uu____74279 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____74279 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_74307 = env  in
       {
         solver = (uu___2255_74307.solver);
         range = (uu___2255_74307.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_74307.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_74307.expected_typ);
         sigtab = (uu___2255_74307.sigtab);
         attrtab = (uu___2255_74307.attrtab);
         is_pattern = (uu___2255_74307.is_pattern);
         instantiate_imp = (uu___2255_74307.instantiate_imp);
         effects = (uu___2255_74307.effects);
         generalize = (uu___2255_74307.generalize);
         letrecs = (uu___2255_74307.letrecs);
         top_level = (uu___2255_74307.top_level);
         check_uvars = (uu___2255_74307.check_uvars);
         use_eq = (uu___2255_74307.use_eq);
         is_iface = (uu___2255_74307.is_iface);
         admit = (uu___2255_74307.admit);
         lax = (uu___2255_74307.lax);
         lax_universes = (uu___2255_74307.lax_universes);
         phase1 = (uu___2255_74307.phase1);
         failhard = (uu___2255_74307.failhard);
         nosynth = (uu___2255_74307.nosynth);
         uvar_subtyping = (uu___2255_74307.uvar_subtyping);
         tc_term = (uu___2255_74307.tc_term);
         type_of = (uu___2255_74307.type_of);
         universe_of = (uu___2255_74307.universe_of);
         check_type_of = (uu___2255_74307.check_type_of);
         use_bv_sorts = (uu___2255_74307.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_74307.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_74307.normalized_eff_names);
         fv_delta_depths = (uu___2255_74307.fv_delta_depths);
         proof_ns = (uu___2255_74307.proof_ns);
         synth_hook = (uu___2255_74307.synth_hook);
         splice = (uu___2255_74307.splice);
         postprocess = (uu___2255_74307.postprocess);
         is_native_tactic = (uu___2255_74307.is_native_tactic);
         identifier_info = (uu___2255_74307.identifier_info);
         tc_hooks = (uu___2255_74307.tc_hooks);
         dsenv = (uu___2255_74307.dsenv);
         nbe = (uu___2255_74307.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74359)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74363,(uu____74364,t)))::tl1
          ->
          let uu____74385 =
            let uu____74388 = FStar_Syntax_Free.uvars t  in
            ext out uu____74388  in
          aux uu____74385 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74391;
            FStar_Syntax_Syntax.index = uu____74392;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74400 =
            let uu____74403 = FStar_Syntax_Free.uvars t  in
            ext out uu____74403  in
          aux uu____74400 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74461)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74465,(uu____74466,t)))::tl1
          ->
          let uu____74487 =
            let uu____74490 = FStar_Syntax_Free.univs t  in
            ext out uu____74490  in
          aux uu____74487 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74493;
            FStar_Syntax_Syntax.index = uu____74494;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74502 =
            let uu____74505 = FStar_Syntax_Free.univs t  in
            ext out uu____74505  in
          aux uu____74502 tl1
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
          let uu____74567 = FStar_Util.set_add uname out  in
          aux uu____74567 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74570,(uu____74571,t)))::tl1
          ->
          let uu____74592 =
            let uu____74595 = FStar_Syntax_Free.univnames t  in
            ext out uu____74595  in
          aux uu____74592 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74598;
            FStar_Syntax_Syntax.index = uu____74599;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74607 =
            let uu____74610 = FStar_Syntax_Free.univnames t  in
            ext out uu____74610  in
          aux uu____74607 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_74631  ->
            match uu___457_74631 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____74635 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____74648 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____74659 =
      let uu____74668 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____74668
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____74659 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____74716 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_74729  ->
              match uu___458_74729 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____74732 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____74732
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____74738) ->
                  let uu____74755 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____74755))
       in
    FStar_All.pipe_right uu____74716 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_74769  ->
    match uu___459_74769 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____74775 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____74775
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____74798  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____74853) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____74886,uu____74887) -> false  in
      let uu____74901 =
        FStar_List.tryFind
          (fun uu____74923  ->
             match uu____74923 with | (p,uu____74934) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____74901 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____74953,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____74983 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____74983
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_75005 = e  in
        {
          solver = (uu___2398_75005.solver);
          range = (uu___2398_75005.range);
          curmodule = (uu___2398_75005.curmodule);
          gamma = (uu___2398_75005.gamma);
          gamma_sig = (uu___2398_75005.gamma_sig);
          gamma_cache = (uu___2398_75005.gamma_cache);
          modules = (uu___2398_75005.modules);
          expected_typ = (uu___2398_75005.expected_typ);
          sigtab = (uu___2398_75005.sigtab);
          attrtab = (uu___2398_75005.attrtab);
          is_pattern = (uu___2398_75005.is_pattern);
          instantiate_imp = (uu___2398_75005.instantiate_imp);
          effects = (uu___2398_75005.effects);
          generalize = (uu___2398_75005.generalize);
          letrecs = (uu___2398_75005.letrecs);
          top_level = (uu___2398_75005.top_level);
          check_uvars = (uu___2398_75005.check_uvars);
          use_eq = (uu___2398_75005.use_eq);
          is_iface = (uu___2398_75005.is_iface);
          admit = (uu___2398_75005.admit);
          lax = (uu___2398_75005.lax);
          lax_universes = (uu___2398_75005.lax_universes);
          phase1 = (uu___2398_75005.phase1);
          failhard = (uu___2398_75005.failhard);
          nosynth = (uu___2398_75005.nosynth);
          uvar_subtyping = (uu___2398_75005.uvar_subtyping);
          tc_term = (uu___2398_75005.tc_term);
          type_of = (uu___2398_75005.type_of);
          universe_of = (uu___2398_75005.universe_of);
          check_type_of = (uu___2398_75005.check_type_of);
          use_bv_sorts = (uu___2398_75005.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_75005.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_75005.normalized_eff_names);
          fv_delta_depths = (uu___2398_75005.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_75005.synth_hook);
          splice = (uu___2398_75005.splice);
          postprocess = (uu___2398_75005.postprocess);
          is_native_tactic = (uu___2398_75005.is_native_tactic);
          identifier_info = (uu___2398_75005.identifier_info);
          tc_hooks = (uu___2398_75005.tc_hooks);
          dsenv = (uu___2398_75005.dsenv);
          nbe = (uu___2398_75005.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_75053 = e  in
      {
        solver = (uu___2407_75053.solver);
        range = (uu___2407_75053.range);
        curmodule = (uu___2407_75053.curmodule);
        gamma = (uu___2407_75053.gamma);
        gamma_sig = (uu___2407_75053.gamma_sig);
        gamma_cache = (uu___2407_75053.gamma_cache);
        modules = (uu___2407_75053.modules);
        expected_typ = (uu___2407_75053.expected_typ);
        sigtab = (uu___2407_75053.sigtab);
        attrtab = (uu___2407_75053.attrtab);
        is_pattern = (uu___2407_75053.is_pattern);
        instantiate_imp = (uu___2407_75053.instantiate_imp);
        effects = (uu___2407_75053.effects);
        generalize = (uu___2407_75053.generalize);
        letrecs = (uu___2407_75053.letrecs);
        top_level = (uu___2407_75053.top_level);
        check_uvars = (uu___2407_75053.check_uvars);
        use_eq = (uu___2407_75053.use_eq);
        is_iface = (uu___2407_75053.is_iface);
        admit = (uu___2407_75053.admit);
        lax = (uu___2407_75053.lax);
        lax_universes = (uu___2407_75053.lax_universes);
        phase1 = (uu___2407_75053.phase1);
        failhard = (uu___2407_75053.failhard);
        nosynth = (uu___2407_75053.nosynth);
        uvar_subtyping = (uu___2407_75053.uvar_subtyping);
        tc_term = (uu___2407_75053.tc_term);
        type_of = (uu___2407_75053.type_of);
        universe_of = (uu___2407_75053.universe_of);
        check_type_of = (uu___2407_75053.check_type_of);
        use_bv_sorts = (uu___2407_75053.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_75053.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_75053.normalized_eff_names);
        fv_delta_depths = (uu___2407_75053.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_75053.synth_hook);
        splice = (uu___2407_75053.splice);
        postprocess = (uu___2407_75053.postprocess);
        is_native_tactic = (uu___2407_75053.is_native_tactic);
        identifier_info = (uu___2407_75053.identifier_info);
        tc_hooks = (uu___2407_75053.tc_hooks);
        dsenv = (uu___2407_75053.dsenv);
        nbe = (uu___2407_75053.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____75069 = FStar_Syntax_Free.names t  in
      let uu____75072 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____75069 uu____75072
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____75095 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____75095
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____75105 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____75105
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____75126 =
      match uu____75126 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____75146 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____75146)
       in
    let uu____75154 =
      let uu____75158 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____75158 FStar_List.rev  in
    FStar_All.pipe_right uu____75154 (FStar_String.concat " ")
  
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
                  (let uu____75228 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____75228 with
                   | FStar_Pervasives_Native.Some uu____75232 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____75235 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____75245;
        univ_ineqs = uu____75246; implicits = uu____75247;_} -> true
    | uu____75259 -> false
  
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
          let uu___2451_75290 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_75290.deferred);
            univ_ineqs = (uu___2451_75290.univ_ineqs);
            implicits = (uu___2451_75290.implicits)
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
          let uu____75329 = FStar_Options.defensive ()  in
          if uu____75329
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____75335 =
              let uu____75337 =
                let uu____75339 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____75339  in
              Prims.op_Negation uu____75337  in
            (if uu____75335
             then
               let uu____75346 =
                 let uu____75352 =
                   let uu____75354 = FStar_Syntax_Print.term_to_string t  in
                   let uu____75356 =
                     let uu____75358 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____75358
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____75354 uu____75356
                    in
                 (FStar_Errors.Warning_Defensive, uu____75352)  in
               FStar_Errors.log_issue rng uu____75346
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
          let uu____75398 =
            let uu____75400 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75400  in
          if uu____75398
          then ()
          else
            (let uu____75405 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____75405 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____75431 =
            let uu____75433 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75433  in
          if uu____75431
          then ()
          else
            (let uu____75438 = bound_vars e  in
             def_check_closed_in rng msg uu____75438 t)
  
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
          let uu___2488_75477 = g  in
          let uu____75478 =
            let uu____75479 =
              let uu____75480 =
                let uu____75487 =
                  let uu____75488 =
                    let uu____75505 =
                      let uu____75516 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____75516]  in
                    (f, uu____75505)  in
                  FStar_Syntax_Syntax.Tm_app uu____75488  in
                FStar_Syntax_Syntax.mk uu____75487  in
              uu____75480 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _75553  -> FStar_TypeChecker_Common.NonTrivial _75553)
              uu____75479
             in
          {
            guard_f = uu____75478;
            deferred = (uu___2488_75477.deferred);
            univ_ineqs = (uu___2488_75477.univ_ineqs);
            implicits = (uu___2488_75477.implicits)
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
          let uu___2495_75571 = g  in
          let uu____75572 =
            let uu____75573 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75573  in
          {
            guard_f = uu____75572;
            deferred = (uu___2495_75571.deferred);
            univ_ineqs = (uu___2495_75571.univ_ineqs);
            implicits = (uu___2495_75571.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_75590 = g  in
          let uu____75591 =
            let uu____75592 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____75592  in
          {
            guard_f = uu____75591;
            deferred = (uu___2500_75590.deferred);
            univ_ineqs = (uu___2500_75590.univ_ineqs);
            implicits = (uu___2500_75590.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_75594 = g  in
          let uu____75595 =
            let uu____75596 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75596  in
          {
            guard_f = uu____75595;
            deferred = (uu___2504_75594.deferred);
            univ_ineqs = (uu___2504_75594.univ_ineqs);
            implicits = (uu___2504_75594.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____75603 ->
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
          let uu____75620 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____75620
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____75627 =
      let uu____75628 = FStar_Syntax_Util.unmeta t  in
      uu____75628.FStar_Syntax_Syntax.n  in
    match uu____75627 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____75632 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____75675 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____75675;
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
                       let uu____75770 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____75770
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_75777 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_75777.deferred);
              univ_ineqs = (uu___2559_75777.univ_ineqs);
              implicits = (uu___2559_75777.implicits)
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
               let uu____75811 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____75811
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
            let uu___2574_75838 = g  in
            let uu____75839 =
              let uu____75840 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____75840  in
            {
              guard_f = uu____75839;
              deferred = (uu___2574_75838.deferred);
              univ_ineqs = (uu___2574_75838.univ_ineqs);
              implicits = (uu___2574_75838.implicits)
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
              let uu____75898 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____75898 with
              | FStar_Pervasives_Native.Some
                  (uu____75923::(tm,uu____75925)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____75989 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____76007 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____76007;
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
                      let uu___2596_76039 = trivial_guard  in
                      {
                        guard_f = (uu___2596_76039.guard_f);
                        deferred = (uu___2596_76039.deferred);
                        univ_ineqs = (uu___2596_76039.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____76057  -> ());
    push = (fun uu____76059  -> ());
    pop = (fun uu____76062  -> ());
    snapshot =
      (fun uu____76065  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____76084  -> fun uu____76085  -> ());
    encode_sig = (fun uu____76100  -> fun uu____76101  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____76107 =
             let uu____76114 = FStar_Options.peek ()  in (e, g, uu____76114)
              in
           [uu____76107]);
    solve = (fun uu____76130  -> fun uu____76131  -> fun uu____76132  -> ());
    finish = (fun uu____76139  -> ());
    refresh = (fun uu____76141  -> ())
  } 