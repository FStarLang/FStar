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
    match projectee with | Beta  -> true | uu____51478 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____51489 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____51500 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____51512 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____51530 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____51541 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____51552 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____51563 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____51574 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____51585 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____51597 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____51618 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____51645 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____51672 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____51696 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____51707 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____51718 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____51729 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____51740 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____51751 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____51762 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____51773 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____51784 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____51795 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____51806 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____51817 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____51828 -> false
  
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
      | uu____51888 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____51914 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____51925 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____51936 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____51948 -> false
  
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
           (fun uu___446_63165  ->
              match uu___446_63165 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____63168 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____63168  in
                  let uu____63169 =
                    let uu____63170 = FStar_Syntax_Subst.compress y  in
                    uu____63170.FStar_Syntax_Syntax.n  in
                  (match uu____63169 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____63174 =
                         let uu___775_63175 = y1  in
                         let uu____63176 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_63175.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_63175.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____63176
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____63174
                   | uu____63179 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_63193 = env  in
      let uu____63194 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_63193.solver);
        range = (uu___781_63193.range);
        curmodule = (uu___781_63193.curmodule);
        gamma = uu____63194;
        gamma_sig = (uu___781_63193.gamma_sig);
        gamma_cache = (uu___781_63193.gamma_cache);
        modules = (uu___781_63193.modules);
        expected_typ = (uu___781_63193.expected_typ);
        sigtab = (uu___781_63193.sigtab);
        attrtab = (uu___781_63193.attrtab);
        is_pattern = (uu___781_63193.is_pattern);
        instantiate_imp = (uu___781_63193.instantiate_imp);
        effects = (uu___781_63193.effects);
        generalize = (uu___781_63193.generalize);
        letrecs = (uu___781_63193.letrecs);
        top_level = (uu___781_63193.top_level);
        check_uvars = (uu___781_63193.check_uvars);
        use_eq = (uu___781_63193.use_eq);
        is_iface = (uu___781_63193.is_iface);
        admit = (uu___781_63193.admit);
        lax = (uu___781_63193.lax);
        lax_universes = (uu___781_63193.lax_universes);
        phase1 = (uu___781_63193.phase1);
        failhard = (uu___781_63193.failhard);
        nosynth = (uu___781_63193.nosynth);
        uvar_subtyping = (uu___781_63193.uvar_subtyping);
        tc_term = (uu___781_63193.tc_term);
        type_of = (uu___781_63193.type_of);
        universe_of = (uu___781_63193.universe_of);
        check_type_of = (uu___781_63193.check_type_of);
        use_bv_sorts = (uu___781_63193.use_bv_sorts);
        qtbl_name_and_index = (uu___781_63193.qtbl_name_and_index);
        normalized_eff_names = (uu___781_63193.normalized_eff_names);
        fv_delta_depths = (uu___781_63193.fv_delta_depths);
        proof_ns = (uu___781_63193.proof_ns);
        synth_hook = (uu___781_63193.synth_hook);
        splice = (uu___781_63193.splice);
        postprocess = (uu___781_63193.postprocess);
        is_native_tactic = (uu___781_63193.is_native_tactic);
        identifier_info = (uu___781_63193.identifier_info);
        tc_hooks = (uu___781_63193.tc_hooks);
        dsenv = (uu___781_63193.dsenv);
        nbe = (uu___781_63193.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____63202  -> fun uu____63203  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_63225 = env  in
      {
        solver = (uu___788_63225.solver);
        range = (uu___788_63225.range);
        curmodule = (uu___788_63225.curmodule);
        gamma = (uu___788_63225.gamma);
        gamma_sig = (uu___788_63225.gamma_sig);
        gamma_cache = (uu___788_63225.gamma_cache);
        modules = (uu___788_63225.modules);
        expected_typ = (uu___788_63225.expected_typ);
        sigtab = (uu___788_63225.sigtab);
        attrtab = (uu___788_63225.attrtab);
        is_pattern = (uu___788_63225.is_pattern);
        instantiate_imp = (uu___788_63225.instantiate_imp);
        effects = (uu___788_63225.effects);
        generalize = (uu___788_63225.generalize);
        letrecs = (uu___788_63225.letrecs);
        top_level = (uu___788_63225.top_level);
        check_uvars = (uu___788_63225.check_uvars);
        use_eq = (uu___788_63225.use_eq);
        is_iface = (uu___788_63225.is_iface);
        admit = (uu___788_63225.admit);
        lax = (uu___788_63225.lax);
        lax_universes = (uu___788_63225.lax_universes);
        phase1 = (uu___788_63225.phase1);
        failhard = (uu___788_63225.failhard);
        nosynth = (uu___788_63225.nosynth);
        uvar_subtyping = (uu___788_63225.uvar_subtyping);
        tc_term = (uu___788_63225.tc_term);
        type_of = (uu___788_63225.type_of);
        universe_of = (uu___788_63225.universe_of);
        check_type_of = (uu___788_63225.check_type_of);
        use_bv_sorts = (uu___788_63225.use_bv_sorts);
        qtbl_name_and_index = (uu___788_63225.qtbl_name_and_index);
        normalized_eff_names = (uu___788_63225.normalized_eff_names);
        fv_delta_depths = (uu___788_63225.fv_delta_depths);
        proof_ns = (uu___788_63225.proof_ns);
        synth_hook = (uu___788_63225.synth_hook);
        splice = (uu___788_63225.splice);
        postprocess = (uu___788_63225.postprocess);
        is_native_tactic = (uu___788_63225.is_native_tactic);
        identifier_info = (uu___788_63225.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_63225.dsenv);
        nbe = (uu___788_63225.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_63237 = e  in
      let uu____63238 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_63237.solver);
        range = (uu___792_63237.range);
        curmodule = (uu___792_63237.curmodule);
        gamma = (uu___792_63237.gamma);
        gamma_sig = (uu___792_63237.gamma_sig);
        gamma_cache = (uu___792_63237.gamma_cache);
        modules = (uu___792_63237.modules);
        expected_typ = (uu___792_63237.expected_typ);
        sigtab = (uu___792_63237.sigtab);
        attrtab = (uu___792_63237.attrtab);
        is_pattern = (uu___792_63237.is_pattern);
        instantiate_imp = (uu___792_63237.instantiate_imp);
        effects = (uu___792_63237.effects);
        generalize = (uu___792_63237.generalize);
        letrecs = (uu___792_63237.letrecs);
        top_level = (uu___792_63237.top_level);
        check_uvars = (uu___792_63237.check_uvars);
        use_eq = (uu___792_63237.use_eq);
        is_iface = (uu___792_63237.is_iface);
        admit = (uu___792_63237.admit);
        lax = (uu___792_63237.lax);
        lax_universes = (uu___792_63237.lax_universes);
        phase1 = (uu___792_63237.phase1);
        failhard = (uu___792_63237.failhard);
        nosynth = (uu___792_63237.nosynth);
        uvar_subtyping = (uu___792_63237.uvar_subtyping);
        tc_term = (uu___792_63237.tc_term);
        type_of = (uu___792_63237.type_of);
        universe_of = (uu___792_63237.universe_of);
        check_type_of = (uu___792_63237.check_type_of);
        use_bv_sorts = (uu___792_63237.use_bv_sorts);
        qtbl_name_and_index = (uu___792_63237.qtbl_name_and_index);
        normalized_eff_names = (uu___792_63237.normalized_eff_names);
        fv_delta_depths = (uu___792_63237.fv_delta_depths);
        proof_ns = (uu___792_63237.proof_ns);
        synth_hook = (uu___792_63237.synth_hook);
        splice = (uu___792_63237.splice);
        postprocess = (uu___792_63237.postprocess);
        is_native_tactic = (uu___792_63237.is_native_tactic);
        identifier_info = (uu___792_63237.identifier_info);
        tc_hooks = (uu___792_63237.tc_hooks);
        dsenv = uu____63238;
        nbe = (uu___792_63237.nbe)
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
      | (NoDelta ,uu____63267) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____63270,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____63272,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____63275 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____63289 . unit -> 'Auu____63289 FStar_Util.smap =
  fun uu____63296  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____63302 . unit -> 'Auu____63302 FStar_Util.smap =
  fun uu____63309  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____63447 = new_gamma_cache ()  in
                  let uu____63450 = new_sigtab ()  in
                  let uu____63453 = new_sigtab ()  in
                  let uu____63460 =
                    let uu____63475 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____63475, FStar_Pervasives_Native.None)  in
                  let uu____63496 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____63500 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____63504 = FStar_Options.using_facts_from ()  in
                  let uu____63505 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____63508 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____63447;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____63450;
                    attrtab = uu____63453;
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
                    qtbl_name_and_index = uu____63460;
                    normalized_eff_names = uu____63496;
                    fv_delta_depths = uu____63500;
                    proof_ns = uu____63504;
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
                    is_native_tactic = (fun uu____63570  -> false);
                    identifier_info = uu____63505;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____63508;
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
  fun uu____63649  ->
    let uu____63650 = FStar_ST.op_Bang query_indices  in
    match uu____63650 with
    | [] -> failwith "Empty query indices!"
    | uu____63705 ->
        let uu____63715 =
          let uu____63725 =
            let uu____63733 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____63733  in
          let uu____63787 = FStar_ST.op_Bang query_indices  in uu____63725 ::
            uu____63787
           in
        FStar_ST.op_Colon_Equals query_indices uu____63715
  
let (pop_query_indices : unit -> unit) =
  fun uu____63883  ->
    let uu____63884 = FStar_ST.op_Bang query_indices  in
    match uu____63884 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____64011  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____64048  ->
    match uu____64048 with
    | (l,n1) ->
        let uu____64058 = FStar_ST.op_Bang query_indices  in
        (match uu____64058 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____64180 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____64203  ->
    let uu____64204 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____64204
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____64272 =
       let uu____64275 = FStar_ST.op_Bang stack  in env :: uu____64275  in
     FStar_ST.op_Colon_Equals stack uu____64272);
    (let uu___860_64324 = env  in
     let uu____64325 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____64328 = FStar_Util.smap_copy (sigtab env)  in
     let uu____64331 = FStar_Util.smap_copy (attrtab env)  in
     let uu____64338 =
       let uu____64353 =
         let uu____64357 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____64357  in
       let uu____64389 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____64353, uu____64389)  in
     let uu____64438 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____64441 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____64444 =
       let uu____64447 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____64447  in
     {
       solver = (uu___860_64324.solver);
       range = (uu___860_64324.range);
       curmodule = (uu___860_64324.curmodule);
       gamma = (uu___860_64324.gamma);
       gamma_sig = (uu___860_64324.gamma_sig);
       gamma_cache = uu____64325;
       modules = (uu___860_64324.modules);
       expected_typ = (uu___860_64324.expected_typ);
       sigtab = uu____64328;
       attrtab = uu____64331;
       is_pattern = (uu___860_64324.is_pattern);
       instantiate_imp = (uu___860_64324.instantiate_imp);
       effects = (uu___860_64324.effects);
       generalize = (uu___860_64324.generalize);
       letrecs = (uu___860_64324.letrecs);
       top_level = (uu___860_64324.top_level);
       check_uvars = (uu___860_64324.check_uvars);
       use_eq = (uu___860_64324.use_eq);
       is_iface = (uu___860_64324.is_iface);
       admit = (uu___860_64324.admit);
       lax = (uu___860_64324.lax);
       lax_universes = (uu___860_64324.lax_universes);
       phase1 = (uu___860_64324.phase1);
       failhard = (uu___860_64324.failhard);
       nosynth = (uu___860_64324.nosynth);
       uvar_subtyping = (uu___860_64324.uvar_subtyping);
       tc_term = (uu___860_64324.tc_term);
       type_of = (uu___860_64324.type_of);
       universe_of = (uu___860_64324.universe_of);
       check_type_of = (uu___860_64324.check_type_of);
       use_bv_sorts = (uu___860_64324.use_bv_sorts);
       qtbl_name_and_index = uu____64338;
       normalized_eff_names = uu____64438;
       fv_delta_depths = uu____64441;
       proof_ns = (uu___860_64324.proof_ns);
       synth_hook = (uu___860_64324.synth_hook);
       splice = (uu___860_64324.splice);
       postprocess = (uu___860_64324.postprocess);
       is_native_tactic = (uu___860_64324.is_native_tactic);
       identifier_info = uu____64444;
       tc_hooks = (uu___860_64324.tc_hooks);
       dsenv = (uu___860_64324.dsenv);
       nbe = (uu___860_64324.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____64472  ->
    let uu____64473 = FStar_ST.op_Bang stack  in
    match uu____64473 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____64527 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____64617  ->
           let uu____64618 = snapshot_stack env  in
           match uu____64618 with
           | (stack_depth,env1) ->
               let uu____64652 = snapshot_query_indices ()  in
               (match uu____64652 with
                | (query_indices_depth,()) ->
                    let uu____64685 = (env1.solver).snapshot msg  in
                    (match uu____64685 with
                     | (solver_depth,()) ->
                         let uu____64742 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____64742 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_64809 = env1  in
                                 {
                                   solver = (uu___885_64809.solver);
                                   range = (uu___885_64809.range);
                                   curmodule = (uu___885_64809.curmodule);
                                   gamma = (uu___885_64809.gamma);
                                   gamma_sig = (uu___885_64809.gamma_sig);
                                   gamma_cache = (uu___885_64809.gamma_cache);
                                   modules = (uu___885_64809.modules);
                                   expected_typ =
                                     (uu___885_64809.expected_typ);
                                   sigtab = (uu___885_64809.sigtab);
                                   attrtab = (uu___885_64809.attrtab);
                                   is_pattern = (uu___885_64809.is_pattern);
                                   instantiate_imp =
                                     (uu___885_64809.instantiate_imp);
                                   effects = (uu___885_64809.effects);
                                   generalize = (uu___885_64809.generalize);
                                   letrecs = (uu___885_64809.letrecs);
                                   top_level = (uu___885_64809.top_level);
                                   check_uvars = (uu___885_64809.check_uvars);
                                   use_eq = (uu___885_64809.use_eq);
                                   is_iface = (uu___885_64809.is_iface);
                                   admit = (uu___885_64809.admit);
                                   lax = (uu___885_64809.lax);
                                   lax_universes =
                                     (uu___885_64809.lax_universes);
                                   phase1 = (uu___885_64809.phase1);
                                   failhard = (uu___885_64809.failhard);
                                   nosynth = (uu___885_64809.nosynth);
                                   uvar_subtyping =
                                     (uu___885_64809.uvar_subtyping);
                                   tc_term = (uu___885_64809.tc_term);
                                   type_of = (uu___885_64809.type_of);
                                   universe_of = (uu___885_64809.universe_of);
                                   check_type_of =
                                     (uu___885_64809.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_64809.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_64809.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_64809.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_64809.fv_delta_depths);
                                   proof_ns = (uu___885_64809.proof_ns);
                                   synth_hook = (uu___885_64809.synth_hook);
                                   splice = (uu___885_64809.splice);
                                   postprocess = (uu___885_64809.postprocess);
                                   is_native_tactic =
                                     (uu___885_64809.is_native_tactic);
                                   identifier_info =
                                     (uu___885_64809.identifier_info);
                                   tc_hooks = (uu___885_64809.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_64809.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____64843  ->
             let uu____64844 =
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
             match uu____64844 with
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
                             ((let uu____65024 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____65024
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____65040 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____65040
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____65072,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____65114 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____65144  ->
                  match uu____65144 with
                  | (m,uu____65152) -> FStar_Ident.lid_equals l m))
           in
        (match uu____65114 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_65167 = env  in
               {
                 solver = (uu___930_65167.solver);
                 range = (uu___930_65167.range);
                 curmodule = (uu___930_65167.curmodule);
                 gamma = (uu___930_65167.gamma);
                 gamma_sig = (uu___930_65167.gamma_sig);
                 gamma_cache = (uu___930_65167.gamma_cache);
                 modules = (uu___930_65167.modules);
                 expected_typ = (uu___930_65167.expected_typ);
                 sigtab = (uu___930_65167.sigtab);
                 attrtab = (uu___930_65167.attrtab);
                 is_pattern = (uu___930_65167.is_pattern);
                 instantiate_imp = (uu___930_65167.instantiate_imp);
                 effects = (uu___930_65167.effects);
                 generalize = (uu___930_65167.generalize);
                 letrecs = (uu___930_65167.letrecs);
                 top_level = (uu___930_65167.top_level);
                 check_uvars = (uu___930_65167.check_uvars);
                 use_eq = (uu___930_65167.use_eq);
                 is_iface = (uu___930_65167.is_iface);
                 admit = (uu___930_65167.admit);
                 lax = (uu___930_65167.lax);
                 lax_universes = (uu___930_65167.lax_universes);
                 phase1 = (uu___930_65167.phase1);
                 failhard = (uu___930_65167.failhard);
                 nosynth = (uu___930_65167.nosynth);
                 uvar_subtyping = (uu___930_65167.uvar_subtyping);
                 tc_term = (uu___930_65167.tc_term);
                 type_of = (uu___930_65167.type_of);
                 universe_of = (uu___930_65167.universe_of);
                 check_type_of = (uu___930_65167.check_type_of);
                 use_bv_sorts = (uu___930_65167.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_65167.normalized_eff_names);
                 fv_delta_depths = (uu___930_65167.fv_delta_depths);
                 proof_ns = (uu___930_65167.proof_ns);
                 synth_hook = (uu___930_65167.synth_hook);
                 splice = (uu___930_65167.splice);
                 postprocess = (uu___930_65167.postprocess);
                 is_native_tactic = (uu___930_65167.is_native_tactic);
                 identifier_info = (uu___930_65167.identifier_info);
                 tc_hooks = (uu___930_65167.tc_hooks);
                 dsenv = (uu___930_65167.dsenv);
                 nbe = (uu___930_65167.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____65184,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_65200 = env  in
               {
                 solver = (uu___939_65200.solver);
                 range = (uu___939_65200.range);
                 curmodule = (uu___939_65200.curmodule);
                 gamma = (uu___939_65200.gamma);
                 gamma_sig = (uu___939_65200.gamma_sig);
                 gamma_cache = (uu___939_65200.gamma_cache);
                 modules = (uu___939_65200.modules);
                 expected_typ = (uu___939_65200.expected_typ);
                 sigtab = (uu___939_65200.sigtab);
                 attrtab = (uu___939_65200.attrtab);
                 is_pattern = (uu___939_65200.is_pattern);
                 instantiate_imp = (uu___939_65200.instantiate_imp);
                 effects = (uu___939_65200.effects);
                 generalize = (uu___939_65200.generalize);
                 letrecs = (uu___939_65200.letrecs);
                 top_level = (uu___939_65200.top_level);
                 check_uvars = (uu___939_65200.check_uvars);
                 use_eq = (uu___939_65200.use_eq);
                 is_iface = (uu___939_65200.is_iface);
                 admit = (uu___939_65200.admit);
                 lax = (uu___939_65200.lax);
                 lax_universes = (uu___939_65200.lax_universes);
                 phase1 = (uu___939_65200.phase1);
                 failhard = (uu___939_65200.failhard);
                 nosynth = (uu___939_65200.nosynth);
                 uvar_subtyping = (uu___939_65200.uvar_subtyping);
                 tc_term = (uu___939_65200.tc_term);
                 type_of = (uu___939_65200.type_of);
                 universe_of = (uu___939_65200.universe_of);
                 check_type_of = (uu___939_65200.check_type_of);
                 use_bv_sorts = (uu___939_65200.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_65200.normalized_eff_names);
                 fv_delta_depths = (uu___939_65200.fv_delta_depths);
                 proof_ns = (uu___939_65200.proof_ns);
                 synth_hook = (uu___939_65200.synth_hook);
                 splice = (uu___939_65200.splice);
                 postprocess = (uu___939_65200.postprocess);
                 is_native_tactic = (uu___939_65200.is_native_tactic);
                 identifier_info = (uu___939_65200.identifier_info);
                 tc_hooks = (uu___939_65200.tc_hooks);
                 dsenv = (uu___939_65200.dsenv);
                 nbe = (uu___939_65200.nbe)
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
        (let uu___946_65243 = e  in
         {
           solver = (uu___946_65243.solver);
           range = r;
           curmodule = (uu___946_65243.curmodule);
           gamma = (uu___946_65243.gamma);
           gamma_sig = (uu___946_65243.gamma_sig);
           gamma_cache = (uu___946_65243.gamma_cache);
           modules = (uu___946_65243.modules);
           expected_typ = (uu___946_65243.expected_typ);
           sigtab = (uu___946_65243.sigtab);
           attrtab = (uu___946_65243.attrtab);
           is_pattern = (uu___946_65243.is_pattern);
           instantiate_imp = (uu___946_65243.instantiate_imp);
           effects = (uu___946_65243.effects);
           generalize = (uu___946_65243.generalize);
           letrecs = (uu___946_65243.letrecs);
           top_level = (uu___946_65243.top_level);
           check_uvars = (uu___946_65243.check_uvars);
           use_eq = (uu___946_65243.use_eq);
           is_iface = (uu___946_65243.is_iface);
           admit = (uu___946_65243.admit);
           lax = (uu___946_65243.lax);
           lax_universes = (uu___946_65243.lax_universes);
           phase1 = (uu___946_65243.phase1);
           failhard = (uu___946_65243.failhard);
           nosynth = (uu___946_65243.nosynth);
           uvar_subtyping = (uu___946_65243.uvar_subtyping);
           tc_term = (uu___946_65243.tc_term);
           type_of = (uu___946_65243.type_of);
           universe_of = (uu___946_65243.universe_of);
           check_type_of = (uu___946_65243.check_type_of);
           use_bv_sorts = (uu___946_65243.use_bv_sorts);
           qtbl_name_and_index = (uu___946_65243.qtbl_name_and_index);
           normalized_eff_names = (uu___946_65243.normalized_eff_names);
           fv_delta_depths = (uu___946_65243.fv_delta_depths);
           proof_ns = (uu___946_65243.proof_ns);
           synth_hook = (uu___946_65243.synth_hook);
           splice = (uu___946_65243.splice);
           postprocess = (uu___946_65243.postprocess);
           is_native_tactic = (uu___946_65243.is_native_tactic);
           identifier_info = (uu___946_65243.identifier_info);
           tc_hooks = (uu___946_65243.tc_hooks);
           dsenv = (uu___946_65243.dsenv);
           nbe = (uu___946_65243.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____65263 =
        let uu____65264 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____65264 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65263
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____65319 =
          let uu____65320 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____65320 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65319
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____65375 =
          let uu____65376 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____65376 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65375
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____65431 =
        let uu____65432 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____65432 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65431
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_65496 = env  in
      {
        solver = (uu___963_65496.solver);
        range = (uu___963_65496.range);
        curmodule = lid;
        gamma = (uu___963_65496.gamma);
        gamma_sig = (uu___963_65496.gamma_sig);
        gamma_cache = (uu___963_65496.gamma_cache);
        modules = (uu___963_65496.modules);
        expected_typ = (uu___963_65496.expected_typ);
        sigtab = (uu___963_65496.sigtab);
        attrtab = (uu___963_65496.attrtab);
        is_pattern = (uu___963_65496.is_pattern);
        instantiate_imp = (uu___963_65496.instantiate_imp);
        effects = (uu___963_65496.effects);
        generalize = (uu___963_65496.generalize);
        letrecs = (uu___963_65496.letrecs);
        top_level = (uu___963_65496.top_level);
        check_uvars = (uu___963_65496.check_uvars);
        use_eq = (uu___963_65496.use_eq);
        is_iface = (uu___963_65496.is_iface);
        admit = (uu___963_65496.admit);
        lax = (uu___963_65496.lax);
        lax_universes = (uu___963_65496.lax_universes);
        phase1 = (uu___963_65496.phase1);
        failhard = (uu___963_65496.failhard);
        nosynth = (uu___963_65496.nosynth);
        uvar_subtyping = (uu___963_65496.uvar_subtyping);
        tc_term = (uu___963_65496.tc_term);
        type_of = (uu___963_65496.type_of);
        universe_of = (uu___963_65496.universe_of);
        check_type_of = (uu___963_65496.check_type_of);
        use_bv_sorts = (uu___963_65496.use_bv_sorts);
        qtbl_name_and_index = (uu___963_65496.qtbl_name_and_index);
        normalized_eff_names = (uu___963_65496.normalized_eff_names);
        fv_delta_depths = (uu___963_65496.fv_delta_depths);
        proof_ns = (uu___963_65496.proof_ns);
        synth_hook = (uu___963_65496.synth_hook);
        splice = (uu___963_65496.splice);
        postprocess = (uu___963_65496.postprocess);
        is_native_tactic = (uu___963_65496.is_native_tactic);
        identifier_info = (uu___963_65496.identifier_info);
        tc_hooks = (uu___963_65496.tc_hooks);
        dsenv = (uu___963_65496.dsenv);
        nbe = (uu___963_65496.nbe)
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
      let uu____65527 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____65527
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65540 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____65540)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____65555 =
      let uu____65557 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____65557  in
    (FStar_Errors.Fatal_VariableNotFound, uu____65555)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____65566  ->
    let uu____65567 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____65567
  
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
      | ((formals,t),uu____65667) ->
          let vs = mk_univ_subst formals us  in
          let uu____65691 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____65691)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_65708  ->
    match uu___447_65708 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____65734  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____65754 = inst_tscheme t  in
      match uu____65754 with
      | (us,t1) ->
          let uu____65765 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____65765)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____65786  ->
          match uu____65786 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____65808 =
                         let uu____65810 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____65814 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____65818 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____65820 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____65810 uu____65814 uu____65818 uu____65820
                          in
                       failwith uu____65808)
                    else ();
                    (let uu____65825 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____65825))
               | uu____65834 ->
                   let uu____65835 =
                     let uu____65837 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____65837
                      in
                   failwith uu____65835)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____65849 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____65860 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____65871 -> false
  
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
             | ([],uu____65919) -> Maybe
             | (uu____65926,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____65946 -> No  in
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
          let uu____66040 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____66040 with
          | FStar_Pervasives_Native.None  ->
              let uu____66063 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_66107  ->
                     match uu___448_66107 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____66146 = FStar_Ident.lid_equals lid l  in
                         if uu____66146
                         then
                           let uu____66169 =
                             let uu____66188 =
                               let uu____66203 = inst_tscheme t  in
                               FStar_Util.Inl uu____66203  in
                             let uu____66218 = FStar_Ident.range_of_lid l  in
                             (uu____66188, uu____66218)  in
                           FStar_Pervasives_Native.Some uu____66169
                         else FStar_Pervasives_Native.None
                     | uu____66271 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____66063
                (fun uu____66309  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_66318  ->
                        match uu___449_66318 with
                        | (uu____66321,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____66323);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____66324;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____66325;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____66326;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____66327;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____66347 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____66347
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
                                  uu____66399 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____66406 -> cache t  in
                            let uu____66407 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____66407 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____66413 =
                                   let uu____66414 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____66414)
                                    in
                                 maybe_cache uu____66413)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____66485 = find_in_sigtab env lid  in
         match uu____66485 with
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
      let uu____66566 = lookup_qname env lid  in
      match uu____66566 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____66587,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____66701 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____66701 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____66746 =
          let uu____66749 = lookup_attr env1 attr  in se1 :: uu____66749  in
        FStar_Util.smap_add (attrtab env1) attr uu____66746  in
      FStar_List.iter
        (fun attr  ->
           let uu____66759 =
             let uu____66760 = FStar_Syntax_Subst.compress attr  in
             uu____66760.FStar_Syntax_Syntax.n  in
           match uu____66759 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____66764 =
                 let uu____66766 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____66766.FStar_Ident.str  in
               add_one1 env se uu____66764
           | uu____66767 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____66790) ->
          add_sigelts env ses
      | uu____66799 ->
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
            | uu____66814 -> ()))

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
        (fun uu___450_66846  ->
           match uu___450_66846 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____66864 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____66926,lb::[]),uu____66928) ->
            let uu____66937 =
              let uu____66946 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____66955 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____66946, uu____66955)  in
            FStar_Pervasives_Native.Some uu____66937
        | FStar_Syntax_Syntax.Sig_let ((uu____66968,lbs),uu____66970) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____67002 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____67015 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____67015
                     then
                       let uu____67028 =
                         let uu____67037 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____67046 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____67037, uu____67046)  in
                       FStar_Pervasives_Native.Some uu____67028
                     else FStar_Pervasives_Native.None)
        | uu____67069 -> FStar_Pervasives_Native.None
  
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
          let uu____67129 =
            let uu____67138 =
              let uu____67143 =
                let uu____67144 =
                  let uu____67147 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____67147
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____67144)  in
              inst_tscheme1 uu____67143  in
            (uu____67138, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67129
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____67169,uu____67170) ->
          let uu____67175 =
            let uu____67184 =
              let uu____67189 =
                let uu____67190 =
                  let uu____67193 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____67193  in
                (us, uu____67190)  in
              inst_tscheme1 uu____67189  in
            (uu____67184, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67175
      | uu____67212 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____67301 =
          match uu____67301 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____67397,uvs,t,uu____67400,uu____67401,uu____67402);
                      FStar_Syntax_Syntax.sigrng = uu____67403;
                      FStar_Syntax_Syntax.sigquals = uu____67404;
                      FStar_Syntax_Syntax.sigmeta = uu____67405;
                      FStar_Syntax_Syntax.sigattrs = uu____67406;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67429 =
                     let uu____67438 = inst_tscheme1 (uvs, t)  in
                     (uu____67438, rng)  in
                   FStar_Pervasives_Native.Some uu____67429
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____67462;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____67464;
                      FStar_Syntax_Syntax.sigattrs = uu____67465;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67482 =
                     let uu____67484 = in_cur_mod env l  in uu____67484 = Yes
                      in
                   if uu____67482
                   then
                     let uu____67496 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____67496
                      then
                        let uu____67512 =
                          let uu____67521 = inst_tscheme1 (uvs, t)  in
                          (uu____67521, rng)  in
                        FStar_Pervasives_Native.Some uu____67512
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____67554 =
                        let uu____67563 = inst_tscheme1 (uvs, t)  in
                        (uu____67563, rng)  in
                      FStar_Pervasives_Native.Some uu____67554)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67588,uu____67589);
                      FStar_Syntax_Syntax.sigrng = uu____67590;
                      FStar_Syntax_Syntax.sigquals = uu____67591;
                      FStar_Syntax_Syntax.sigmeta = uu____67592;
                      FStar_Syntax_Syntax.sigattrs = uu____67593;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____67634 =
                          let uu____67643 = inst_tscheme1 (uvs, k)  in
                          (uu____67643, rng)  in
                        FStar_Pervasives_Native.Some uu____67634
                    | uu____67664 ->
                        let uu____67665 =
                          let uu____67674 =
                            let uu____67679 =
                              let uu____67680 =
                                let uu____67683 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67683
                                 in
                              (uvs, uu____67680)  in
                            inst_tscheme1 uu____67679  in
                          (uu____67674, rng)  in
                        FStar_Pervasives_Native.Some uu____67665)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67706,uu____67707);
                      FStar_Syntax_Syntax.sigrng = uu____67708;
                      FStar_Syntax_Syntax.sigquals = uu____67709;
                      FStar_Syntax_Syntax.sigmeta = uu____67710;
                      FStar_Syntax_Syntax.sigattrs = uu____67711;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____67753 =
                          let uu____67762 = inst_tscheme_with (uvs, k) us  in
                          (uu____67762, rng)  in
                        FStar_Pervasives_Native.Some uu____67753
                    | uu____67783 ->
                        let uu____67784 =
                          let uu____67793 =
                            let uu____67798 =
                              let uu____67799 =
                                let uu____67802 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67802
                                 in
                              (uvs, uu____67799)  in
                            inst_tscheme_with uu____67798 us  in
                          (uu____67793, rng)  in
                        FStar_Pervasives_Native.Some uu____67784)
               | FStar_Util.Inr se ->
                   let uu____67838 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____67859;
                          FStar_Syntax_Syntax.sigrng = uu____67860;
                          FStar_Syntax_Syntax.sigquals = uu____67861;
                          FStar_Syntax_Syntax.sigmeta = uu____67862;
                          FStar_Syntax_Syntax.sigattrs = uu____67863;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____67878 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____67838
                     (FStar_Util.map_option
                        (fun uu____67926  ->
                           match uu____67926 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____67957 =
          let uu____67968 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____67968 mapper  in
        match uu____67957 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____68042 =
              let uu____68053 =
                let uu____68060 =
                  let uu___1290_68063 = t  in
                  let uu____68064 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_68063.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____68064;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_68063.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____68060)  in
              (uu____68053, r)  in
            FStar_Pervasives_Native.Some uu____68042
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____68113 = lookup_qname env l  in
      match uu____68113 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____68134 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____68188 = try_lookup_bv env bv  in
      match uu____68188 with
      | FStar_Pervasives_Native.None  ->
          let uu____68203 = variable_not_found bv  in
          FStar_Errors.raise_error uu____68203 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____68219 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____68220 =
            let uu____68221 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____68221  in
          (uu____68219, uu____68220)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____68243 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____68243 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____68309 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____68309  in
          let uu____68310 =
            let uu____68319 =
              let uu____68324 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____68324)  in
            (uu____68319, r1)  in
          FStar_Pervasives_Native.Some uu____68310
  
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
        let uu____68359 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____68359 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____68392,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____68417 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____68417  in
            let uu____68418 =
              let uu____68423 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____68423, r1)  in
            FStar_Pervasives_Native.Some uu____68418
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____68447 = try_lookup_lid env l  in
      match uu____68447 with
      | FStar_Pervasives_Native.None  ->
          let uu____68474 = name_not_found l  in
          let uu____68480 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____68474 uu____68480
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_68523  ->
              match uu___451_68523 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____68527 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____68548 = lookup_qname env lid  in
      match uu____68548 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68557,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68560;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____68562;
              FStar_Syntax_Syntax.sigattrs = uu____68563;_},FStar_Pervasives_Native.None
            ),uu____68564)
          ->
          let uu____68613 =
            let uu____68620 =
              let uu____68621 =
                let uu____68624 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____68624 t  in
              (uvs, uu____68621)  in
            (uu____68620, q)  in
          FStar_Pervasives_Native.Some uu____68613
      | uu____68637 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68659 = lookup_qname env lid  in
      match uu____68659 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68664,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68667;
              FStar_Syntax_Syntax.sigquals = uu____68668;
              FStar_Syntax_Syntax.sigmeta = uu____68669;
              FStar_Syntax_Syntax.sigattrs = uu____68670;_},FStar_Pervasives_Native.None
            ),uu____68671)
          ->
          let uu____68720 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68720 (uvs, t)
      | uu____68725 ->
          let uu____68726 = name_not_found lid  in
          let uu____68732 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68726 uu____68732
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68752 = lookup_qname env lid  in
      match uu____68752 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68757,uvs,t,uu____68760,uu____68761,uu____68762);
              FStar_Syntax_Syntax.sigrng = uu____68763;
              FStar_Syntax_Syntax.sigquals = uu____68764;
              FStar_Syntax_Syntax.sigmeta = uu____68765;
              FStar_Syntax_Syntax.sigattrs = uu____68766;_},FStar_Pervasives_Native.None
            ),uu____68767)
          ->
          let uu____68822 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68822 (uvs, t)
      | uu____68827 ->
          let uu____68828 = name_not_found lid  in
          let uu____68834 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68828 uu____68834
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____68857 = lookup_qname env lid  in
      match uu____68857 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____68865,uu____68866,uu____68867,uu____68868,uu____68869,dcs);
              FStar_Syntax_Syntax.sigrng = uu____68871;
              FStar_Syntax_Syntax.sigquals = uu____68872;
              FStar_Syntax_Syntax.sigmeta = uu____68873;
              FStar_Syntax_Syntax.sigattrs = uu____68874;_},uu____68875),uu____68876)
          -> (true, dcs)
      | uu____68939 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____68955 = lookup_qname env lid  in
      match uu____68955 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68956,uu____68957,uu____68958,l,uu____68960,uu____68961);
              FStar_Syntax_Syntax.sigrng = uu____68962;
              FStar_Syntax_Syntax.sigquals = uu____68963;
              FStar_Syntax_Syntax.sigmeta = uu____68964;
              FStar_Syntax_Syntax.sigattrs = uu____68965;_},uu____68966),uu____68967)
          -> l
      | uu____69024 ->
          let uu____69025 =
            let uu____69027 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____69027  in
          failwith uu____69025
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69097)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69154) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69178 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69178
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69213 -> FStar_Pervasives_Native.None)
          | uu____69222 -> FStar_Pervasives_Native.None
  
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
        let uu____69284 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____69284
  
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
        let uu____69317 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____69317
  
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
             (FStar_Util.Inl uu____69369,uu____69370) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____69419),uu____69420) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____69469 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____69487 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____69497 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____69514 ->
                  let uu____69521 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____69521
              | FStar_Syntax_Syntax.Sig_let ((uu____69522,lbs),uu____69524)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____69540 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____69540
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____69547 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____69555 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____69556 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____69563 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69564 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____69565 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69566 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____69579 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____69597 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____69597
           (fun d_opt  ->
              let uu____69610 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____69610
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____69620 =
                   let uu____69623 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____69623  in
                 match uu____69620 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____69624 =
                       let uu____69626 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____69626
                        in
                     failwith uu____69624
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____69631 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____69631
                       then
                         let uu____69634 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____69636 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____69638 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____69634 uu____69636 uu____69638
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
        (FStar_Util.Inr (se,uu____69663),uu____69664) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____69713 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____69735),uu____69736) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____69785 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____69807 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____69807
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____69830 = lookup_attrs_of_lid env fv_lid1  in
        match uu____69830 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____69854 =
                      let uu____69855 = FStar_Syntax_Util.un_uinst tm  in
                      uu____69855.FStar_Syntax_Syntax.n  in
                    match uu____69854 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____69860 -> false))
  
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
      let uu____69894 = lookup_qname env ftv  in
      match uu____69894 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69898) ->
          let uu____69943 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____69943 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____69964,t),r) ->
               let uu____69979 =
                 let uu____69980 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____69980 t  in
               FStar_Pervasives_Native.Some uu____69979)
      | uu____69981 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____69993 = try_lookup_effect_lid env ftv  in
      match uu____69993 with
      | FStar_Pervasives_Native.None  ->
          let uu____69996 = name_not_found ftv  in
          let uu____70002 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____69996 uu____70002
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
        let uu____70026 = lookup_qname env lid0  in
        match uu____70026 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____70037);
                FStar_Syntax_Syntax.sigrng = uu____70038;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____70040;
                FStar_Syntax_Syntax.sigattrs = uu____70041;_},FStar_Pervasives_Native.None
              ),uu____70042)
            ->
            let lid1 =
              let uu____70096 =
                let uu____70097 = FStar_Ident.range_of_lid lid  in
                let uu____70098 =
                  let uu____70099 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____70099  in
                FStar_Range.set_use_range uu____70097 uu____70098  in
              FStar_Ident.set_lid_range lid uu____70096  in
            let uu____70100 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_70106  ->
                      match uu___452_70106 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____70109 -> false))
               in
            if uu____70100
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____70128 =
                      let uu____70130 =
                        let uu____70132 = get_range env  in
                        FStar_Range.string_of_range uu____70132  in
                      let uu____70133 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____70135 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____70130 uu____70133 uu____70135
                       in
                    failwith uu____70128)
                  in
               match (binders, univs1) with
               | ([],uu____70156) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____70182,uu____70183::uu____70184::uu____70185) ->
                   let uu____70206 =
                     let uu____70208 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____70210 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____70208 uu____70210
                      in
                   failwith uu____70206
               | uu____70221 ->
                   let uu____70236 =
                     let uu____70241 =
                       let uu____70242 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____70242)  in
                     inst_tscheme_with uu____70241 insts  in
                   (match uu____70236 with
                    | (uu____70255,t) ->
                        let t1 =
                          let uu____70258 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____70258 t  in
                        let uu____70259 =
                          let uu____70260 = FStar_Syntax_Subst.compress t1
                             in
                          uu____70260.FStar_Syntax_Syntax.n  in
                        (match uu____70259 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____70295 -> failwith "Impossible")))
        | uu____70303 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____70327 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____70327 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____70340,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____70347 = find1 l2  in
            (match uu____70347 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____70354 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____70354 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____70358 = find1 l  in
            (match uu____70358 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____70363 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____70363
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____70378 = lookup_qname env l1  in
      match uu____70378 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____70381;
              FStar_Syntax_Syntax.sigrng = uu____70382;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____70384;
              FStar_Syntax_Syntax.sigattrs = uu____70385;_},uu____70386),uu____70387)
          -> q
      | uu____70438 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____70462 =
          let uu____70463 =
            let uu____70465 = FStar_Util.string_of_int i  in
            let uu____70467 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____70465 uu____70467
             in
          failwith uu____70463  in
        let uu____70470 = lookup_datacon env lid  in
        match uu____70470 with
        | (uu____70475,t) ->
            let uu____70477 =
              let uu____70478 = FStar_Syntax_Subst.compress t  in
              uu____70478.FStar_Syntax_Syntax.n  in
            (match uu____70477 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70482) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____70526 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____70526
                      FStar_Pervasives_Native.fst)
             | uu____70537 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70551 = lookup_qname env l  in
      match uu____70551 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____70553,uu____70554,uu____70555);
              FStar_Syntax_Syntax.sigrng = uu____70556;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70558;
              FStar_Syntax_Syntax.sigattrs = uu____70559;_},uu____70560),uu____70561)
          ->
          FStar_Util.for_some
            (fun uu___453_70614  ->
               match uu___453_70614 with
               | FStar_Syntax_Syntax.Projector uu____70616 -> true
               | uu____70622 -> false) quals
      | uu____70624 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70638 = lookup_qname env lid  in
      match uu____70638 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____70640,uu____70641,uu____70642,uu____70643,uu____70644,uu____70645);
              FStar_Syntax_Syntax.sigrng = uu____70646;
              FStar_Syntax_Syntax.sigquals = uu____70647;
              FStar_Syntax_Syntax.sigmeta = uu____70648;
              FStar_Syntax_Syntax.sigattrs = uu____70649;_},uu____70650),uu____70651)
          -> true
      | uu____70709 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70723 = lookup_qname env lid  in
      match uu____70723 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____70725,uu____70726,uu____70727,uu____70728,uu____70729,uu____70730);
              FStar_Syntax_Syntax.sigrng = uu____70731;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70733;
              FStar_Syntax_Syntax.sigattrs = uu____70734;_},uu____70735),uu____70736)
          ->
          FStar_Util.for_some
            (fun uu___454_70797  ->
               match uu___454_70797 with
               | FStar_Syntax_Syntax.RecordType uu____70799 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____70809 -> true
               | uu____70819 -> false) quals
      | uu____70821 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____70831,uu____70832);
            FStar_Syntax_Syntax.sigrng = uu____70833;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____70835;
            FStar_Syntax_Syntax.sigattrs = uu____70836;_},uu____70837),uu____70838)
        ->
        FStar_Util.for_some
          (fun uu___455_70895  ->
             match uu___455_70895 with
             | FStar_Syntax_Syntax.Action uu____70897 -> true
             | uu____70899 -> false) quals
    | uu____70901 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70915 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____70915
  
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
      let uu____70932 =
        let uu____70933 = FStar_Syntax_Util.un_uinst head1  in
        uu____70933.FStar_Syntax_Syntax.n  in
      match uu____70932 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____70939 ->
               true
           | uu____70942 -> false)
      | uu____70944 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70958 = lookup_qname env l  in
      match uu____70958 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____70961),uu____70962) ->
          FStar_Util.for_some
            (fun uu___456_71010  ->
               match uu___456_71010 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____71013 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____71015 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____71091 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____71109) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____71127 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____71135 ->
                 FStar_Pervasives_Native.Some true
             | uu____71154 -> FStar_Pervasives_Native.Some false)
         in
      let uu____71157 =
        let uu____71161 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____71161 mapper  in
      match uu____71157 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____71221 = lookup_qname env lid  in
      match uu____71221 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71225,uu____71226,tps,uu____71228,uu____71229,uu____71230);
              FStar_Syntax_Syntax.sigrng = uu____71231;
              FStar_Syntax_Syntax.sigquals = uu____71232;
              FStar_Syntax_Syntax.sigmeta = uu____71233;
              FStar_Syntax_Syntax.sigattrs = uu____71234;_},uu____71235),uu____71236)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____71302 -> FStar_Pervasives_Native.None
  
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
           (fun uu____71348  ->
              match uu____71348 with
              | (d,uu____71357) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____71373 = effect_decl_opt env l  in
      match uu____71373 with
      | FStar_Pervasives_Native.None  ->
          let uu____71388 = name_not_found l  in
          let uu____71394 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____71388 uu____71394
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____71417  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____71436  ->
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
        let uu____71468 = FStar_Ident.lid_equals l1 l2  in
        if uu____71468
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____71479 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____71479
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____71490 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____71543  ->
                        match uu____71543 with
                        | (m1,m2,uu____71557,uu____71558,uu____71559) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____71490 with
              | FStar_Pervasives_Native.None  ->
                  let uu____71576 =
                    let uu____71582 =
                      let uu____71584 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____71586 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____71584
                        uu____71586
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____71582)
                     in
                  FStar_Errors.raise_error uu____71576 env.range
              | FStar_Pervasives_Native.Some
                  (uu____71596,uu____71597,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____71631 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____71631
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
  'Auu____71651 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____71651) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____71680 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____71706  ->
                match uu____71706 with
                | (d,uu____71713) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____71680 with
      | FStar_Pervasives_Native.None  ->
          let uu____71724 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____71724
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____71739 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____71739 with
           | (uu____71754,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____71772)::(wp,uu____71774)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____71830 -> failwith "Impossible"))
  
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
          let uu____71888 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____71888
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____71893 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____71893
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
                  let uu____71904 = get_range env  in
                  let uu____71905 =
                    let uu____71912 =
                      let uu____71913 =
                        let uu____71930 =
                          let uu____71941 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____71941]  in
                        (null_wp, uu____71930)  in
                      FStar_Syntax_Syntax.Tm_app uu____71913  in
                    FStar_Syntax_Syntax.mk uu____71912  in
                  uu____71905 FStar_Pervasives_Native.None uu____71904  in
                let uu____71978 =
                  let uu____71979 =
                    let uu____71990 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____71990]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____71979;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____71978))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_72028 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_72028.order);
              joins = (uu___1944_72028.joins)
            }  in
          let uu___1947_72037 = env  in
          {
            solver = (uu___1947_72037.solver);
            range = (uu___1947_72037.range);
            curmodule = (uu___1947_72037.curmodule);
            gamma = (uu___1947_72037.gamma);
            gamma_sig = (uu___1947_72037.gamma_sig);
            gamma_cache = (uu___1947_72037.gamma_cache);
            modules = (uu___1947_72037.modules);
            expected_typ = (uu___1947_72037.expected_typ);
            sigtab = (uu___1947_72037.sigtab);
            attrtab = (uu___1947_72037.attrtab);
            is_pattern = (uu___1947_72037.is_pattern);
            instantiate_imp = (uu___1947_72037.instantiate_imp);
            effects;
            generalize = (uu___1947_72037.generalize);
            letrecs = (uu___1947_72037.letrecs);
            top_level = (uu___1947_72037.top_level);
            check_uvars = (uu___1947_72037.check_uvars);
            use_eq = (uu___1947_72037.use_eq);
            is_iface = (uu___1947_72037.is_iface);
            admit = (uu___1947_72037.admit);
            lax = (uu___1947_72037.lax);
            lax_universes = (uu___1947_72037.lax_universes);
            phase1 = (uu___1947_72037.phase1);
            failhard = (uu___1947_72037.failhard);
            nosynth = (uu___1947_72037.nosynth);
            uvar_subtyping = (uu___1947_72037.uvar_subtyping);
            tc_term = (uu___1947_72037.tc_term);
            type_of = (uu___1947_72037.type_of);
            universe_of = (uu___1947_72037.universe_of);
            check_type_of = (uu___1947_72037.check_type_of);
            use_bv_sorts = (uu___1947_72037.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_72037.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_72037.normalized_eff_names);
            fv_delta_depths = (uu___1947_72037.fv_delta_depths);
            proof_ns = (uu___1947_72037.proof_ns);
            synth_hook = (uu___1947_72037.synth_hook);
            splice = (uu___1947_72037.splice);
            postprocess = (uu___1947_72037.postprocess);
            is_native_tactic = (uu___1947_72037.is_native_tactic);
            identifier_info = (uu___1947_72037.identifier_info);
            tc_hooks = (uu___1947_72037.tc_hooks);
            dsenv = (uu___1947_72037.dsenv);
            nbe = (uu___1947_72037.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____72067 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____72067  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____72225 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____72226 = l1 u t wp e  in
                                l2 u t uu____72225 uu____72226))
                | uu____72227 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____72299 = inst_tscheme_with lift_t [u]  in
            match uu____72299 with
            | (uu____72306,lift_t1) ->
                let uu____72308 =
                  let uu____72315 =
                    let uu____72316 =
                      let uu____72333 =
                        let uu____72344 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72353 =
                          let uu____72364 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____72364]  in
                        uu____72344 :: uu____72353  in
                      (lift_t1, uu____72333)  in
                    FStar_Syntax_Syntax.Tm_app uu____72316  in
                  FStar_Syntax_Syntax.mk uu____72315  in
                uu____72308 FStar_Pervasives_Native.None
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
            let uu____72474 = inst_tscheme_with lift_t [u]  in
            match uu____72474 with
            | (uu____72481,lift_t1) ->
                let uu____72483 =
                  let uu____72490 =
                    let uu____72491 =
                      let uu____72508 =
                        let uu____72519 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72528 =
                          let uu____72539 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____72548 =
                            let uu____72559 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____72559]  in
                          uu____72539 :: uu____72548  in
                        uu____72519 :: uu____72528  in
                      (lift_t1, uu____72508)  in
                    FStar_Syntax_Syntax.Tm_app uu____72491  in
                  FStar_Syntax_Syntax.mk uu____72490  in
                uu____72483 FStar_Pervasives_Native.None
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
              let uu____72661 =
                let uu____72662 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____72662
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____72661  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____72671 =
              let uu____72673 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____72673  in
            let uu____72674 =
              let uu____72676 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____72704 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____72704)
                 in
              FStar_Util.dflt "none" uu____72676  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____72671
              uu____72674
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____72733  ->
                    match uu____72733 with
                    | (e,uu____72741) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____72764 =
            match uu____72764 with
            | (i,j) ->
                let uu____72775 = FStar_Ident.lid_equals i j  in
                if uu____72775
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _72782  -> FStar_Pervasives_Native.Some _72782)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____72811 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____72821 = FStar_Ident.lid_equals i k  in
                        if uu____72821
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____72835 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____72835
                                  then []
                                  else
                                    (let uu____72842 =
                                       let uu____72851 =
                                         find_edge order1 (i, k)  in
                                       let uu____72854 =
                                         find_edge order1 (k, j)  in
                                       (uu____72851, uu____72854)  in
                                     match uu____72842 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____72869 =
                                           compose_edges e1 e2  in
                                         [uu____72869]
                                     | uu____72870 -> [])))))
                 in
              FStar_List.append order1 uu____72811  in
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
                   let uu____72900 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____72903 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____72903
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____72900
                   then
                     let uu____72910 =
                       let uu____72916 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____72916)
                        in
                     let uu____72920 = get_range env  in
                     FStar_Errors.raise_error uu____72910 uu____72920
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____72998 = FStar_Ident.lid_equals i j
                                   in
                                if uu____72998
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____73050 =
                                              let uu____73059 =
                                                find_edge order2 (i, k)  in
                                              let uu____73062 =
                                                find_edge order2 (j, k)  in
                                              (uu____73059, uu____73062)  in
                                            match uu____73050 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____73104,uu____73105)
                                                     ->
                                                     let uu____73112 =
                                                       let uu____73119 =
                                                         let uu____73121 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73121
                                                          in
                                                       let uu____73124 =
                                                         let uu____73126 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73126
                                                          in
                                                       (uu____73119,
                                                         uu____73124)
                                                        in
                                                     (match uu____73112 with
                                                      | (true ,true ) ->
                                                          let uu____73143 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____73143
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
                                            | uu____73186 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_73259 = env.effects  in
              { decls = (uu___2074_73259.decls); order = order2; joins }  in
            let uu___2077_73260 = env  in
            {
              solver = (uu___2077_73260.solver);
              range = (uu___2077_73260.range);
              curmodule = (uu___2077_73260.curmodule);
              gamma = (uu___2077_73260.gamma);
              gamma_sig = (uu___2077_73260.gamma_sig);
              gamma_cache = (uu___2077_73260.gamma_cache);
              modules = (uu___2077_73260.modules);
              expected_typ = (uu___2077_73260.expected_typ);
              sigtab = (uu___2077_73260.sigtab);
              attrtab = (uu___2077_73260.attrtab);
              is_pattern = (uu___2077_73260.is_pattern);
              instantiate_imp = (uu___2077_73260.instantiate_imp);
              effects;
              generalize = (uu___2077_73260.generalize);
              letrecs = (uu___2077_73260.letrecs);
              top_level = (uu___2077_73260.top_level);
              check_uvars = (uu___2077_73260.check_uvars);
              use_eq = (uu___2077_73260.use_eq);
              is_iface = (uu___2077_73260.is_iface);
              admit = (uu___2077_73260.admit);
              lax = (uu___2077_73260.lax);
              lax_universes = (uu___2077_73260.lax_universes);
              phase1 = (uu___2077_73260.phase1);
              failhard = (uu___2077_73260.failhard);
              nosynth = (uu___2077_73260.nosynth);
              uvar_subtyping = (uu___2077_73260.uvar_subtyping);
              tc_term = (uu___2077_73260.tc_term);
              type_of = (uu___2077_73260.type_of);
              universe_of = (uu___2077_73260.universe_of);
              check_type_of = (uu___2077_73260.check_type_of);
              use_bv_sorts = (uu___2077_73260.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_73260.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_73260.normalized_eff_names);
              fv_delta_depths = (uu___2077_73260.fv_delta_depths);
              proof_ns = (uu___2077_73260.proof_ns);
              synth_hook = (uu___2077_73260.synth_hook);
              splice = (uu___2077_73260.splice);
              postprocess = (uu___2077_73260.postprocess);
              is_native_tactic = (uu___2077_73260.is_native_tactic);
              identifier_info = (uu___2077_73260.identifier_info);
              tc_hooks = (uu___2077_73260.tc_hooks);
              dsenv = (uu___2077_73260.dsenv);
              nbe = (uu___2077_73260.nbe)
            }))
      | uu____73261 -> env
  
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
        | uu____73290 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____73303 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____73303 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____73320 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____73320 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____73345 =
                     let uu____73351 =
                       let uu____73353 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____73361 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____73372 =
                         let uu____73374 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____73374  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____73353 uu____73361 uu____73372
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____73351)
                      in
                   FStar_Errors.raise_error uu____73345
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____73382 =
                     let uu____73393 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____73393 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____73430  ->
                        fun uu____73431  ->
                          match (uu____73430, uu____73431) with
                          | ((x,uu____73461),(t,uu____73463)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____73382
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____73494 =
                     let uu___2115_73495 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_73495.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_73495.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_73495.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_73495.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____73494
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____73507 .
    'Auu____73507 ->
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
          let uu____73537 = effect_decl_opt env effect_name  in
          match uu____73537 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____73576 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____73599 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____73638 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____73638
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____73643 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____73643
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____73658 =
                     let uu____73661 = get_range env  in
                     let uu____73662 =
                       let uu____73669 =
                         let uu____73670 =
                           let uu____73687 =
                             let uu____73698 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____73698; wp]  in
                           (repr, uu____73687)  in
                         FStar_Syntax_Syntax.Tm_app uu____73670  in
                       FStar_Syntax_Syntax.mk uu____73669  in
                     uu____73662 FStar_Pervasives_Native.None uu____73661  in
                   FStar_Pervasives_Native.Some uu____73658)
  
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
      | uu____73842 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____73857 =
        let uu____73858 = FStar_Syntax_Subst.compress t  in
        uu____73858.FStar_Syntax_Syntax.n  in
      match uu____73857 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____73862,c) ->
          is_reifiable_comp env c
      | uu____73884 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____73904 =
           let uu____73906 = is_reifiable_effect env l  in
           Prims.op_Negation uu____73906  in
         if uu____73904
         then
           let uu____73909 =
             let uu____73915 =
               let uu____73917 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____73917
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____73915)  in
           let uu____73921 = get_range env  in
           FStar_Errors.raise_error uu____73909 uu____73921
         else ());
        (let uu____73924 = effect_repr_aux true env c u_c  in
         match uu____73924 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_73960 = env  in
        {
          solver = (uu___2180_73960.solver);
          range = (uu___2180_73960.range);
          curmodule = (uu___2180_73960.curmodule);
          gamma = (uu___2180_73960.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_73960.gamma_cache);
          modules = (uu___2180_73960.modules);
          expected_typ = (uu___2180_73960.expected_typ);
          sigtab = (uu___2180_73960.sigtab);
          attrtab = (uu___2180_73960.attrtab);
          is_pattern = (uu___2180_73960.is_pattern);
          instantiate_imp = (uu___2180_73960.instantiate_imp);
          effects = (uu___2180_73960.effects);
          generalize = (uu___2180_73960.generalize);
          letrecs = (uu___2180_73960.letrecs);
          top_level = (uu___2180_73960.top_level);
          check_uvars = (uu___2180_73960.check_uvars);
          use_eq = (uu___2180_73960.use_eq);
          is_iface = (uu___2180_73960.is_iface);
          admit = (uu___2180_73960.admit);
          lax = (uu___2180_73960.lax);
          lax_universes = (uu___2180_73960.lax_universes);
          phase1 = (uu___2180_73960.phase1);
          failhard = (uu___2180_73960.failhard);
          nosynth = (uu___2180_73960.nosynth);
          uvar_subtyping = (uu___2180_73960.uvar_subtyping);
          tc_term = (uu___2180_73960.tc_term);
          type_of = (uu___2180_73960.type_of);
          universe_of = (uu___2180_73960.universe_of);
          check_type_of = (uu___2180_73960.check_type_of);
          use_bv_sorts = (uu___2180_73960.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_73960.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_73960.normalized_eff_names);
          fv_delta_depths = (uu___2180_73960.fv_delta_depths);
          proof_ns = (uu___2180_73960.proof_ns);
          synth_hook = (uu___2180_73960.synth_hook);
          splice = (uu___2180_73960.splice);
          postprocess = (uu___2180_73960.postprocess);
          is_native_tactic = (uu___2180_73960.is_native_tactic);
          identifier_info = (uu___2180_73960.identifier_info);
          tc_hooks = (uu___2180_73960.tc_hooks);
          dsenv = (uu___2180_73960.dsenv);
          nbe = (uu___2180_73960.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_73974 = env  in
      {
        solver = (uu___2187_73974.solver);
        range = (uu___2187_73974.range);
        curmodule = (uu___2187_73974.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_73974.gamma_sig);
        gamma_cache = (uu___2187_73974.gamma_cache);
        modules = (uu___2187_73974.modules);
        expected_typ = (uu___2187_73974.expected_typ);
        sigtab = (uu___2187_73974.sigtab);
        attrtab = (uu___2187_73974.attrtab);
        is_pattern = (uu___2187_73974.is_pattern);
        instantiate_imp = (uu___2187_73974.instantiate_imp);
        effects = (uu___2187_73974.effects);
        generalize = (uu___2187_73974.generalize);
        letrecs = (uu___2187_73974.letrecs);
        top_level = (uu___2187_73974.top_level);
        check_uvars = (uu___2187_73974.check_uvars);
        use_eq = (uu___2187_73974.use_eq);
        is_iface = (uu___2187_73974.is_iface);
        admit = (uu___2187_73974.admit);
        lax = (uu___2187_73974.lax);
        lax_universes = (uu___2187_73974.lax_universes);
        phase1 = (uu___2187_73974.phase1);
        failhard = (uu___2187_73974.failhard);
        nosynth = (uu___2187_73974.nosynth);
        uvar_subtyping = (uu___2187_73974.uvar_subtyping);
        tc_term = (uu___2187_73974.tc_term);
        type_of = (uu___2187_73974.type_of);
        universe_of = (uu___2187_73974.universe_of);
        check_type_of = (uu___2187_73974.check_type_of);
        use_bv_sorts = (uu___2187_73974.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_73974.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_73974.normalized_eff_names);
        fv_delta_depths = (uu___2187_73974.fv_delta_depths);
        proof_ns = (uu___2187_73974.proof_ns);
        synth_hook = (uu___2187_73974.synth_hook);
        splice = (uu___2187_73974.splice);
        postprocess = (uu___2187_73974.postprocess);
        is_native_tactic = (uu___2187_73974.is_native_tactic);
        identifier_info = (uu___2187_73974.identifier_info);
        tc_hooks = (uu___2187_73974.tc_hooks);
        dsenv = (uu___2187_73974.dsenv);
        nbe = (uu___2187_73974.nbe)
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
            (let uu___2200_74032 = env  in
             {
               solver = (uu___2200_74032.solver);
               range = (uu___2200_74032.range);
               curmodule = (uu___2200_74032.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_74032.gamma_sig);
               gamma_cache = (uu___2200_74032.gamma_cache);
               modules = (uu___2200_74032.modules);
               expected_typ = (uu___2200_74032.expected_typ);
               sigtab = (uu___2200_74032.sigtab);
               attrtab = (uu___2200_74032.attrtab);
               is_pattern = (uu___2200_74032.is_pattern);
               instantiate_imp = (uu___2200_74032.instantiate_imp);
               effects = (uu___2200_74032.effects);
               generalize = (uu___2200_74032.generalize);
               letrecs = (uu___2200_74032.letrecs);
               top_level = (uu___2200_74032.top_level);
               check_uvars = (uu___2200_74032.check_uvars);
               use_eq = (uu___2200_74032.use_eq);
               is_iface = (uu___2200_74032.is_iface);
               admit = (uu___2200_74032.admit);
               lax = (uu___2200_74032.lax);
               lax_universes = (uu___2200_74032.lax_universes);
               phase1 = (uu___2200_74032.phase1);
               failhard = (uu___2200_74032.failhard);
               nosynth = (uu___2200_74032.nosynth);
               uvar_subtyping = (uu___2200_74032.uvar_subtyping);
               tc_term = (uu___2200_74032.tc_term);
               type_of = (uu___2200_74032.type_of);
               universe_of = (uu___2200_74032.universe_of);
               check_type_of = (uu___2200_74032.check_type_of);
               use_bv_sorts = (uu___2200_74032.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_74032.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_74032.normalized_eff_names);
               fv_delta_depths = (uu___2200_74032.fv_delta_depths);
               proof_ns = (uu___2200_74032.proof_ns);
               synth_hook = (uu___2200_74032.synth_hook);
               splice = (uu___2200_74032.splice);
               postprocess = (uu___2200_74032.postprocess);
               is_native_tactic = (uu___2200_74032.is_native_tactic);
               identifier_info = (uu___2200_74032.identifier_info);
               tc_hooks = (uu___2200_74032.tc_hooks);
               dsenv = (uu___2200_74032.dsenv);
               nbe = (uu___2200_74032.nbe)
             }))
    | uu____74033 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____74062  ->
             match uu____74062 with | (x,uu____74070) -> push_bv env1 x) env
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
            let uu___2214_74105 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_74105.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_74105.FStar_Syntax_Syntax.index);
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
      (let uu___2225_74147 = env  in
       {
         solver = (uu___2225_74147.solver);
         range = (uu___2225_74147.range);
         curmodule = (uu___2225_74147.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_74147.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_74147.sigtab);
         attrtab = (uu___2225_74147.attrtab);
         is_pattern = (uu___2225_74147.is_pattern);
         instantiate_imp = (uu___2225_74147.instantiate_imp);
         effects = (uu___2225_74147.effects);
         generalize = (uu___2225_74147.generalize);
         letrecs = (uu___2225_74147.letrecs);
         top_level = (uu___2225_74147.top_level);
         check_uvars = (uu___2225_74147.check_uvars);
         use_eq = (uu___2225_74147.use_eq);
         is_iface = (uu___2225_74147.is_iface);
         admit = (uu___2225_74147.admit);
         lax = (uu___2225_74147.lax);
         lax_universes = (uu___2225_74147.lax_universes);
         phase1 = (uu___2225_74147.phase1);
         failhard = (uu___2225_74147.failhard);
         nosynth = (uu___2225_74147.nosynth);
         uvar_subtyping = (uu___2225_74147.uvar_subtyping);
         tc_term = (uu___2225_74147.tc_term);
         type_of = (uu___2225_74147.type_of);
         universe_of = (uu___2225_74147.universe_of);
         check_type_of = (uu___2225_74147.check_type_of);
         use_bv_sorts = (uu___2225_74147.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_74147.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_74147.normalized_eff_names);
         fv_delta_depths = (uu___2225_74147.fv_delta_depths);
         proof_ns = (uu___2225_74147.proof_ns);
         synth_hook = (uu___2225_74147.synth_hook);
         splice = (uu___2225_74147.splice);
         postprocess = (uu___2225_74147.postprocess);
         is_native_tactic = (uu___2225_74147.is_native_tactic);
         identifier_info = (uu___2225_74147.identifier_info);
         tc_hooks = (uu___2225_74147.tc_hooks);
         dsenv = (uu___2225_74147.dsenv);
         nbe = (uu___2225_74147.nbe)
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
        let uu____74191 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____74191 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____74219 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____74219)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_74235 = env  in
      {
        solver = (uu___2240_74235.solver);
        range = (uu___2240_74235.range);
        curmodule = (uu___2240_74235.curmodule);
        gamma = (uu___2240_74235.gamma);
        gamma_sig = (uu___2240_74235.gamma_sig);
        gamma_cache = (uu___2240_74235.gamma_cache);
        modules = (uu___2240_74235.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_74235.sigtab);
        attrtab = (uu___2240_74235.attrtab);
        is_pattern = (uu___2240_74235.is_pattern);
        instantiate_imp = (uu___2240_74235.instantiate_imp);
        effects = (uu___2240_74235.effects);
        generalize = (uu___2240_74235.generalize);
        letrecs = (uu___2240_74235.letrecs);
        top_level = (uu___2240_74235.top_level);
        check_uvars = (uu___2240_74235.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_74235.is_iface);
        admit = (uu___2240_74235.admit);
        lax = (uu___2240_74235.lax);
        lax_universes = (uu___2240_74235.lax_universes);
        phase1 = (uu___2240_74235.phase1);
        failhard = (uu___2240_74235.failhard);
        nosynth = (uu___2240_74235.nosynth);
        uvar_subtyping = (uu___2240_74235.uvar_subtyping);
        tc_term = (uu___2240_74235.tc_term);
        type_of = (uu___2240_74235.type_of);
        universe_of = (uu___2240_74235.universe_of);
        check_type_of = (uu___2240_74235.check_type_of);
        use_bv_sorts = (uu___2240_74235.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_74235.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_74235.normalized_eff_names);
        fv_delta_depths = (uu___2240_74235.fv_delta_depths);
        proof_ns = (uu___2240_74235.proof_ns);
        synth_hook = (uu___2240_74235.synth_hook);
        splice = (uu___2240_74235.splice);
        postprocess = (uu___2240_74235.postprocess);
        is_native_tactic = (uu___2240_74235.is_native_tactic);
        identifier_info = (uu___2240_74235.identifier_info);
        tc_hooks = (uu___2240_74235.tc_hooks);
        dsenv = (uu___2240_74235.dsenv);
        nbe = (uu___2240_74235.nbe)
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
    let uu____74266 = expected_typ env_  in
    ((let uu___2247_74272 = env_  in
      {
        solver = (uu___2247_74272.solver);
        range = (uu___2247_74272.range);
        curmodule = (uu___2247_74272.curmodule);
        gamma = (uu___2247_74272.gamma);
        gamma_sig = (uu___2247_74272.gamma_sig);
        gamma_cache = (uu___2247_74272.gamma_cache);
        modules = (uu___2247_74272.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_74272.sigtab);
        attrtab = (uu___2247_74272.attrtab);
        is_pattern = (uu___2247_74272.is_pattern);
        instantiate_imp = (uu___2247_74272.instantiate_imp);
        effects = (uu___2247_74272.effects);
        generalize = (uu___2247_74272.generalize);
        letrecs = (uu___2247_74272.letrecs);
        top_level = (uu___2247_74272.top_level);
        check_uvars = (uu___2247_74272.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_74272.is_iface);
        admit = (uu___2247_74272.admit);
        lax = (uu___2247_74272.lax);
        lax_universes = (uu___2247_74272.lax_universes);
        phase1 = (uu___2247_74272.phase1);
        failhard = (uu___2247_74272.failhard);
        nosynth = (uu___2247_74272.nosynth);
        uvar_subtyping = (uu___2247_74272.uvar_subtyping);
        tc_term = (uu___2247_74272.tc_term);
        type_of = (uu___2247_74272.type_of);
        universe_of = (uu___2247_74272.universe_of);
        check_type_of = (uu___2247_74272.check_type_of);
        use_bv_sorts = (uu___2247_74272.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_74272.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_74272.normalized_eff_names);
        fv_delta_depths = (uu___2247_74272.fv_delta_depths);
        proof_ns = (uu___2247_74272.proof_ns);
        synth_hook = (uu___2247_74272.synth_hook);
        splice = (uu___2247_74272.splice);
        postprocess = (uu___2247_74272.postprocess);
        is_native_tactic = (uu___2247_74272.is_native_tactic);
        identifier_info = (uu___2247_74272.identifier_info);
        tc_hooks = (uu___2247_74272.tc_hooks);
        dsenv = (uu___2247_74272.dsenv);
        nbe = (uu___2247_74272.nbe)
      }), uu____74266)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____74284 =
      let uu____74287 = FStar_Ident.id_of_text ""  in [uu____74287]  in
    FStar_Ident.lid_of_ids uu____74284  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____74294 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____74294
        then
          let uu____74299 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____74299 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_74327 = env  in
       {
         solver = (uu___2255_74327.solver);
         range = (uu___2255_74327.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_74327.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_74327.expected_typ);
         sigtab = (uu___2255_74327.sigtab);
         attrtab = (uu___2255_74327.attrtab);
         is_pattern = (uu___2255_74327.is_pattern);
         instantiate_imp = (uu___2255_74327.instantiate_imp);
         effects = (uu___2255_74327.effects);
         generalize = (uu___2255_74327.generalize);
         letrecs = (uu___2255_74327.letrecs);
         top_level = (uu___2255_74327.top_level);
         check_uvars = (uu___2255_74327.check_uvars);
         use_eq = (uu___2255_74327.use_eq);
         is_iface = (uu___2255_74327.is_iface);
         admit = (uu___2255_74327.admit);
         lax = (uu___2255_74327.lax);
         lax_universes = (uu___2255_74327.lax_universes);
         phase1 = (uu___2255_74327.phase1);
         failhard = (uu___2255_74327.failhard);
         nosynth = (uu___2255_74327.nosynth);
         uvar_subtyping = (uu___2255_74327.uvar_subtyping);
         tc_term = (uu___2255_74327.tc_term);
         type_of = (uu___2255_74327.type_of);
         universe_of = (uu___2255_74327.universe_of);
         check_type_of = (uu___2255_74327.check_type_of);
         use_bv_sorts = (uu___2255_74327.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_74327.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_74327.normalized_eff_names);
         fv_delta_depths = (uu___2255_74327.fv_delta_depths);
         proof_ns = (uu___2255_74327.proof_ns);
         synth_hook = (uu___2255_74327.synth_hook);
         splice = (uu___2255_74327.splice);
         postprocess = (uu___2255_74327.postprocess);
         is_native_tactic = (uu___2255_74327.is_native_tactic);
         identifier_info = (uu___2255_74327.identifier_info);
         tc_hooks = (uu___2255_74327.tc_hooks);
         dsenv = (uu___2255_74327.dsenv);
         nbe = (uu___2255_74327.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74379)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74383,(uu____74384,t)))::tl1
          ->
          let uu____74405 =
            let uu____74408 = FStar_Syntax_Free.uvars t  in
            ext out uu____74408  in
          aux uu____74405 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74411;
            FStar_Syntax_Syntax.index = uu____74412;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74420 =
            let uu____74423 = FStar_Syntax_Free.uvars t  in
            ext out uu____74423  in
          aux uu____74420 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74481)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74485,(uu____74486,t)))::tl1
          ->
          let uu____74507 =
            let uu____74510 = FStar_Syntax_Free.univs t  in
            ext out uu____74510  in
          aux uu____74507 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74513;
            FStar_Syntax_Syntax.index = uu____74514;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74522 =
            let uu____74525 = FStar_Syntax_Free.univs t  in
            ext out uu____74525  in
          aux uu____74522 tl1
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
          let uu____74587 = FStar_Util.set_add uname out  in
          aux uu____74587 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74590,(uu____74591,t)))::tl1
          ->
          let uu____74612 =
            let uu____74615 = FStar_Syntax_Free.univnames t  in
            ext out uu____74615  in
          aux uu____74612 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74618;
            FStar_Syntax_Syntax.index = uu____74619;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74627 =
            let uu____74630 = FStar_Syntax_Free.univnames t  in
            ext out uu____74630  in
          aux uu____74627 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_74651  ->
            match uu___457_74651 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____74655 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____74668 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____74679 =
      let uu____74688 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____74688
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____74679 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____74736 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_74749  ->
              match uu___458_74749 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____74752 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____74752
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____74758) ->
                  let uu____74775 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____74775))
       in
    FStar_All.pipe_right uu____74736 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_74789  ->
    match uu___459_74789 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____74795 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____74795
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____74818  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____74873) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____74906,uu____74907) -> false  in
      let uu____74921 =
        FStar_List.tryFind
          (fun uu____74943  ->
             match uu____74943 with | (p,uu____74954) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____74921 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____74973,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75003 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____75003
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_75025 = e  in
        {
          solver = (uu___2398_75025.solver);
          range = (uu___2398_75025.range);
          curmodule = (uu___2398_75025.curmodule);
          gamma = (uu___2398_75025.gamma);
          gamma_sig = (uu___2398_75025.gamma_sig);
          gamma_cache = (uu___2398_75025.gamma_cache);
          modules = (uu___2398_75025.modules);
          expected_typ = (uu___2398_75025.expected_typ);
          sigtab = (uu___2398_75025.sigtab);
          attrtab = (uu___2398_75025.attrtab);
          is_pattern = (uu___2398_75025.is_pattern);
          instantiate_imp = (uu___2398_75025.instantiate_imp);
          effects = (uu___2398_75025.effects);
          generalize = (uu___2398_75025.generalize);
          letrecs = (uu___2398_75025.letrecs);
          top_level = (uu___2398_75025.top_level);
          check_uvars = (uu___2398_75025.check_uvars);
          use_eq = (uu___2398_75025.use_eq);
          is_iface = (uu___2398_75025.is_iface);
          admit = (uu___2398_75025.admit);
          lax = (uu___2398_75025.lax);
          lax_universes = (uu___2398_75025.lax_universes);
          phase1 = (uu___2398_75025.phase1);
          failhard = (uu___2398_75025.failhard);
          nosynth = (uu___2398_75025.nosynth);
          uvar_subtyping = (uu___2398_75025.uvar_subtyping);
          tc_term = (uu___2398_75025.tc_term);
          type_of = (uu___2398_75025.type_of);
          universe_of = (uu___2398_75025.universe_of);
          check_type_of = (uu___2398_75025.check_type_of);
          use_bv_sorts = (uu___2398_75025.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_75025.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_75025.normalized_eff_names);
          fv_delta_depths = (uu___2398_75025.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_75025.synth_hook);
          splice = (uu___2398_75025.splice);
          postprocess = (uu___2398_75025.postprocess);
          is_native_tactic = (uu___2398_75025.is_native_tactic);
          identifier_info = (uu___2398_75025.identifier_info);
          tc_hooks = (uu___2398_75025.tc_hooks);
          dsenv = (uu___2398_75025.dsenv);
          nbe = (uu___2398_75025.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_75073 = e  in
      {
        solver = (uu___2407_75073.solver);
        range = (uu___2407_75073.range);
        curmodule = (uu___2407_75073.curmodule);
        gamma = (uu___2407_75073.gamma);
        gamma_sig = (uu___2407_75073.gamma_sig);
        gamma_cache = (uu___2407_75073.gamma_cache);
        modules = (uu___2407_75073.modules);
        expected_typ = (uu___2407_75073.expected_typ);
        sigtab = (uu___2407_75073.sigtab);
        attrtab = (uu___2407_75073.attrtab);
        is_pattern = (uu___2407_75073.is_pattern);
        instantiate_imp = (uu___2407_75073.instantiate_imp);
        effects = (uu___2407_75073.effects);
        generalize = (uu___2407_75073.generalize);
        letrecs = (uu___2407_75073.letrecs);
        top_level = (uu___2407_75073.top_level);
        check_uvars = (uu___2407_75073.check_uvars);
        use_eq = (uu___2407_75073.use_eq);
        is_iface = (uu___2407_75073.is_iface);
        admit = (uu___2407_75073.admit);
        lax = (uu___2407_75073.lax);
        lax_universes = (uu___2407_75073.lax_universes);
        phase1 = (uu___2407_75073.phase1);
        failhard = (uu___2407_75073.failhard);
        nosynth = (uu___2407_75073.nosynth);
        uvar_subtyping = (uu___2407_75073.uvar_subtyping);
        tc_term = (uu___2407_75073.tc_term);
        type_of = (uu___2407_75073.type_of);
        universe_of = (uu___2407_75073.universe_of);
        check_type_of = (uu___2407_75073.check_type_of);
        use_bv_sorts = (uu___2407_75073.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_75073.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_75073.normalized_eff_names);
        fv_delta_depths = (uu___2407_75073.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_75073.synth_hook);
        splice = (uu___2407_75073.splice);
        postprocess = (uu___2407_75073.postprocess);
        is_native_tactic = (uu___2407_75073.is_native_tactic);
        identifier_info = (uu___2407_75073.identifier_info);
        tc_hooks = (uu___2407_75073.tc_hooks);
        dsenv = (uu___2407_75073.dsenv);
        nbe = (uu___2407_75073.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____75089 = FStar_Syntax_Free.names t  in
      let uu____75092 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____75089 uu____75092
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____75115 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____75115
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____75125 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____75125
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____75146 =
      match uu____75146 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____75166 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____75166)
       in
    let uu____75174 =
      let uu____75178 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____75178 FStar_List.rev  in
    FStar_All.pipe_right uu____75174 (FStar_String.concat " ")
  
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
                  (let uu____75248 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____75248 with
                   | FStar_Pervasives_Native.Some uu____75252 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____75255 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____75265;
        univ_ineqs = uu____75266; implicits = uu____75267;_} -> true
    | uu____75279 -> false
  
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
          let uu___2451_75310 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_75310.deferred);
            univ_ineqs = (uu___2451_75310.univ_ineqs);
            implicits = (uu___2451_75310.implicits)
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
          let uu____75349 = FStar_Options.defensive ()  in
          if uu____75349
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____75355 =
              let uu____75357 =
                let uu____75359 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____75359  in
              Prims.op_Negation uu____75357  in
            (if uu____75355
             then
               let uu____75366 =
                 let uu____75372 =
                   let uu____75374 = FStar_Syntax_Print.term_to_string t  in
                   let uu____75376 =
                     let uu____75378 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____75378
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____75374 uu____75376
                    in
                 (FStar_Errors.Warning_Defensive, uu____75372)  in
               FStar_Errors.log_issue rng uu____75366
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
          let uu____75418 =
            let uu____75420 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75420  in
          if uu____75418
          then ()
          else
            (let uu____75425 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____75425 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____75451 =
            let uu____75453 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75453  in
          if uu____75451
          then ()
          else
            (let uu____75458 = bound_vars e  in
             def_check_closed_in rng msg uu____75458 t)
  
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
          let uu___2488_75497 = g  in
          let uu____75498 =
            let uu____75499 =
              let uu____75500 =
                let uu____75507 =
                  let uu____75508 =
                    let uu____75525 =
                      let uu____75536 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____75536]  in
                    (f, uu____75525)  in
                  FStar_Syntax_Syntax.Tm_app uu____75508  in
                FStar_Syntax_Syntax.mk uu____75507  in
              uu____75500 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _75573  -> FStar_TypeChecker_Common.NonTrivial _75573)
              uu____75499
             in
          {
            guard_f = uu____75498;
            deferred = (uu___2488_75497.deferred);
            univ_ineqs = (uu___2488_75497.univ_ineqs);
            implicits = (uu___2488_75497.implicits)
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
          let uu___2495_75591 = g  in
          let uu____75592 =
            let uu____75593 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75593  in
          {
            guard_f = uu____75592;
            deferred = (uu___2495_75591.deferred);
            univ_ineqs = (uu___2495_75591.univ_ineqs);
            implicits = (uu___2495_75591.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_75610 = g  in
          let uu____75611 =
            let uu____75612 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____75612  in
          {
            guard_f = uu____75611;
            deferred = (uu___2500_75610.deferred);
            univ_ineqs = (uu___2500_75610.univ_ineqs);
            implicits = (uu___2500_75610.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_75614 = g  in
          let uu____75615 =
            let uu____75616 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75616  in
          {
            guard_f = uu____75615;
            deferred = (uu___2504_75614.deferred);
            univ_ineqs = (uu___2504_75614.univ_ineqs);
            implicits = (uu___2504_75614.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____75623 ->
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
          let uu____75640 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____75640
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____75647 =
      let uu____75648 = FStar_Syntax_Util.unmeta t  in
      uu____75648.FStar_Syntax_Syntax.n  in
    match uu____75647 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____75652 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____75695 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____75695;
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
                       let uu____75790 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____75790
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_75797 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_75797.deferred);
              univ_ineqs = (uu___2559_75797.univ_ineqs);
              implicits = (uu___2559_75797.implicits)
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
               let uu____75831 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____75831
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
            let uu___2574_75858 = g  in
            let uu____75859 =
              let uu____75860 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____75860  in
            {
              guard_f = uu____75859;
              deferred = (uu___2574_75858.deferred);
              univ_ineqs = (uu___2574_75858.univ_ineqs);
              implicits = (uu___2574_75858.implicits)
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
              let uu____75918 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____75918 with
              | FStar_Pervasives_Native.Some
                  (uu____75943::(tm,uu____75945)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____76009 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____76027 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____76027;
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
                      let uu___2596_76059 = trivial_guard  in
                      {
                        guard_f = (uu___2596_76059.guard_f);
                        deferred = (uu___2596_76059.deferred);
                        univ_ineqs = (uu___2596_76059.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____76077  -> ());
    push = (fun uu____76079  -> ());
    pop = (fun uu____76082  -> ());
    snapshot =
      (fun uu____76085  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____76104  -> fun uu____76105  -> ());
    encode_sig = (fun uu____76120  -> fun uu____76121  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____76127 =
             let uu____76134 = FStar_Options.peek ()  in (e, g, uu____76134)
              in
           [uu____76127]);
    solve = (fun uu____76150  -> fun uu____76151  -> fun uu____76152  -> ());
    finish = (fun uu____76159  -> ());
    refresh = (fun uu____76161  -> ())
  } 