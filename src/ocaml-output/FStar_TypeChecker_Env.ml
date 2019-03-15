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
    match projectee with | Beta  -> true | uu____51445 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____51456 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____51467 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____51479 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____51497 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____51508 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____51519 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____51530 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____51541 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____51552 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____51564 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____51585 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____51612 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____51639 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____51663 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____51674 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____51685 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____51696 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____51707 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____51718 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____51729 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____51740 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____51751 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____51762 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____51773 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____51784 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____51795 -> false
  
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
      | uu____51855 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____51881 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____51892 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____51903 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____51915 -> false
  
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
           (fun uu___446_63132  ->
              match uu___446_63132 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____63135 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____63135  in
                  let uu____63136 =
                    let uu____63137 = FStar_Syntax_Subst.compress y  in
                    uu____63137.FStar_Syntax_Syntax.n  in
                  (match uu____63136 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____63141 =
                         let uu___775_63142 = y1  in
                         let uu____63143 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_63142.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_63142.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____63143
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____63141
                   | uu____63146 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_63160 = env  in
      let uu____63161 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_63160.solver);
        range = (uu___781_63160.range);
        curmodule = (uu___781_63160.curmodule);
        gamma = uu____63161;
        gamma_sig = (uu___781_63160.gamma_sig);
        gamma_cache = (uu___781_63160.gamma_cache);
        modules = (uu___781_63160.modules);
        expected_typ = (uu___781_63160.expected_typ);
        sigtab = (uu___781_63160.sigtab);
        attrtab = (uu___781_63160.attrtab);
        is_pattern = (uu___781_63160.is_pattern);
        instantiate_imp = (uu___781_63160.instantiate_imp);
        effects = (uu___781_63160.effects);
        generalize = (uu___781_63160.generalize);
        letrecs = (uu___781_63160.letrecs);
        top_level = (uu___781_63160.top_level);
        check_uvars = (uu___781_63160.check_uvars);
        use_eq = (uu___781_63160.use_eq);
        is_iface = (uu___781_63160.is_iface);
        admit = (uu___781_63160.admit);
        lax = (uu___781_63160.lax);
        lax_universes = (uu___781_63160.lax_universes);
        phase1 = (uu___781_63160.phase1);
        failhard = (uu___781_63160.failhard);
        nosynth = (uu___781_63160.nosynth);
        uvar_subtyping = (uu___781_63160.uvar_subtyping);
        tc_term = (uu___781_63160.tc_term);
        type_of = (uu___781_63160.type_of);
        universe_of = (uu___781_63160.universe_of);
        check_type_of = (uu___781_63160.check_type_of);
        use_bv_sorts = (uu___781_63160.use_bv_sorts);
        qtbl_name_and_index = (uu___781_63160.qtbl_name_and_index);
        normalized_eff_names = (uu___781_63160.normalized_eff_names);
        fv_delta_depths = (uu___781_63160.fv_delta_depths);
        proof_ns = (uu___781_63160.proof_ns);
        synth_hook = (uu___781_63160.synth_hook);
        splice = (uu___781_63160.splice);
        postprocess = (uu___781_63160.postprocess);
        is_native_tactic = (uu___781_63160.is_native_tactic);
        identifier_info = (uu___781_63160.identifier_info);
        tc_hooks = (uu___781_63160.tc_hooks);
        dsenv = (uu___781_63160.dsenv);
        nbe = (uu___781_63160.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____63169  -> fun uu____63170  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_63192 = env  in
      {
        solver = (uu___788_63192.solver);
        range = (uu___788_63192.range);
        curmodule = (uu___788_63192.curmodule);
        gamma = (uu___788_63192.gamma);
        gamma_sig = (uu___788_63192.gamma_sig);
        gamma_cache = (uu___788_63192.gamma_cache);
        modules = (uu___788_63192.modules);
        expected_typ = (uu___788_63192.expected_typ);
        sigtab = (uu___788_63192.sigtab);
        attrtab = (uu___788_63192.attrtab);
        is_pattern = (uu___788_63192.is_pattern);
        instantiate_imp = (uu___788_63192.instantiate_imp);
        effects = (uu___788_63192.effects);
        generalize = (uu___788_63192.generalize);
        letrecs = (uu___788_63192.letrecs);
        top_level = (uu___788_63192.top_level);
        check_uvars = (uu___788_63192.check_uvars);
        use_eq = (uu___788_63192.use_eq);
        is_iface = (uu___788_63192.is_iface);
        admit = (uu___788_63192.admit);
        lax = (uu___788_63192.lax);
        lax_universes = (uu___788_63192.lax_universes);
        phase1 = (uu___788_63192.phase1);
        failhard = (uu___788_63192.failhard);
        nosynth = (uu___788_63192.nosynth);
        uvar_subtyping = (uu___788_63192.uvar_subtyping);
        tc_term = (uu___788_63192.tc_term);
        type_of = (uu___788_63192.type_of);
        universe_of = (uu___788_63192.universe_of);
        check_type_of = (uu___788_63192.check_type_of);
        use_bv_sorts = (uu___788_63192.use_bv_sorts);
        qtbl_name_and_index = (uu___788_63192.qtbl_name_and_index);
        normalized_eff_names = (uu___788_63192.normalized_eff_names);
        fv_delta_depths = (uu___788_63192.fv_delta_depths);
        proof_ns = (uu___788_63192.proof_ns);
        synth_hook = (uu___788_63192.synth_hook);
        splice = (uu___788_63192.splice);
        postprocess = (uu___788_63192.postprocess);
        is_native_tactic = (uu___788_63192.is_native_tactic);
        identifier_info = (uu___788_63192.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_63192.dsenv);
        nbe = (uu___788_63192.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_63204 = e  in
      let uu____63205 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_63204.solver);
        range = (uu___792_63204.range);
        curmodule = (uu___792_63204.curmodule);
        gamma = (uu___792_63204.gamma);
        gamma_sig = (uu___792_63204.gamma_sig);
        gamma_cache = (uu___792_63204.gamma_cache);
        modules = (uu___792_63204.modules);
        expected_typ = (uu___792_63204.expected_typ);
        sigtab = (uu___792_63204.sigtab);
        attrtab = (uu___792_63204.attrtab);
        is_pattern = (uu___792_63204.is_pattern);
        instantiate_imp = (uu___792_63204.instantiate_imp);
        effects = (uu___792_63204.effects);
        generalize = (uu___792_63204.generalize);
        letrecs = (uu___792_63204.letrecs);
        top_level = (uu___792_63204.top_level);
        check_uvars = (uu___792_63204.check_uvars);
        use_eq = (uu___792_63204.use_eq);
        is_iface = (uu___792_63204.is_iface);
        admit = (uu___792_63204.admit);
        lax = (uu___792_63204.lax);
        lax_universes = (uu___792_63204.lax_universes);
        phase1 = (uu___792_63204.phase1);
        failhard = (uu___792_63204.failhard);
        nosynth = (uu___792_63204.nosynth);
        uvar_subtyping = (uu___792_63204.uvar_subtyping);
        tc_term = (uu___792_63204.tc_term);
        type_of = (uu___792_63204.type_of);
        universe_of = (uu___792_63204.universe_of);
        check_type_of = (uu___792_63204.check_type_of);
        use_bv_sorts = (uu___792_63204.use_bv_sorts);
        qtbl_name_and_index = (uu___792_63204.qtbl_name_and_index);
        normalized_eff_names = (uu___792_63204.normalized_eff_names);
        fv_delta_depths = (uu___792_63204.fv_delta_depths);
        proof_ns = (uu___792_63204.proof_ns);
        synth_hook = (uu___792_63204.synth_hook);
        splice = (uu___792_63204.splice);
        postprocess = (uu___792_63204.postprocess);
        is_native_tactic = (uu___792_63204.is_native_tactic);
        identifier_info = (uu___792_63204.identifier_info);
        tc_hooks = (uu___792_63204.tc_hooks);
        dsenv = uu____63205;
        nbe = (uu___792_63204.nbe)
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
      | (NoDelta ,uu____63234) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____63237,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____63239,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____63242 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____63256 . unit -> 'Auu____63256 FStar_Util.smap =
  fun uu____63263  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____63269 . unit -> 'Auu____63269 FStar_Util.smap =
  fun uu____63276  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____63414 = new_gamma_cache ()  in
                  let uu____63417 = new_sigtab ()  in
                  let uu____63420 = new_sigtab ()  in
                  let uu____63427 =
                    let uu____63442 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____63442, FStar_Pervasives_Native.None)  in
                  let uu____63463 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____63467 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____63471 = FStar_Options.using_facts_from ()  in
                  let uu____63472 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____63475 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____63414;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____63417;
                    attrtab = uu____63420;
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
                    qtbl_name_and_index = uu____63427;
                    normalized_eff_names = uu____63463;
                    fv_delta_depths = uu____63467;
                    proof_ns = uu____63471;
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
                    is_native_tactic = (fun uu____63537  -> false);
                    identifier_info = uu____63472;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____63475;
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
  fun uu____63616  ->
    let uu____63617 = FStar_ST.op_Bang query_indices  in
    match uu____63617 with
    | [] -> failwith "Empty query indices!"
    | uu____63672 ->
        let uu____63682 =
          let uu____63692 =
            let uu____63700 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____63700  in
          let uu____63754 = FStar_ST.op_Bang query_indices  in uu____63692 ::
            uu____63754
           in
        FStar_ST.op_Colon_Equals query_indices uu____63682
  
let (pop_query_indices : unit -> unit) =
  fun uu____63850  ->
    let uu____63851 = FStar_ST.op_Bang query_indices  in
    match uu____63851 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____63978  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____64015  ->
    match uu____64015 with
    | (l,n1) ->
        let uu____64025 = FStar_ST.op_Bang query_indices  in
        (match uu____64025 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____64147 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____64170  ->
    let uu____64171 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____64171
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____64239 =
       let uu____64242 = FStar_ST.op_Bang stack  in env :: uu____64242  in
     FStar_ST.op_Colon_Equals stack uu____64239);
    (let uu___860_64291 = env  in
     let uu____64292 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____64295 = FStar_Util.smap_copy (sigtab env)  in
     let uu____64298 = FStar_Util.smap_copy (attrtab env)  in
     let uu____64305 =
       let uu____64320 =
         let uu____64324 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____64324  in
       let uu____64356 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____64320, uu____64356)  in
     let uu____64405 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____64408 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____64411 =
       let uu____64414 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____64414  in
     {
       solver = (uu___860_64291.solver);
       range = (uu___860_64291.range);
       curmodule = (uu___860_64291.curmodule);
       gamma = (uu___860_64291.gamma);
       gamma_sig = (uu___860_64291.gamma_sig);
       gamma_cache = uu____64292;
       modules = (uu___860_64291.modules);
       expected_typ = (uu___860_64291.expected_typ);
       sigtab = uu____64295;
       attrtab = uu____64298;
       is_pattern = (uu___860_64291.is_pattern);
       instantiate_imp = (uu___860_64291.instantiate_imp);
       effects = (uu___860_64291.effects);
       generalize = (uu___860_64291.generalize);
       letrecs = (uu___860_64291.letrecs);
       top_level = (uu___860_64291.top_level);
       check_uvars = (uu___860_64291.check_uvars);
       use_eq = (uu___860_64291.use_eq);
       is_iface = (uu___860_64291.is_iface);
       admit = (uu___860_64291.admit);
       lax = (uu___860_64291.lax);
       lax_universes = (uu___860_64291.lax_universes);
       phase1 = (uu___860_64291.phase1);
       failhard = (uu___860_64291.failhard);
       nosynth = (uu___860_64291.nosynth);
       uvar_subtyping = (uu___860_64291.uvar_subtyping);
       tc_term = (uu___860_64291.tc_term);
       type_of = (uu___860_64291.type_of);
       universe_of = (uu___860_64291.universe_of);
       check_type_of = (uu___860_64291.check_type_of);
       use_bv_sorts = (uu___860_64291.use_bv_sorts);
       qtbl_name_and_index = uu____64305;
       normalized_eff_names = uu____64405;
       fv_delta_depths = uu____64408;
       proof_ns = (uu___860_64291.proof_ns);
       synth_hook = (uu___860_64291.synth_hook);
       splice = (uu___860_64291.splice);
       postprocess = (uu___860_64291.postprocess);
       is_native_tactic = (uu___860_64291.is_native_tactic);
       identifier_info = uu____64411;
       tc_hooks = (uu___860_64291.tc_hooks);
       dsenv = (uu___860_64291.dsenv);
       nbe = (uu___860_64291.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____64439  ->
    let uu____64440 = FStar_ST.op_Bang stack  in
    match uu____64440 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____64494 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____64584  ->
           let uu____64585 = snapshot_stack env  in
           match uu____64585 with
           | (stack_depth,env1) ->
               let uu____64619 = snapshot_query_indices ()  in
               (match uu____64619 with
                | (query_indices_depth,()) ->
                    let uu____64652 = (env1.solver).snapshot msg  in
                    (match uu____64652 with
                     | (solver_depth,()) ->
                         let uu____64709 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____64709 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_64776 = env1  in
                                 {
                                   solver = (uu___885_64776.solver);
                                   range = (uu___885_64776.range);
                                   curmodule = (uu___885_64776.curmodule);
                                   gamma = (uu___885_64776.gamma);
                                   gamma_sig = (uu___885_64776.gamma_sig);
                                   gamma_cache = (uu___885_64776.gamma_cache);
                                   modules = (uu___885_64776.modules);
                                   expected_typ =
                                     (uu___885_64776.expected_typ);
                                   sigtab = (uu___885_64776.sigtab);
                                   attrtab = (uu___885_64776.attrtab);
                                   is_pattern = (uu___885_64776.is_pattern);
                                   instantiate_imp =
                                     (uu___885_64776.instantiate_imp);
                                   effects = (uu___885_64776.effects);
                                   generalize = (uu___885_64776.generalize);
                                   letrecs = (uu___885_64776.letrecs);
                                   top_level = (uu___885_64776.top_level);
                                   check_uvars = (uu___885_64776.check_uvars);
                                   use_eq = (uu___885_64776.use_eq);
                                   is_iface = (uu___885_64776.is_iface);
                                   admit = (uu___885_64776.admit);
                                   lax = (uu___885_64776.lax);
                                   lax_universes =
                                     (uu___885_64776.lax_universes);
                                   phase1 = (uu___885_64776.phase1);
                                   failhard = (uu___885_64776.failhard);
                                   nosynth = (uu___885_64776.nosynth);
                                   uvar_subtyping =
                                     (uu___885_64776.uvar_subtyping);
                                   tc_term = (uu___885_64776.tc_term);
                                   type_of = (uu___885_64776.type_of);
                                   universe_of = (uu___885_64776.universe_of);
                                   check_type_of =
                                     (uu___885_64776.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_64776.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_64776.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_64776.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_64776.fv_delta_depths);
                                   proof_ns = (uu___885_64776.proof_ns);
                                   synth_hook = (uu___885_64776.synth_hook);
                                   splice = (uu___885_64776.splice);
                                   postprocess = (uu___885_64776.postprocess);
                                   is_native_tactic =
                                     (uu___885_64776.is_native_tactic);
                                   identifier_info =
                                     (uu___885_64776.identifier_info);
                                   tc_hooks = (uu___885_64776.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_64776.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____64810  ->
             let uu____64811 =
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
             match uu____64811 with
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
                             ((let uu____64991 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____64991
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____65007 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____65007
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____65039,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____65081 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____65111  ->
                  match uu____65111 with
                  | (m,uu____65119) -> FStar_Ident.lid_equals l m))
           in
        (match uu____65081 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_65134 = env  in
               {
                 solver = (uu___930_65134.solver);
                 range = (uu___930_65134.range);
                 curmodule = (uu___930_65134.curmodule);
                 gamma = (uu___930_65134.gamma);
                 gamma_sig = (uu___930_65134.gamma_sig);
                 gamma_cache = (uu___930_65134.gamma_cache);
                 modules = (uu___930_65134.modules);
                 expected_typ = (uu___930_65134.expected_typ);
                 sigtab = (uu___930_65134.sigtab);
                 attrtab = (uu___930_65134.attrtab);
                 is_pattern = (uu___930_65134.is_pattern);
                 instantiate_imp = (uu___930_65134.instantiate_imp);
                 effects = (uu___930_65134.effects);
                 generalize = (uu___930_65134.generalize);
                 letrecs = (uu___930_65134.letrecs);
                 top_level = (uu___930_65134.top_level);
                 check_uvars = (uu___930_65134.check_uvars);
                 use_eq = (uu___930_65134.use_eq);
                 is_iface = (uu___930_65134.is_iface);
                 admit = (uu___930_65134.admit);
                 lax = (uu___930_65134.lax);
                 lax_universes = (uu___930_65134.lax_universes);
                 phase1 = (uu___930_65134.phase1);
                 failhard = (uu___930_65134.failhard);
                 nosynth = (uu___930_65134.nosynth);
                 uvar_subtyping = (uu___930_65134.uvar_subtyping);
                 tc_term = (uu___930_65134.tc_term);
                 type_of = (uu___930_65134.type_of);
                 universe_of = (uu___930_65134.universe_of);
                 check_type_of = (uu___930_65134.check_type_of);
                 use_bv_sorts = (uu___930_65134.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_65134.normalized_eff_names);
                 fv_delta_depths = (uu___930_65134.fv_delta_depths);
                 proof_ns = (uu___930_65134.proof_ns);
                 synth_hook = (uu___930_65134.synth_hook);
                 splice = (uu___930_65134.splice);
                 postprocess = (uu___930_65134.postprocess);
                 is_native_tactic = (uu___930_65134.is_native_tactic);
                 identifier_info = (uu___930_65134.identifier_info);
                 tc_hooks = (uu___930_65134.tc_hooks);
                 dsenv = (uu___930_65134.dsenv);
                 nbe = (uu___930_65134.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____65151,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_65167 = env  in
               {
                 solver = (uu___939_65167.solver);
                 range = (uu___939_65167.range);
                 curmodule = (uu___939_65167.curmodule);
                 gamma = (uu___939_65167.gamma);
                 gamma_sig = (uu___939_65167.gamma_sig);
                 gamma_cache = (uu___939_65167.gamma_cache);
                 modules = (uu___939_65167.modules);
                 expected_typ = (uu___939_65167.expected_typ);
                 sigtab = (uu___939_65167.sigtab);
                 attrtab = (uu___939_65167.attrtab);
                 is_pattern = (uu___939_65167.is_pattern);
                 instantiate_imp = (uu___939_65167.instantiate_imp);
                 effects = (uu___939_65167.effects);
                 generalize = (uu___939_65167.generalize);
                 letrecs = (uu___939_65167.letrecs);
                 top_level = (uu___939_65167.top_level);
                 check_uvars = (uu___939_65167.check_uvars);
                 use_eq = (uu___939_65167.use_eq);
                 is_iface = (uu___939_65167.is_iface);
                 admit = (uu___939_65167.admit);
                 lax = (uu___939_65167.lax);
                 lax_universes = (uu___939_65167.lax_universes);
                 phase1 = (uu___939_65167.phase1);
                 failhard = (uu___939_65167.failhard);
                 nosynth = (uu___939_65167.nosynth);
                 uvar_subtyping = (uu___939_65167.uvar_subtyping);
                 tc_term = (uu___939_65167.tc_term);
                 type_of = (uu___939_65167.type_of);
                 universe_of = (uu___939_65167.universe_of);
                 check_type_of = (uu___939_65167.check_type_of);
                 use_bv_sorts = (uu___939_65167.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_65167.normalized_eff_names);
                 fv_delta_depths = (uu___939_65167.fv_delta_depths);
                 proof_ns = (uu___939_65167.proof_ns);
                 synth_hook = (uu___939_65167.synth_hook);
                 splice = (uu___939_65167.splice);
                 postprocess = (uu___939_65167.postprocess);
                 is_native_tactic = (uu___939_65167.is_native_tactic);
                 identifier_info = (uu___939_65167.identifier_info);
                 tc_hooks = (uu___939_65167.tc_hooks);
                 dsenv = (uu___939_65167.dsenv);
                 nbe = (uu___939_65167.nbe)
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
        (let uu___946_65210 = e  in
         {
           solver = (uu___946_65210.solver);
           range = r;
           curmodule = (uu___946_65210.curmodule);
           gamma = (uu___946_65210.gamma);
           gamma_sig = (uu___946_65210.gamma_sig);
           gamma_cache = (uu___946_65210.gamma_cache);
           modules = (uu___946_65210.modules);
           expected_typ = (uu___946_65210.expected_typ);
           sigtab = (uu___946_65210.sigtab);
           attrtab = (uu___946_65210.attrtab);
           is_pattern = (uu___946_65210.is_pattern);
           instantiate_imp = (uu___946_65210.instantiate_imp);
           effects = (uu___946_65210.effects);
           generalize = (uu___946_65210.generalize);
           letrecs = (uu___946_65210.letrecs);
           top_level = (uu___946_65210.top_level);
           check_uvars = (uu___946_65210.check_uvars);
           use_eq = (uu___946_65210.use_eq);
           is_iface = (uu___946_65210.is_iface);
           admit = (uu___946_65210.admit);
           lax = (uu___946_65210.lax);
           lax_universes = (uu___946_65210.lax_universes);
           phase1 = (uu___946_65210.phase1);
           failhard = (uu___946_65210.failhard);
           nosynth = (uu___946_65210.nosynth);
           uvar_subtyping = (uu___946_65210.uvar_subtyping);
           tc_term = (uu___946_65210.tc_term);
           type_of = (uu___946_65210.type_of);
           universe_of = (uu___946_65210.universe_of);
           check_type_of = (uu___946_65210.check_type_of);
           use_bv_sorts = (uu___946_65210.use_bv_sorts);
           qtbl_name_and_index = (uu___946_65210.qtbl_name_and_index);
           normalized_eff_names = (uu___946_65210.normalized_eff_names);
           fv_delta_depths = (uu___946_65210.fv_delta_depths);
           proof_ns = (uu___946_65210.proof_ns);
           synth_hook = (uu___946_65210.synth_hook);
           splice = (uu___946_65210.splice);
           postprocess = (uu___946_65210.postprocess);
           is_native_tactic = (uu___946_65210.is_native_tactic);
           identifier_info = (uu___946_65210.identifier_info);
           tc_hooks = (uu___946_65210.tc_hooks);
           dsenv = (uu___946_65210.dsenv);
           nbe = (uu___946_65210.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____65230 =
        let uu____65231 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____65231 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65230
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____65286 =
          let uu____65287 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____65287 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65286
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____65342 =
          let uu____65343 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____65343 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____65342
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____65398 =
        let uu____65399 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____65399 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65398
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_65463 = env  in
      {
        solver = (uu___963_65463.solver);
        range = (uu___963_65463.range);
        curmodule = lid;
        gamma = (uu___963_65463.gamma);
        gamma_sig = (uu___963_65463.gamma_sig);
        gamma_cache = (uu___963_65463.gamma_cache);
        modules = (uu___963_65463.modules);
        expected_typ = (uu___963_65463.expected_typ);
        sigtab = (uu___963_65463.sigtab);
        attrtab = (uu___963_65463.attrtab);
        is_pattern = (uu___963_65463.is_pattern);
        instantiate_imp = (uu___963_65463.instantiate_imp);
        effects = (uu___963_65463.effects);
        generalize = (uu___963_65463.generalize);
        letrecs = (uu___963_65463.letrecs);
        top_level = (uu___963_65463.top_level);
        check_uvars = (uu___963_65463.check_uvars);
        use_eq = (uu___963_65463.use_eq);
        is_iface = (uu___963_65463.is_iface);
        admit = (uu___963_65463.admit);
        lax = (uu___963_65463.lax);
        lax_universes = (uu___963_65463.lax_universes);
        phase1 = (uu___963_65463.phase1);
        failhard = (uu___963_65463.failhard);
        nosynth = (uu___963_65463.nosynth);
        uvar_subtyping = (uu___963_65463.uvar_subtyping);
        tc_term = (uu___963_65463.tc_term);
        type_of = (uu___963_65463.type_of);
        universe_of = (uu___963_65463.universe_of);
        check_type_of = (uu___963_65463.check_type_of);
        use_bv_sorts = (uu___963_65463.use_bv_sorts);
        qtbl_name_and_index = (uu___963_65463.qtbl_name_and_index);
        normalized_eff_names = (uu___963_65463.normalized_eff_names);
        fv_delta_depths = (uu___963_65463.fv_delta_depths);
        proof_ns = (uu___963_65463.proof_ns);
        synth_hook = (uu___963_65463.synth_hook);
        splice = (uu___963_65463.splice);
        postprocess = (uu___963_65463.postprocess);
        is_native_tactic = (uu___963_65463.is_native_tactic);
        identifier_info = (uu___963_65463.identifier_info);
        tc_hooks = (uu___963_65463.tc_hooks);
        dsenv = (uu___963_65463.dsenv);
        nbe = (uu___963_65463.nbe)
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
      let uu____65494 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____65494
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65507 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____65507)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____65522 =
      let uu____65524 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____65524  in
    (FStar_Errors.Fatal_VariableNotFound, uu____65522)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____65533  ->
    let uu____65534 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____65534
  
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
      | ((formals,t),uu____65634) ->
          let vs = mk_univ_subst formals us  in
          let uu____65658 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____65658)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_65675  ->
    match uu___447_65675 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____65701  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____65721 = inst_tscheme t  in
      match uu____65721 with
      | (us,t1) ->
          let uu____65732 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____65732)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____65753  ->
          match uu____65753 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____65775 =
                         let uu____65777 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____65781 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____65785 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____65787 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____65777 uu____65781 uu____65785 uu____65787
                          in
                       failwith uu____65775)
                    else ();
                    (let uu____65792 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____65792))
               | uu____65801 ->
                   let uu____65802 =
                     let uu____65804 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____65804
                      in
                   failwith uu____65802)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____65816 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____65827 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____65838 -> false
  
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
             | ([],uu____65886) -> Maybe
             | (uu____65893,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____65913 -> No  in
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
          let uu____66007 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____66007 with
          | FStar_Pervasives_Native.None  ->
              let uu____66030 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_66074  ->
                     match uu___448_66074 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____66113 = FStar_Ident.lid_equals lid l  in
                         if uu____66113
                         then
                           let uu____66136 =
                             let uu____66155 =
                               let uu____66170 = inst_tscheme t  in
                               FStar_Util.Inl uu____66170  in
                             let uu____66185 = FStar_Ident.range_of_lid l  in
                             (uu____66155, uu____66185)  in
                           FStar_Pervasives_Native.Some uu____66136
                         else FStar_Pervasives_Native.None
                     | uu____66238 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____66030
                (fun uu____66276  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_66285  ->
                        match uu___449_66285 with
                        | (uu____66288,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____66290);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____66291;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____66292;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____66293;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____66294;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____66314 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____66314
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
                                  uu____66366 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____66373 -> cache t  in
                            let uu____66374 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____66374 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____66380 =
                                   let uu____66381 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____66381)
                                    in
                                 maybe_cache uu____66380)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____66452 = find_in_sigtab env lid  in
         match uu____66452 with
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
      let uu____66533 = lookup_qname env lid  in
      match uu____66533 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____66554,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____66668 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____66668 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____66713 =
          let uu____66716 = lookup_attr env1 attr  in se1 :: uu____66716  in
        FStar_Util.smap_add (attrtab env1) attr uu____66713  in
      FStar_List.iter
        (fun attr  ->
           let uu____66726 =
             let uu____66727 = FStar_Syntax_Subst.compress attr  in
             uu____66727.FStar_Syntax_Syntax.n  in
           match uu____66726 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____66731 =
                 let uu____66733 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____66733.FStar_Ident.str  in
               add_one1 env se uu____66731
           | uu____66734 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____66757) ->
          add_sigelts env ses
      | uu____66766 ->
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
            | uu____66781 -> ()))

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
        (fun uu___450_66813  ->
           match uu___450_66813 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____66831 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____66893,lb::[]),uu____66895) ->
            let uu____66904 =
              let uu____66913 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____66922 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____66913, uu____66922)  in
            FStar_Pervasives_Native.Some uu____66904
        | FStar_Syntax_Syntax.Sig_let ((uu____66935,lbs),uu____66937) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____66969 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____66982 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____66982
                     then
                       let uu____66995 =
                         let uu____67004 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____67013 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____67004, uu____67013)  in
                       FStar_Pervasives_Native.Some uu____66995
                     else FStar_Pervasives_Native.None)
        | uu____67036 -> FStar_Pervasives_Native.None
  
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
          let uu____67096 =
            let uu____67105 =
              let uu____67110 =
                let uu____67111 =
                  let uu____67114 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____67114
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____67111)  in
              inst_tscheme1 uu____67110  in
            (uu____67105, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67096
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____67136,uu____67137) ->
          let uu____67142 =
            let uu____67151 =
              let uu____67156 =
                let uu____67157 =
                  let uu____67160 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____67160  in
                (us, uu____67157)  in
              inst_tscheme1 uu____67156  in
            (uu____67151, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67142
      | uu____67179 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____67268 =
          match uu____67268 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____67364,uvs,t,uu____67367,uu____67368,uu____67369);
                      FStar_Syntax_Syntax.sigrng = uu____67370;
                      FStar_Syntax_Syntax.sigquals = uu____67371;
                      FStar_Syntax_Syntax.sigmeta = uu____67372;
                      FStar_Syntax_Syntax.sigattrs = uu____67373;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67396 =
                     let uu____67405 = inst_tscheme1 (uvs, t)  in
                     (uu____67405, rng)  in
                   FStar_Pervasives_Native.Some uu____67396
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____67429;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____67431;
                      FStar_Syntax_Syntax.sigattrs = uu____67432;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____67449 =
                     let uu____67451 = in_cur_mod env l  in uu____67451 = Yes
                      in
                   if uu____67449
                   then
                     let uu____67463 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____67463
                      then
                        let uu____67479 =
                          let uu____67488 = inst_tscheme1 (uvs, t)  in
                          (uu____67488, rng)  in
                        FStar_Pervasives_Native.Some uu____67479
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____67521 =
                        let uu____67530 = inst_tscheme1 (uvs, t)  in
                        (uu____67530, rng)  in
                      FStar_Pervasives_Native.Some uu____67521)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67555,uu____67556);
                      FStar_Syntax_Syntax.sigrng = uu____67557;
                      FStar_Syntax_Syntax.sigquals = uu____67558;
                      FStar_Syntax_Syntax.sigmeta = uu____67559;
                      FStar_Syntax_Syntax.sigattrs = uu____67560;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____67601 =
                          let uu____67610 = inst_tscheme1 (uvs, k)  in
                          (uu____67610, rng)  in
                        FStar_Pervasives_Native.Some uu____67601
                    | uu____67631 ->
                        let uu____67632 =
                          let uu____67641 =
                            let uu____67646 =
                              let uu____67647 =
                                let uu____67650 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67650
                                 in
                              (uvs, uu____67647)  in
                            inst_tscheme1 uu____67646  in
                          (uu____67641, rng)  in
                        FStar_Pervasives_Native.Some uu____67632)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____67673,uu____67674);
                      FStar_Syntax_Syntax.sigrng = uu____67675;
                      FStar_Syntax_Syntax.sigquals = uu____67676;
                      FStar_Syntax_Syntax.sigmeta = uu____67677;
                      FStar_Syntax_Syntax.sigattrs = uu____67678;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____67720 =
                          let uu____67729 = inst_tscheme_with (uvs, k) us  in
                          (uu____67729, rng)  in
                        FStar_Pervasives_Native.Some uu____67720
                    | uu____67750 ->
                        let uu____67751 =
                          let uu____67760 =
                            let uu____67765 =
                              let uu____67766 =
                                let uu____67769 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____67769
                                 in
                              (uvs, uu____67766)  in
                            inst_tscheme_with uu____67765 us  in
                          (uu____67760, rng)  in
                        FStar_Pervasives_Native.Some uu____67751)
               | FStar_Util.Inr se ->
                   let uu____67805 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____67826;
                          FStar_Syntax_Syntax.sigrng = uu____67827;
                          FStar_Syntax_Syntax.sigquals = uu____67828;
                          FStar_Syntax_Syntax.sigmeta = uu____67829;
                          FStar_Syntax_Syntax.sigattrs = uu____67830;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____67845 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____67805
                     (FStar_Util.map_option
                        (fun uu____67893  ->
                           match uu____67893 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____67924 =
          let uu____67935 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____67935 mapper  in
        match uu____67924 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____68009 =
              let uu____68020 =
                let uu____68027 =
                  let uu___1290_68030 = t  in
                  let uu____68031 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_68030.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____68031;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_68030.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____68027)  in
              (uu____68020, r)  in
            FStar_Pervasives_Native.Some uu____68009
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____68080 = lookup_qname env l  in
      match uu____68080 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____68101 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____68155 = try_lookup_bv env bv  in
      match uu____68155 with
      | FStar_Pervasives_Native.None  ->
          let uu____68170 = variable_not_found bv  in
          FStar_Errors.raise_error uu____68170 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____68186 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____68187 =
            let uu____68188 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____68188  in
          (uu____68186, uu____68187)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____68210 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____68210 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____68276 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____68276  in
          let uu____68277 =
            let uu____68286 =
              let uu____68291 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____68291)  in
            (uu____68286, r1)  in
          FStar_Pervasives_Native.Some uu____68277
  
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
        let uu____68326 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____68326 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____68359,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____68384 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____68384  in
            let uu____68385 =
              let uu____68390 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____68390, r1)  in
            FStar_Pervasives_Native.Some uu____68385
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____68414 = try_lookup_lid env l  in
      match uu____68414 with
      | FStar_Pervasives_Native.None  ->
          let uu____68441 = name_not_found l  in
          let uu____68447 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____68441 uu____68447
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_68490  ->
              match uu___451_68490 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____68494 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____68515 = lookup_qname env lid  in
      match uu____68515 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68524,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68527;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____68529;
              FStar_Syntax_Syntax.sigattrs = uu____68530;_},FStar_Pervasives_Native.None
            ),uu____68531)
          ->
          let uu____68580 =
            let uu____68587 =
              let uu____68588 =
                let uu____68591 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____68591 t  in
              (uvs, uu____68588)  in
            (uu____68587, q)  in
          FStar_Pervasives_Native.Some uu____68580
      | uu____68604 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68626 = lookup_qname env lid  in
      match uu____68626 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____68631,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____68634;
              FStar_Syntax_Syntax.sigquals = uu____68635;
              FStar_Syntax_Syntax.sigmeta = uu____68636;
              FStar_Syntax_Syntax.sigattrs = uu____68637;_},FStar_Pervasives_Native.None
            ),uu____68638)
          ->
          let uu____68687 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68687 (uvs, t)
      | uu____68692 ->
          let uu____68693 = name_not_found lid  in
          let uu____68699 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68693 uu____68699
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____68719 = lookup_qname env lid  in
      match uu____68719 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68724,uvs,t,uu____68727,uu____68728,uu____68729);
              FStar_Syntax_Syntax.sigrng = uu____68730;
              FStar_Syntax_Syntax.sigquals = uu____68731;
              FStar_Syntax_Syntax.sigmeta = uu____68732;
              FStar_Syntax_Syntax.sigattrs = uu____68733;_},FStar_Pervasives_Native.None
            ),uu____68734)
          ->
          let uu____68789 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____68789 (uvs, t)
      | uu____68794 ->
          let uu____68795 = name_not_found lid  in
          let uu____68801 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____68795 uu____68801
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____68824 = lookup_qname env lid  in
      match uu____68824 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____68832,uu____68833,uu____68834,uu____68835,uu____68836,dcs);
              FStar_Syntax_Syntax.sigrng = uu____68838;
              FStar_Syntax_Syntax.sigquals = uu____68839;
              FStar_Syntax_Syntax.sigmeta = uu____68840;
              FStar_Syntax_Syntax.sigattrs = uu____68841;_},uu____68842),uu____68843)
          -> (true, dcs)
      | uu____68906 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____68922 = lookup_qname env lid  in
      match uu____68922 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____68923,uu____68924,uu____68925,l,uu____68927,uu____68928);
              FStar_Syntax_Syntax.sigrng = uu____68929;
              FStar_Syntax_Syntax.sigquals = uu____68930;
              FStar_Syntax_Syntax.sigmeta = uu____68931;
              FStar_Syntax_Syntax.sigattrs = uu____68932;_},uu____68933),uu____68934)
          -> l
      | uu____68991 ->
          let uu____68992 =
            let uu____68994 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____68994  in
          failwith uu____68992
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69064)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69121) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69145 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69145
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69180 -> FStar_Pervasives_Native.None)
          | uu____69189 -> FStar_Pervasives_Native.None
  
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
        let uu____69251 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____69251
  
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
        let uu____69284 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____69284
  
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
             (FStar_Util.Inl uu____69336,uu____69337) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____69386),uu____69387) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____69436 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____69454 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____69464 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____69481 ->
                  let uu____69488 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____69488
              | FStar_Syntax_Syntax.Sig_let ((uu____69489,lbs),uu____69491)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____69507 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____69507
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____69514 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____69522 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____69523 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____69530 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69531 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____69532 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69533 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____69546 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____69564 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____69564
           (fun d_opt  ->
              let uu____69577 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____69577
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____69587 =
                   let uu____69590 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____69590  in
                 match uu____69587 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____69591 =
                       let uu____69593 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____69593
                        in
                     failwith uu____69591
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____69598 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____69598
                       then
                         let uu____69601 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____69603 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____69605 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____69601 uu____69603 uu____69605
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
        (FStar_Util.Inr (se,uu____69630),uu____69631) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____69680 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____69702),uu____69703) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____69752 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____69774 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____69774
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____69797 = lookup_attrs_of_lid env fv_lid1  in
        match uu____69797 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____69821 =
                      let uu____69822 = FStar_Syntax_Util.un_uinst tm  in
                      uu____69822.FStar_Syntax_Syntax.n  in
                    match uu____69821 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____69827 -> false))
  
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
      let uu____69861 = lookup_qname env ftv  in
      match uu____69861 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69865) ->
          let uu____69910 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____69910 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____69931,t),r) ->
               let uu____69946 =
                 let uu____69947 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____69947 t  in
               FStar_Pervasives_Native.Some uu____69946)
      | uu____69948 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____69960 = try_lookup_effect_lid env ftv  in
      match uu____69960 with
      | FStar_Pervasives_Native.None  ->
          let uu____69963 = name_not_found ftv  in
          let uu____69969 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____69963 uu____69969
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
        let uu____69993 = lookup_qname env lid0  in
        match uu____69993 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____70004);
                FStar_Syntax_Syntax.sigrng = uu____70005;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____70007;
                FStar_Syntax_Syntax.sigattrs = uu____70008;_},FStar_Pervasives_Native.None
              ),uu____70009)
            ->
            let lid1 =
              let uu____70063 =
                let uu____70064 = FStar_Ident.range_of_lid lid  in
                let uu____70065 =
                  let uu____70066 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____70066  in
                FStar_Range.set_use_range uu____70064 uu____70065  in
              FStar_Ident.set_lid_range lid uu____70063  in
            let uu____70067 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_70073  ->
                      match uu___452_70073 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____70076 -> false))
               in
            if uu____70067
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____70095 =
                      let uu____70097 =
                        let uu____70099 = get_range env  in
                        FStar_Range.string_of_range uu____70099  in
                      let uu____70100 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____70102 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____70097 uu____70100 uu____70102
                       in
                    failwith uu____70095)
                  in
               match (binders, univs1) with
               | ([],uu____70123) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____70149,uu____70150::uu____70151::uu____70152) ->
                   let uu____70173 =
                     let uu____70175 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____70177 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____70175 uu____70177
                      in
                   failwith uu____70173
               | uu____70188 ->
                   let uu____70203 =
                     let uu____70208 =
                       let uu____70209 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____70209)  in
                     inst_tscheme_with uu____70208 insts  in
                   (match uu____70203 with
                    | (uu____70222,t) ->
                        let t1 =
                          let uu____70225 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____70225 t  in
                        let uu____70226 =
                          let uu____70227 = FStar_Syntax_Subst.compress t1
                             in
                          uu____70227.FStar_Syntax_Syntax.n  in
                        (match uu____70226 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____70262 -> failwith "Impossible")))
        | uu____70270 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____70294 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____70294 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____70307,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____70314 = find1 l2  in
            (match uu____70314 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____70321 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____70321 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____70325 = find1 l  in
            (match uu____70325 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____70330 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____70330
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____70345 = lookup_qname env l1  in
      match uu____70345 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____70348;
              FStar_Syntax_Syntax.sigrng = uu____70349;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____70351;
              FStar_Syntax_Syntax.sigattrs = uu____70352;_},uu____70353),uu____70354)
          -> q
      | uu____70405 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____70429 =
          let uu____70430 =
            let uu____70432 = FStar_Util.string_of_int i  in
            let uu____70434 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____70432 uu____70434
             in
          failwith uu____70430  in
        let uu____70437 = lookup_datacon env lid  in
        match uu____70437 with
        | (uu____70442,t) ->
            let uu____70444 =
              let uu____70445 = FStar_Syntax_Subst.compress t  in
              uu____70445.FStar_Syntax_Syntax.n  in
            (match uu____70444 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70449) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____70493 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____70493
                      FStar_Pervasives_Native.fst)
             | uu____70504 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70518 = lookup_qname env l  in
      match uu____70518 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____70520,uu____70521,uu____70522);
              FStar_Syntax_Syntax.sigrng = uu____70523;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70525;
              FStar_Syntax_Syntax.sigattrs = uu____70526;_},uu____70527),uu____70528)
          ->
          FStar_Util.for_some
            (fun uu___453_70581  ->
               match uu___453_70581 with
               | FStar_Syntax_Syntax.Projector uu____70583 -> true
               | uu____70589 -> false) quals
      | uu____70591 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70605 = lookup_qname env lid  in
      match uu____70605 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____70607,uu____70608,uu____70609,uu____70610,uu____70611,uu____70612);
              FStar_Syntax_Syntax.sigrng = uu____70613;
              FStar_Syntax_Syntax.sigquals = uu____70614;
              FStar_Syntax_Syntax.sigmeta = uu____70615;
              FStar_Syntax_Syntax.sigattrs = uu____70616;_},uu____70617),uu____70618)
          -> true
      | uu____70676 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70690 = lookup_qname env lid  in
      match uu____70690 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____70692,uu____70693,uu____70694,uu____70695,uu____70696,uu____70697);
              FStar_Syntax_Syntax.sigrng = uu____70698;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____70700;
              FStar_Syntax_Syntax.sigattrs = uu____70701;_},uu____70702),uu____70703)
          ->
          FStar_Util.for_some
            (fun uu___454_70764  ->
               match uu___454_70764 with
               | FStar_Syntax_Syntax.RecordType uu____70766 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____70776 -> true
               | uu____70786 -> false) quals
      | uu____70788 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____70798,uu____70799);
            FStar_Syntax_Syntax.sigrng = uu____70800;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____70802;
            FStar_Syntax_Syntax.sigattrs = uu____70803;_},uu____70804),uu____70805)
        ->
        FStar_Util.for_some
          (fun uu___455_70862  ->
             match uu___455_70862 with
             | FStar_Syntax_Syntax.Action uu____70864 -> true
             | uu____70866 -> false) quals
    | uu____70868 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____70882 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____70882
  
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
      let uu____70899 =
        let uu____70900 = FStar_Syntax_Util.un_uinst head1  in
        uu____70900.FStar_Syntax_Syntax.n  in
      match uu____70899 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____70906 ->
               true
           | uu____70909 -> false)
      | uu____70911 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____70925 = lookup_qname env l  in
      match uu____70925 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____70928),uu____70929) ->
          FStar_Util.for_some
            (fun uu___456_70977  ->
               match uu___456_70977 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____70980 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____70982 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____71058 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____71076) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____71094 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____71102 ->
                 FStar_Pervasives_Native.Some true
             | uu____71121 -> FStar_Pervasives_Native.Some false)
         in
      let uu____71124 =
        let uu____71128 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____71128 mapper  in
      match uu____71124 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____71188 = lookup_qname env lid  in
      match uu____71188 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71192,uu____71193,tps,uu____71195,uu____71196,uu____71197);
              FStar_Syntax_Syntax.sigrng = uu____71198;
              FStar_Syntax_Syntax.sigquals = uu____71199;
              FStar_Syntax_Syntax.sigmeta = uu____71200;
              FStar_Syntax_Syntax.sigattrs = uu____71201;_},uu____71202),uu____71203)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____71269 -> FStar_Pervasives_Native.None
  
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
           (fun uu____71315  ->
              match uu____71315 with
              | (d,uu____71324) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____71340 = effect_decl_opt env l  in
      match uu____71340 with
      | FStar_Pervasives_Native.None  ->
          let uu____71355 = name_not_found l  in
          let uu____71361 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____71355 uu____71361
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____71384  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____71403  ->
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
        let uu____71435 = FStar_Ident.lid_equals l1 l2  in
        if uu____71435
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____71446 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____71446
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____71457 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____71510  ->
                        match uu____71510 with
                        | (m1,m2,uu____71524,uu____71525,uu____71526) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____71457 with
              | FStar_Pervasives_Native.None  ->
                  let uu____71543 =
                    let uu____71549 =
                      let uu____71551 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____71553 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____71551
                        uu____71553
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____71549)
                     in
                  FStar_Errors.raise_error uu____71543 env.range
              | FStar_Pervasives_Native.Some
                  (uu____71563,uu____71564,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____71598 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____71598
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
  'Auu____71618 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____71618) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____71647 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____71673  ->
                match uu____71673 with
                | (d,uu____71680) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____71647 with
      | FStar_Pervasives_Native.None  ->
          let uu____71691 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____71691
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____71706 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____71706 with
           | (uu____71721,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____71739)::(wp,uu____71741)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____71797 -> failwith "Impossible"))
  
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
          let uu____71855 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____71855
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____71860 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____71860
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
                  let uu____71871 = get_range env  in
                  let uu____71872 =
                    let uu____71879 =
                      let uu____71880 =
                        let uu____71897 =
                          let uu____71908 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____71908]  in
                        (null_wp, uu____71897)  in
                      FStar_Syntax_Syntax.Tm_app uu____71880  in
                    FStar_Syntax_Syntax.mk uu____71879  in
                  uu____71872 FStar_Pervasives_Native.None uu____71871  in
                let uu____71945 =
                  let uu____71946 =
                    let uu____71957 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____71957]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____71946;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____71945))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_71995 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_71995.order);
              joins = (uu___1944_71995.joins)
            }  in
          let uu___1947_72004 = env  in
          {
            solver = (uu___1947_72004.solver);
            range = (uu___1947_72004.range);
            curmodule = (uu___1947_72004.curmodule);
            gamma = (uu___1947_72004.gamma);
            gamma_sig = (uu___1947_72004.gamma_sig);
            gamma_cache = (uu___1947_72004.gamma_cache);
            modules = (uu___1947_72004.modules);
            expected_typ = (uu___1947_72004.expected_typ);
            sigtab = (uu___1947_72004.sigtab);
            attrtab = (uu___1947_72004.attrtab);
            is_pattern = (uu___1947_72004.is_pattern);
            instantiate_imp = (uu___1947_72004.instantiate_imp);
            effects;
            generalize = (uu___1947_72004.generalize);
            letrecs = (uu___1947_72004.letrecs);
            top_level = (uu___1947_72004.top_level);
            check_uvars = (uu___1947_72004.check_uvars);
            use_eq = (uu___1947_72004.use_eq);
            is_iface = (uu___1947_72004.is_iface);
            admit = (uu___1947_72004.admit);
            lax = (uu___1947_72004.lax);
            lax_universes = (uu___1947_72004.lax_universes);
            phase1 = (uu___1947_72004.phase1);
            failhard = (uu___1947_72004.failhard);
            nosynth = (uu___1947_72004.nosynth);
            uvar_subtyping = (uu___1947_72004.uvar_subtyping);
            tc_term = (uu___1947_72004.tc_term);
            type_of = (uu___1947_72004.type_of);
            universe_of = (uu___1947_72004.universe_of);
            check_type_of = (uu___1947_72004.check_type_of);
            use_bv_sorts = (uu___1947_72004.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_72004.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_72004.normalized_eff_names);
            fv_delta_depths = (uu___1947_72004.fv_delta_depths);
            proof_ns = (uu___1947_72004.proof_ns);
            synth_hook = (uu___1947_72004.synth_hook);
            splice = (uu___1947_72004.splice);
            postprocess = (uu___1947_72004.postprocess);
            is_native_tactic = (uu___1947_72004.is_native_tactic);
            identifier_info = (uu___1947_72004.identifier_info);
            tc_hooks = (uu___1947_72004.tc_hooks);
            dsenv = (uu___1947_72004.dsenv);
            nbe = (uu___1947_72004.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____72034 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____72034  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____72192 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____72193 = l1 u t wp e  in
                                l2 u t uu____72192 uu____72193))
                | uu____72194 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____72266 = inst_tscheme_with lift_t [u]  in
            match uu____72266 with
            | (uu____72273,lift_t1) ->
                let uu____72275 =
                  let uu____72282 =
                    let uu____72283 =
                      let uu____72300 =
                        let uu____72311 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72320 =
                          let uu____72331 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____72331]  in
                        uu____72311 :: uu____72320  in
                      (lift_t1, uu____72300)  in
                    FStar_Syntax_Syntax.Tm_app uu____72283  in
                  FStar_Syntax_Syntax.mk uu____72282  in
                uu____72275 FStar_Pervasives_Native.None
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
            let uu____72441 = inst_tscheme_with lift_t [u]  in
            match uu____72441 with
            | (uu____72448,lift_t1) ->
                let uu____72450 =
                  let uu____72457 =
                    let uu____72458 =
                      let uu____72475 =
                        let uu____72486 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____72495 =
                          let uu____72506 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____72515 =
                            let uu____72526 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____72526]  in
                          uu____72506 :: uu____72515  in
                        uu____72486 :: uu____72495  in
                      (lift_t1, uu____72475)  in
                    FStar_Syntax_Syntax.Tm_app uu____72458  in
                  FStar_Syntax_Syntax.mk uu____72457  in
                uu____72450 FStar_Pervasives_Native.None
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
              let uu____72628 =
                let uu____72629 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____72629
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____72628  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____72638 =
              let uu____72640 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____72640  in
            let uu____72641 =
              let uu____72643 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____72671 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____72671)
                 in
              FStar_Util.dflt "none" uu____72643  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____72638
              uu____72641
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____72700  ->
                    match uu____72700 with
                    | (e,uu____72708) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____72731 =
            match uu____72731 with
            | (i,j) ->
                let uu____72742 = FStar_Ident.lid_equals i j  in
                if uu____72742
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _72749  -> FStar_Pervasives_Native.Some _72749)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____72778 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____72788 = FStar_Ident.lid_equals i k  in
                        if uu____72788
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____72802 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____72802
                                  then []
                                  else
                                    (let uu____72809 =
                                       let uu____72818 =
                                         find_edge order1 (i, k)  in
                                       let uu____72821 =
                                         find_edge order1 (k, j)  in
                                       (uu____72818, uu____72821)  in
                                     match uu____72809 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____72836 =
                                           compose_edges e1 e2  in
                                         [uu____72836]
                                     | uu____72837 -> [])))))
                 in
              FStar_List.append order1 uu____72778  in
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
                   let uu____72867 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____72870 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____72870
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____72867
                   then
                     let uu____72877 =
                       let uu____72883 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____72883)
                        in
                     let uu____72887 = get_range env  in
                     FStar_Errors.raise_error uu____72877 uu____72887
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____72965 = FStar_Ident.lid_equals i j
                                   in
                                if uu____72965
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____73017 =
                                              let uu____73026 =
                                                find_edge order2 (i, k)  in
                                              let uu____73029 =
                                                find_edge order2 (j, k)  in
                                              (uu____73026, uu____73029)  in
                                            match uu____73017 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____73071,uu____73072)
                                                     ->
                                                     let uu____73079 =
                                                       let uu____73086 =
                                                         let uu____73088 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73088
                                                          in
                                                       let uu____73091 =
                                                         let uu____73093 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73093
                                                          in
                                                       (uu____73086,
                                                         uu____73091)
                                                        in
                                                     (match uu____73079 with
                                                      | (true ,true ) ->
                                                          let uu____73110 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____73110
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
                                            | uu____73153 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_73226 = env.effects  in
              { decls = (uu___2074_73226.decls); order = order2; joins }  in
            let uu___2077_73227 = env  in
            {
              solver = (uu___2077_73227.solver);
              range = (uu___2077_73227.range);
              curmodule = (uu___2077_73227.curmodule);
              gamma = (uu___2077_73227.gamma);
              gamma_sig = (uu___2077_73227.gamma_sig);
              gamma_cache = (uu___2077_73227.gamma_cache);
              modules = (uu___2077_73227.modules);
              expected_typ = (uu___2077_73227.expected_typ);
              sigtab = (uu___2077_73227.sigtab);
              attrtab = (uu___2077_73227.attrtab);
              is_pattern = (uu___2077_73227.is_pattern);
              instantiate_imp = (uu___2077_73227.instantiate_imp);
              effects;
              generalize = (uu___2077_73227.generalize);
              letrecs = (uu___2077_73227.letrecs);
              top_level = (uu___2077_73227.top_level);
              check_uvars = (uu___2077_73227.check_uvars);
              use_eq = (uu___2077_73227.use_eq);
              is_iface = (uu___2077_73227.is_iface);
              admit = (uu___2077_73227.admit);
              lax = (uu___2077_73227.lax);
              lax_universes = (uu___2077_73227.lax_universes);
              phase1 = (uu___2077_73227.phase1);
              failhard = (uu___2077_73227.failhard);
              nosynth = (uu___2077_73227.nosynth);
              uvar_subtyping = (uu___2077_73227.uvar_subtyping);
              tc_term = (uu___2077_73227.tc_term);
              type_of = (uu___2077_73227.type_of);
              universe_of = (uu___2077_73227.universe_of);
              check_type_of = (uu___2077_73227.check_type_of);
              use_bv_sorts = (uu___2077_73227.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_73227.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_73227.normalized_eff_names);
              fv_delta_depths = (uu___2077_73227.fv_delta_depths);
              proof_ns = (uu___2077_73227.proof_ns);
              synth_hook = (uu___2077_73227.synth_hook);
              splice = (uu___2077_73227.splice);
              postprocess = (uu___2077_73227.postprocess);
              is_native_tactic = (uu___2077_73227.is_native_tactic);
              identifier_info = (uu___2077_73227.identifier_info);
              tc_hooks = (uu___2077_73227.tc_hooks);
              dsenv = (uu___2077_73227.dsenv);
              nbe = (uu___2077_73227.nbe)
            }))
      | uu____73228 -> env
  
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
        | uu____73257 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____73270 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____73270 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____73287 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____73287 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____73312 =
                     let uu____73318 =
                       let uu____73320 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____73328 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____73339 =
                         let uu____73341 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____73341  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____73320 uu____73328 uu____73339
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____73318)
                      in
                   FStar_Errors.raise_error uu____73312
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____73349 =
                     let uu____73360 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____73360 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____73397  ->
                        fun uu____73398  ->
                          match (uu____73397, uu____73398) with
                          | ((x,uu____73428),(t,uu____73430)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____73349
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____73461 =
                     let uu___2115_73462 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_73462.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_73462.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_73462.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_73462.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____73461
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____73474 .
    'Auu____73474 ->
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
          let uu____73504 = effect_decl_opt env effect_name  in
          match uu____73504 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____73543 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____73566 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____73605 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____73605
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____73610 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____73610
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____73625 =
                     let uu____73628 = get_range env  in
                     let uu____73629 =
                       let uu____73636 =
                         let uu____73637 =
                           let uu____73654 =
                             let uu____73665 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____73665; wp]  in
                           (repr, uu____73654)  in
                         FStar_Syntax_Syntax.Tm_app uu____73637  in
                       FStar_Syntax_Syntax.mk uu____73636  in
                     uu____73629 FStar_Pervasives_Native.None uu____73628  in
                   FStar_Pervasives_Native.Some uu____73625)
  
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
      | uu____73809 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____73824 =
        let uu____73825 = FStar_Syntax_Subst.compress t  in
        uu____73825.FStar_Syntax_Syntax.n  in
      match uu____73824 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____73829,c) ->
          is_reifiable_comp env c
      | uu____73851 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____73871 =
           let uu____73873 = is_reifiable_effect env l  in
           Prims.op_Negation uu____73873  in
         if uu____73871
         then
           let uu____73876 =
             let uu____73882 =
               let uu____73884 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____73884
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____73882)  in
           let uu____73888 = get_range env  in
           FStar_Errors.raise_error uu____73876 uu____73888
         else ());
        (let uu____73891 = effect_repr_aux true env c u_c  in
         match uu____73891 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_73927 = env  in
        {
          solver = (uu___2180_73927.solver);
          range = (uu___2180_73927.range);
          curmodule = (uu___2180_73927.curmodule);
          gamma = (uu___2180_73927.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_73927.gamma_cache);
          modules = (uu___2180_73927.modules);
          expected_typ = (uu___2180_73927.expected_typ);
          sigtab = (uu___2180_73927.sigtab);
          attrtab = (uu___2180_73927.attrtab);
          is_pattern = (uu___2180_73927.is_pattern);
          instantiate_imp = (uu___2180_73927.instantiate_imp);
          effects = (uu___2180_73927.effects);
          generalize = (uu___2180_73927.generalize);
          letrecs = (uu___2180_73927.letrecs);
          top_level = (uu___2180_73927.top_level);
          check_uvars = (uu___2180_73927.check_uvars);
          use_eq = (uu___2180_73927.use_eq);
          is_iface = (uu___2180_73927.is_iface);
          admit = (uu___2180_73927.admit);
          lax = (uu___2180_73927.lax);
          lax_universes = (uu___2180_73927.lax_universes);
          phase1 = (uu___2180_73927.phase1);
          failhard = (uu___2180_73927.failhard);
          nosynth = (uu___2180_73927.nosynth);
          uvar_subtyping = (uu___2180_73927.uvar_subtyping);
          tc_term = (uu___2180_73927.tc_term);
          type_of = (uu___2180_73927.type_of);
          universe_of = (uu___2180_73927.universe_of);
          check_type_of = (uu___2180_73927.check_type_of);
          use_bv_sorts = (uu___2180_73927.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_73927.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_73927.normalized_eff_names);
          fv_delta_depths = (uu___2180_73927.fv_delta_depths);
          proof_ns = (uu___2180_73927.proof_ns);
          synth_hook = (uu___2180_73927.synth_hook);
          splice = (uu___2180_73927.splice);
          postprocess = (uu___2180_73927.postprocess);
          is_native_tactic = (uu___2180_73927.is_native_tactic);
          identifier_info = (uu___2180_73927.identifier_info);
          tc_hooks = (uu___2180_73927.tc_hooks);
          dsenv = (uu___2180_73927.dsenv);
          nbe = (uu___2180_73927.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_73941 = env  in
      {
        solver = (uu___2187_73941.solver);
        range = (uu___2187_73941.range);
        curmodule = (uu___2187_73941.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_73941.gamma_sig);
        gamma_cache = (uu___2187_73941.gamma_cache);
        modules = (uu___2187_73941.modules);
        expected_typ = (uu___2187_73941.expected_typ);
        sigtab = (uu___2187_73941.sigtab);
        attrtab = (uu___2187_73941.attrtab);
        is_pattern = (uu___2187_73941.is_pattern);
        instantiate_imp = (uu___2187_73941.instantiate_imp);
        effects = (uu___2187_73941.effects);
        generalize = (uu___2187_73941.generalize);
        letrecs = (uu___2187_73941.letrecs);
        top_level = (uu___2187_73941.top_level);
        check_uvars = (uu___2187_73941.check_uvars);
        use_eq = (uu___2187_73941.use_eq);
        is_iface = (uu___2187_73941.is_iface);
        admit = (uu___2187_73941.admit);
        lax = (uu___2187_73941.lax);
        lax_universes = (uu___2187_73941.lax_universes);
        phase1 = (uu___2187_73941.phase1);
        failhard = (uu___2187_73941.failhard);
        nosynth = (uu___2187_73941.nosynth);
        uvar_subtyping = (uu___2187_73941.uvar_subtyping);
        tc_term = (uu___2187_73941.tc_term);
        type_of = (uu___2187_73941.type_of);
        universe_of = (uu___2187_73941.universe_of);
        check_type_of = (uu___2187_73941.check_type_of);
        use_bv_sorts = (uu___2187_73941.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_73941.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_73941.normalized_eff_names);
        fv_delta_depths = (uu___2187_73941.fv_delta_depths);
        proof_ns = (uu___2187_73941.proof_ns);
        synth_hook = (uu___2187_73941.synth_hook);
        splice = (uu___2187_73941.splice);
        postprocess = (uu___2187_73941.postprocess);
        is_native_tactic = (uu___2187_73941.is_native_tactic);
        identifier_info = (uu___2187_73941.identifier_info);
        tc_hooks = (uu___2187_73941.tc_hooks);
        dsenv = (uu___2187_73941.dsenv);
        nbe = (uu___2187_73941.nbe)
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
            (let uu___2200_73999 = env  in
             {
               solver = (uu___2200_73999.solver);
               range = (uu___2200_73999.range);
               curmodule = (uu___2200_73999.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_73999.gamma_sig);
               gamma_cache = (uu___2200_73999.gamma_cache);
               modules = (uu___2200_73999.modules);
               expected_typ = (uu___2200_73999.expected_typ);
               sigtab = (uu___2200_73999.sigtab);
               attrtab = (uu___2200_73999.attrtab);
               is_pattern = (uu___2200_73999.is_pattern);
               instantiate_imp = (uu___2200_73999.instantiate_imp);
               effects = (uu___2200_73999.effects);
               generalize = (uu___2200_73999.generalize);
               letrecs = (uu___2200_73999.letrecs);
               top_level = (uu___2200_73999.top_level);
               check_uvars = (uu___2200_73999.check_uvars);
               use_eq = (uu___2200_73999.use_eq);
               is_iface = (uu___2200_73999.is_iface);
               admit = (uu___2200_73999.admit);
               lax = (uu___2200_73999.lax);
               lax_universes = (uu___2200_73999.lax_universes);
               phase1 = (uu___2200_73999.phase1);
               failhard = (uu___2200_73999.failhard);
               nosynth = (uu___2200_73999.nosynth);
               uvar_subtyping = (uu___2200_73999.uvar_subtyping);
               tc_term = (uu___2200_73999.tc_term);
               type_of = (uu___2200_73999.type_of);
               universe_of = (uu___2200_73999.universe_of);
               check_type_of = (uu___2200_73999.check_type_of);
               use_bv_sorts = (uu___2200_73999.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_73999.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_73999.normalized_eff_names);
               fv_delta_depths = (uu___2200_73999.fv_delta_depths);
               proof_ns = (uu___2200_73999.proof_ns);
               synth_hook = (uu___2200_73999.synth_hook);
               splice = (uu___2200_73999.splice);
               postprocess = (uu___2200_73999.postprocess);
               is_native_tactic = (uu___2200_73999.is_native_tactic);
               identifier_info = (uu___2200_73999.identifier_info);
               tc_hooks = (uu___2200_73999.tc_hooks);
               dsenv = (uu___2200_73999.dsenv);
               nbe = (uu___2200_73999.nbe)
             }))
    | uu____74000 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____74029  ->
             match uu____74029 with | (x,uu____74037) -> push_bv env1 x) env
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
            let uu___2214_74072 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_74072.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_74072.FStar_Syntax_Syntax.index);
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
      (let uu___2225_74114 = env  in
       {
         solver = (uu___2225_74114.solver);
         range = (uu___2225_74114.range);
         curmodule = (uu___2225_74114.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_74114.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_74114.sigtab);
         attrtab = (uu___2225_74114.attrtab);
         is_pattern = (uu___2225_74114.is_pattern);
         instantiate_imp = (uu___2225_74114.instantiate_imp);
         effects = (uu___2225_74114.effects);
         generalize = (uu___2225_74114.generalize);
         letrecs = (uu___2225_74114.letrecs);
         top_level = (uu___2225_74114.top_level);
         check_uvars = (uu___2225_74114.check_uvars);
         use_eq = (uu___2225_74114.use_eq);
         is_iface = (uu___2225_74114.is_iface);
         admit = (uu___2225_74114.admit);
         lax = (uu___2225_74114.lax);
         lax_universes = (uu___2225_74114.lax_universes);
         phase1 = (uu___2225_74114.phase1);
         failhard = (uu___2225_74114.failhard);
         nosynth = (uu___2225_74114.nosynth);
         uvar_subtyping = (uu___2225_74114.uvar_subtyping);
         tc_term = (uu___2225_74114.tc_term);
         type_of = (uu___2225_74114.type_of);
         universe_of = (uu___2225_74114.universe_of);
         check_type_of = (uu___2225_74114.check_type_of);
         use_bv_sorts = (uu___2225_74114.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_74114.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_74114.normalized_eff_names);
         fv_delta_depths = (uu___2225_74114.fv_delta_depths);
         proof_ns = (uu___2225_74114.proof_ns);
         synth_hook = (uu___2225_74114.synth_hook);
         splice = (uu___2225_74114.splice);
         postprocess = (uu___2225_74114.postprocess);
         is_native_tactic = (uu___2225_74114.is_native_tactic);
         identifier_info = (uu___2225_74114.identifier_info);
         tc_hooks = (uu___2225_74114.tc_hooks);
         dsenv = (uu___2225_74114.dsenv);
         nbe = (uu___2225_74114.nbe)
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
        let uu____74158 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____74158 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____74186 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____74186)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_74202 = env  in
      {
        solver = (uu___2240_74202.solver);
        range = (uu___2240_74202.range);
        curmodule = (uu___2240_74202.curmodule);
        gamma = (uu___2240_74202.gamma);
        gamma_sig = (uu___2240_74202.gamma_sig);
        gamma_cache = (uu___2240_74202.gamma_cache);
        modules = (uu___2240_74202.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_74202.sigtab);
        attrtab = (uu___2240_74202.attrtab);
        is_pattern = (uu___2240_74202.is_pattern);
        instantiate_imp = (uu___2240_74202.instantiate_imp);
        effects = (uu___2240_74202.effects);
        generalize = (uu___2240_74202.generalize);
        letrecs = (uu___2240_74202.letrecs);
        top_level = (uu___2240_74202.top_level);
        check_uvars = (uu___2240_74202.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_74202.is_iface);
        admit = (uu___2240_74202.admit);
        lax = (uu___2240_74202.lax);
        lax_universes = (uu___2240_74202.lax_universes);
        phase1 = (uu___2240_74202.phase1);
        failhard = (uu___2240_74202.failhard);
        nosynth = (uu___2240_74202.nosynth);
        uvar_subtyping = (uu___2240_74202.uvar_subtyping);
        tc_term = (uu___2240_74202.tc_term);
        type_of = (uu___2240_74202.type_of);
        universe_of = (uu___2240_74202.universe_of);
        check_type_of = (uu___2240_74202.check_type_of);
        use_bv_sorts = (uu___2240_74202.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_74202.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_74202.normalized_eff_names);
        fv_delta_depths = (uu___2240_74202.fv_delta_depths);
        proof_ns = (uu___2240_74202.proof_ns);
        synth_hook = (uu___2240_74202.synth_hook);
        splice = (uu___2240_74202.splice);
        postprocess = (uu___2240_74202.postprocess);
        is_native_tactic = (uu___2240_74202.is_native_tactic);
        identifier_info = (uu___2240_74202.identifier_info);
        tc_hooks = (uu___2240_74202.tc_hooks);
        dsenv = (uu___2240_74202.dsenv);
        nbe = (uu___2240_74202.nbe)
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
    let uu____74233 = expected_typ env_  in
    ((let uu___2247_74239 = env_  in
      {
        solver = (uu___2247_74239.solver);
        range = (uu___2247_74239.range);
        curmodule = (uu___2247_74239.curmodule);
        gamma = (uu___2247_74239.gamma);
        gamma_sig = (uu___2247_74239.gamma_sig);
        gamma_cache = (uu___2247_74239.gamma_cache);
        modules = (uu___2247_74239.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_74239.sigtab);
        attrtab = (uu___2247_74239.attrtab);
        is_pattern = (uu___2247_74239.is_pattern);
        instantiate_imp = (uu___2247_74239.instantiate_imp);
        effects = (uu___2247_74239.effects);
        generalize = (uu___2247_74239.generalize);
        letrecs = (uu___2247_74239.letrecs);
        top_level = (uu___2247_74239.top_level);
        check_uvars = (uu___2247_74239.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_74239.is_iface);
        admit = (uu___2247_74239.admit);
        lax = (uu___2247_74239.lax);
        lax_universes = (uu___2247_74239.lax_universes);
        phase1 = (uu___2247_74239.phase1);
        failhard = (uu___2247_74239.failhard);
        nosynth = (uu___2247_74239.nosynth);
        uvar_subtyping = (uu___2247_74239.uvar_subtyping);
        tc_term = (uu___2247_74239.tc_term);
        type_of = (uu___2247_74239.type_of);
        universe_of = (uu___2247_74239.universe_of);
        check_type_of = (uu___2247_74239.check_type_of);
        use_bv_sorts = (uu___2247_74239.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_74239.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_74239.normalized_eff_names);
        fv_delta_depths = (uu___2247_74239.fv_delta_depths);
        proof_ns = (uu___2247_74239.proof_ns);
        synth_hook = (uu___2247_74239.synth_hook);
        splice = (uu___2247_74239.splice);
        postprocess = (uu___2247_74239.postprocess);
        is_native_tactic = (uu___2247_74239.is_native_tactic);
        identifier_info = (uu___2247_74239.identifier_info);
        tc_hooks = (uu___2247_74239.tc_hooks);
        dsenv = (uu___2247_74239.dsenv);
        nbe = (uu___2247_74239.nbe)
      }), uu____74233)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____74251 =
      let uu____74254 = FStar_Ident.id_of_text ""  in [uu____74254]  in
    FStar_Ident.lid_of_ids uu____74251  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____74261 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____74261
        then
          let uu____74266 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____74266 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_74294 = env  in
       {
         solver = (uu___2255_74294.solver);
         range = (uu___2255_74294.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_74294.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_74294.expected_typ);
         sigtab = (uu___2255_74294.sigtab);
         attrtab = (uu___2255_74294.attrtab);
         is_pattern = (uu___2255_74294.is_pattern);
         instantiate_imp = (uu___2255_74294.instantiate_imp);
         effects = (uu___2255_74294.effects);
         generalize = (uu___2255_74294.generalize);
         letrecs = (uu___2255_74294.letrecs);
         top_level = (uu___2255_74294.top_level);
         check_uvars = (uu___2255_74294.check_uvars);
         use_eq = (uu___2255_74294.use_eq);
         is_iface = (uu___2255_74294.is_iface);
         admit = (uu___2255_74294.admit);
         lax = (uu___2255_74294.lax);
         lax_universes = (uu___2255_74294.lax_universes);
         phase1 = (uu___2255_74294.phase1);
         failhard = (uu___2255_74294.failhard);
         nosynth = (uu___2255_74294.nosynth);
         uvar_subtyping = (uu___2255_74294.uvar_subtyping);
         tc_term = (uu___2255_74294.tc_term);
         type_of = (uu___2255_74294.type_of);
         universe_of = (uu___2255_74294.universe_of);
         check_type_of = (uu___2255_74294.check_type_of);
         use_bv_sorts = (uu___2255_74294.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_74294.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_74294.normalized_eff_names);
         fv_delta_depths = (uu___2255_74294.fv_delta_depths);
         proof_ns = (uu___2255_74294.proof_ns);
         synth_hook = (uu___2255_74294.synth_hook);
         splice = (uu___2255_74294.splice);
         postprocess = (uu___2255_74294.postprocess);
         is_native_tactic = (uu___2255_74294.is_native_tactic);
         identifier_info = (uu___2255_74294.identifier_info);
         tc_hooks = (uu___2255_74294.tc_hooks);
         dsenv = (uu___2255_74294.dsenv);
         nbe = (uu___2255_74294.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74346)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74350,(uu____74351,t)))::tl1
          ->
          let uu____74372 =
            let uu____74375 = FStar_Syntax_Free.uvars t  in
            ext out uu____74375  in
          aux uu____74372 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74378;
            FStar_Syntax_Syntax.index = uu____74379;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74387 =
            let uu____74390 = FStar_Syntax_Free.uvars t  in
            ext out uu____74390  in
          aux uu____74387 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____74448)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74452,(uu____74453,t)))::tl1
          ->
          let uu____74474 =
            let uu____74477 = FStar_Syntax_Free.univs t  in
            ext out uu____74477  in
          aux uu____74474 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74480;
            FStar_Syntax_Syntax.index = uu____74481;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74489 =
            let uu____74492 = FStar_Syntax_Free.univs t  in
            ext out uu____74492  in
          aux uu____74489 tl1
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
          let uu____74554 = FStar_Util.set_add uname out  in
          aux uu____74554 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____74557,(uu____74558,t)))::tl1
          ->
          let uu____74579 =
            let uu____74582 = FStar_Syntax_Free.univnames t  in
            ext out uu____74582  in
          aux uu____74579 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____74585;
            FStar_Syntax_Syntax.index = uu____74586;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____74594 =
            let uu____74597 = FStar_Syntax_Free.univnames t  in
            ext out uu____74597  in
          aux uu____74594 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_74618  ->
            match uu___457_74618 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____74622 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____74635 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____74646 =
      let uu____74655 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____74655
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____74646 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____74703 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_74716  ->
              match uu___458_74716 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____74719 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____74719
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____74725) ->
                  let uu____74742 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____74742))
       in
    FStar_All.pipe_right uu____74703 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_74756  ->
    match uu___459_74756 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____74762 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____74762
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____74785  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____74840) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____74873,uu____74874) -> false  in
      let uu____74888 =
        FStar_List.tryFind
          (fun uu____74910  ->
             match uu____74910 with | (p,uu____74921) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____74888 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____74940,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____74970 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____74970
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_74992 = e  in
        {
          solver = (uu___2398_74992.solver);
          range = (uu___2398_74992.range);
          curmodule = (uu___2398_74992.curmodule);
          gamma = (uu___2398_74992.gamma);
          gamma_sig = (uu___2398_74992.gamma_sig);
          gamma_cache = (uu___2398_74992.gamma_cache);
          modules = (uu___2398_74992.modules);
          expected_typ = (uu___2398_74992.expected_typ);
          sigtab = (uu___2398_74992.sigtab);
          attrtab = (uu___2398_74992.attrtab);
          is_pattern = (uu___2398_74992.is_pattern);
          instantiate_imp = (uu___2398_74992.instantiate_imp);
          effects = (uu___2398_74992.effects);
          generalize = (uu___2398_74992.generalize);
          letrecs = (uu___2398_74992.letrecs);
          top_level = (uu___2398_74992.top_level);
          check_uvars = (uu___2398_74992.check_uvars);
          use_eq = (uu___2398_74992.use_eq);
          is_iface = (uu___2398_74992.is_iface);
          admit = (uu___2398_74992.admit);
          lax = (uu___2398_74992.lax);
          lax_universes = (uu___2398_74992.lax_universes);
          phase1 = (uu___2398_74992.phase1);
          failhard = (uu___2398_74992.failhard);
          nosynth = (uu___2398_74992.nosynth);
          uvar_subtyping = (uu___2398_74992.uvar_subtyping);
          tc_term = (uu___2398_74992.tc_term);
          type_of = (uu___2398_74992.type_of);
          universe_of = (uu___2398_74992.universe_of);
          check_type_of = (uu___2398_74992.check_type_of);
          use_bv_sorts = (uu___2398_74992.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_74992.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_74992.normalized_eff_names);
          fv_delta_depths = (uu___2398_74992.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_74992.synth_hook);
          splice = (uu___2398_74992.splice);
          postprocess = (uu___2398_74992.postprocess);
          is_native_tactic = (uu___2398_74992.is_native_tactic);
          identifier_info = (uu___2398_74992.identifier_info);
          tc_hooks = (uu___2398_74992.tc_hooks);
          dsenv = (uu___2398_74992.dsenv);
          nbe = (uu___2398_74992.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_75040 = e  in
      {
        solver = (uu___2407_75040.solver);
        range = (uu___2407_75040.range);
        curmodule = (uu___2407_75040.curmodule);
        gamma = (uu___2407_75040.gamma);
        gamma_sig = (uu___2407_75040.gamma_sig);
        gamma_cache = (uu___2407_75040.gamma_cache);
        modules = (uu___2407_75040.modules);
        expected_typ = (uu___2407_75040.expected_typ);
        sigtab = (uu___2407_75040.sigtab);
        attrtab = (uu___2407_75040.attrtab);
        is_pattern = (uu___2407_75040.is_pattern);
        instantiate_imp = (uu___2407_75040.instantiate_imp);
        effects = (uu___2407_75040.effects);
        generalize = (uu___2407_75040.generalize);
        letrecs = (uu___2407_75040.letrecs);
        top_level = (uu___2407_75040.top_level);
        check_uvars = (uu___2407_75040.check_uvars);
        use_eq = (uu___2407_75040.use_eq);
        is_iface = (uu___2407_75040.is_iface);
        admit = (uu___2407_75040.admit);
        lax = (uu___2407_75040.lax);
        lax_universes = (uu___2407_75040.lax_universes);
        phase1 = (uu___2407_75040.phase1);
        failhard = (uu___2407_75040.failhard);
        nosynth = (uu___2407_75040.nosynth);
        uvar_subtyping = (uu___2407_75040.uvar_subtyping);
        tc_term = (uu___2407_75040.tc_term);
        type_of = (uu___2407_75040.type_of);
        universe_of = (uu___2407_75040.universe_of);
        check_type_of = (uu___2407_75040.check_type_of);
        use_bv_sorts = (uu___2407_75040.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_75040.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_75040.normalized_eff_names);
        fv_delta_depths = (uu___2407_75040.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_75040.synth_hook);
        splice = (uu___2407_75040.splice);
        postprocess = (uu___2407_75040.postprocess);
        is_native_tactic = (uu___2407_75040.is_native_tactic);
        identifier_info = (uu___2407_75040.identifier_info);
        tc_hooks = (uu___2407_75040.tc_hooks);
        dsenv = (uu___2407_75040.dsenv);
        nbe = (uu___2407_75040.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____75056 = FStar_Syntax_Free.names t  in
      let uu____75059 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____75056 uu____75059
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____75082 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____75082
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____75092 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____75092
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____75113 =
      match uu____75113 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____75133 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____75133)
       in
    let uu____75141 =
      let uu____75145 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____75145 FStar_List.rev  in
    FStar_All.pipe_right uu____75141 (FStar_String.concat " ")
  
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
                  (let uu____75215 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____75215 with
                   | FStar_Pervasives_Native.Some uu____75219 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____75222 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____75232;
        univ_ineqs = uu____75233; implicits = uu____75234;_} -> true
    | uu____75246 -> false
  
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
          let uu___2451_75277 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_75277.deferred);
            univ_ineqs = (uu___2451_75277.univ_ineqs);
            implicits = (uu___2451_75277.implicits)
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
          let uu____75316 = FStar_Options.defensive ()  in
          if uu____75316
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____75322 =
              let uu____75324 =
                let uu____75326 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____75326  in
              Prims.op_Negation uu____75324  in
            (if uu____75322
             then
               let uu____75333 =
                 let uu____75339 =
                   let uu____75341 = FStar_Syntax_Print.term_to_string t  in
                   let uu____75343 =
                     let uu____75345 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____75345
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____75341 uu____75343
                    in
                 (FStar_Errors.Warning_Defensive, uu____75339)  in
               FStar_Errors.log_issue rng uu____75333
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
          let uu____75385 =
            let uu____75387 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75387  in
          if uu____75385
          then ()
          else
            (let uu____75392 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____75392 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____75418 =
            let uu____75420 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____75420  in
          if uu____75418
          then ()
          else
            (let uu____75425 = bound_vars e  in
             def_check_closed_in rng msg uu____75425 t)
  
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
          let uu___2488_75464 = g  in
          let uu____75465 =
            let uu____75466 =
              let uu____75467 =
                let uu____75474 =
                  let uu____75475 =
                    let uu____75492 =
                      let uu____75503 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____75503]  in
                    (f, uu____75492)  in
                  FStar_Syntax_Syntax.Tm_app uu____75475  in
                FStar_Syntax_Syntax.mk uu____75474  in
              uu____75467 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _75540  -> FStar_TypeChecker_Common.NonTrivial _75540)
              uu____75466
             in
          {
            guard_f = uu____75465;
            deferred = (uu___2488_75464.deferred);
            univ_ineqs = (uu___2488_75464.univ_ineqs);
            implicits = (uu___2488_75464.implicits)
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
          let uu___2495_75558 = g  in
          let uu____75559 =
            let uu____75560 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75560  in
          {
            guard_f = uu____75559;
            deferred = (uu___2495_75558.deferred);
            univ_ineqs = (uu___2495_75558.univ_ineqs);
            implicits = (uu___2495_75558.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_75577 = g  in
          let uu____75578 =
            let uu____75579 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____75579  in
          {
            guard_f = uu____75578;
            deferred = (uu___2500_75577.deferred);
            univ_ineqs = (uu___2500_75577.univ_ineqs);
            implicits = (uu___2500_75577.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_75581 = g  in
          let uu____75582 =
            let uu____75583 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____75583  in
          {
            guard_f = uu____75582;
            deferred = (uu___2504_75581.deferred);
            univ_ineqs = (uu___2504_75581.univ_ineqs);
            implicits = (uu___2504_75581.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____75590 ->
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
          let uu____75607 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____75607
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____75614 =
      let uu____75615 = FStar_Syntax_Util.unmeta t  in
      uu____75615.FStar_Syntax_Syntax.n  in
    match uu____75614 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____75619 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____75662 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____75662;
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
                       let uu____75757 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____75757
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_75764 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_75764.deferred);
              univ_ineqs = (uu___2559_75764.univ_ineqs);
              implicits = (uu___2559_75764.implicits)
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
               let uu____75798 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____75798
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
            let uu___2574_75825 = g  in
            let uu____75826 =
              let uu____75827 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____75827  in
            {
              guard_f = uu____75826;
              deferred = (uu___2574_75825.deferred);
              univ_ineqs = (uu___2574_75825.univ_ineqs);
              implicits = (uu___2574_75825.implicits)
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
              let uu____75885 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____75885 with
              | FStar_Pervasives_Native.Some
                  (uu____75910::(tm,uu____75912)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____75976 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____75994 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____75994;
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
                      let uu___2596_76026 = trivial_guard  in
                      {
                        guard_f = (uu___2596_76026.guard_f);
                        deferred = (uu___2596_76026.deferred);
                        univ_ineqs = (uu___2596_76026.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____76044  -> ());
    push = (fun uu____76046  -> ());
    pop = (fun uu____76049  -> ());
    snapshot =
      (fun uu____76052  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____76071  -> fun uu____76072  -> ());
    encode_sig = (fun uu____76087  -> fun uu____76088  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____76094 =
             let uu____76101 = FStar_Options.peek ()  in (e, g, uu____76101)
              in
           [uu____76094]);
    solve = (fun uu____76117  -> fun uu____76118  -> fun uu____76119  -> ());
    finish = (fun uu____76126  -> ());
    refresh = (fun uu____76128  -> ())
  } 