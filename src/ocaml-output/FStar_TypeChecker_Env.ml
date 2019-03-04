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
    match projectee with | Beta  -> true | uu____56088 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56099 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56110 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56122 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56141 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56152 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56163 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____56174 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____56185 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____56196 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____56208 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56230 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56258 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56286 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____56311 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____56322 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____56333 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____56344 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____56355 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56366 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____56377 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____56388 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____56399 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____56410 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____56421 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56432 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____56443 -> false
  
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
      | uu____56503 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____56529 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____56540 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____56551 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____56563 -> false
  
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
           (fun uu___446_67825  ->
              match uu___446_67825 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____67828 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____67828  in
                  let uu____67829 =
                    let uu____67830 = FStar_Syntax_Subst.compress y  in
                    uu____67830.FStar_Syntax_Syntax.n  in
                  (match uu____67829 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____67834 =
                         let uu___775_67835 = y1  in
                         let uu____67836 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_67835.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_67835.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____67836
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____67834
                   | uu____67839 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_67853 = env  in
      let uu____67854 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_67853.solver);
        range = (uu___781_67853.range);
        curmodule = (uu___781_67853.curmodule);
        gamma = uu____67854;
        gamma_sig = (uu___781_67853.gamma_sig);
        gamma_cache = (uu___781_67853.gamma_cache);
        modules = (uu___781_67853.modules);
        expected_typ = (uu___781_67853.expected_typ);
        sigtab = (uu___781_67853.sigtab);
        attrtab = (uu___781_67853.attrtab);
        is_pattern = (uu___781_67853.is_pattern);
        instantiate_imp = (uu___781_67853.instantiate_imp);
        effects = (uu___781_67853.effects);
        generalize = (uu___781_67853.generalize);
        letrecs = (uu___781_67853.letrecs);
        top_level = (uu___781_67853.top_level);
        check_uvars = (uu___781_67853.check_uvars);
        use_eq = (uu___781_67853.use_eq);
        is_iface = (uu___781_67853.is_iface);
        admit = (uu___781_67853.admit);
        lax = (uu___781_67853.lax);
        lax_universes = (uu___781_67853.lax_universes);
        phase1 = (uu___781_67853.phase1);
        failhard = (uu___781_67853.failhard);
        nosynth = (uu___781_67853.nosynth);
        uvar_subtyping = (uu___781_67853.uvar_subtyping);
        tc_term = (uu___781_67853.tc_term);
        type_of = (uu___781_67853.type_of);
        universe_of = (uu___781_67853.universe_of);
        check_type_of = (uu___781_67853.check_type_of);
        use_bv_sorts = (uu___781_67853.use_bv_sorts);
        qtbl_name_and_index = (uu___781_67853.qtbl_name_and_index);
        normalized_eff_names = (uu___781_67853.normalized_eff_names);
        fv_delta_depths = (uu___781_67853.fv_delta_depths);
        proof_ns = (uu___781_67853.proof_ns);
        synth_hook = (uu___781_67853.synth_hook);
        splice = (uu___781_67853.splice);
        postprocess = (uu___781_67853.postprocess);
        is_native_tactic = (uu___781_67853.is_native_tactic);
        identifier_info = (uu___781_67853.identifier_info);
        tc_hooks = (uu___781_67853.tc_hooks);
        dsenv = (uu___781_67853.dsenv);
        nbe = (uu___781_67853.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____67862  -> fun uu____67863  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_67885 = env  in
      {
        solver = (uu___788_67885.solver);
        range = (uu___788_67885.range);
        curmodule = (uu___788_67885.curmodule);
        gamma = (uu___788_67885.gamma);
        gamma_sig = (uu___788_67885.gamma_sig);
        gamma_cache = (uu___788_67885.gamma_cache);
        modules = (uu___788_67885.modules);
        expected_typ = (uu___788_67885.expected_typ);
        sigtab = (uu___788_67885.sigtab);
        attrtab = (uu___788_67885.attrtab);
        is_pattern = (uu___788_67885.is_pattern);
        instantiate_imp = (uu___788_67885.instantiate_imp);
        effects = (uu___788_67885.effects);
        generalize = (uu___788_67885.generalize);
        letrecs = (uu___788_67885.letrecs);
        top_level = (uu___788_67885.top_level);
        check_uvars = (uu___788_67885.check_uvars);
        use_eq = (uu___788_67885.use_eq);
        is_iface = (uu___788_67885.is_iface);
        admit = (uu___788_67885.admit);
        lax = (uu___788_67885.lax);
        lax_universes = (uu___788_67885.lax_universes);
        phase1 = (uu___788_67885.phase1);
        failhard = (uu___788_67885.failhard);
        nosynth = (uu___788_67885.nosynth);
        uvar_subtyping = (uu___788_67885.uvar_subtyping);
        tc_term = (uu___788_67885.tc_term);
        type_of = (uu___788_67885.type_of);
        universe_of = (uu___788_67885.universe_of);
        check_type_of = (uu___788_67885.check_type_of);
        use_bv_sorts = (uu___788_67885.use_bv_sorts);
        qtbl_name_and_index = (uu___788_67885.qtbl_name_and_index);
        normalized_eff_names = (uu___788_67885.normalized_eff_names);
        fv_delta_depths = (uu___788_67885.fv_delta_depths);
        proof_ns = (uu___788_67885.proof_ns);
        synth_hook = (uu___788_67885.synth_hook);
        splice = (uu___788_67885.splice);
        postprocess = (uu___788_67885.postprocess);
        is_native_tactic = (uu___788_67885.is_native_tactic);
        identifier_info = (uu___788_67885.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_67885.dsenv);
        nbe = (uu___788_67885.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_67897 = e  in
      let uu____67898 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_67897.solver);
        range = (uu___792_67897.range);
        curmodule = (uu___792_67897.curmodule);
        gamma = (uu___792_67897.gamma);
        gamma_sig = (uu___792_67897.gamma_sig);
        gamma_cache = (uu___792_67897.gamma_cache);
        modules = (uu___792_67897.modules);
        expected_typ = (uu___792_67897.expected_typ);
        sigtab = (uu___792_67897.sigtab);
        attrtab = (uu___792_67897.attrtab);
        is_pattern = (uu___792_67897.is_pattern);
        instantiate_imp = (uu___792_67897.instantiate_imp);
        effects = (uu___792_67897.effects);
        generalize = (uu___792_67897.generalize);
        letrecs = (uu___792_67897.letrecs);
        top_level = (uu___792_67897.top_level);
        check_uvars = (uu___792_67897.check_uvars);
        use_eq = (uu___792_67897.use_eq);
        is_iface = (uu___792_67897.is_iface);
        admit = (uu___792_67897.admit);
        lax = (uu___792_67897.lax);
        lax_universes = (uu___792_67897.lax_universes);
        phase1 = (uu___792_67897.phase1);
        failhard = (uu___792_67897.failhard);
        nosynth = (uu___792_67897.nosynth);
        uvar_subtyping = (uu___792_67897.uvar_subtyping);
        tc_term = (uu___792_67897.tc_term);
        type_of = (uu___792_67897.type_of);
        universe_of = (uu___792_67897.universe_of);
        check_type_of = (uu___792_67897.check_type_of);
        use_bv_sorts = (uu___792_67897.use_bv_sorts);
        qtbl_name_and_index = (uu___792_67897.qtbl_name_and_index);
        normalized_eff_names = (uu___792_67897.normalized_eff_names);
        fv_delta_depths = (uu___792_67897.fv_delta_depths);
        proof_ns = (uu___792_67897.proof_ns);
        synth_hook = (uu___792_67897.synth_hook);
        splice = (uu___792_67897.splice);
        postprocess = (uu___792_67897.postprocess);
        is_native_tactic = (uu___792_67897.is_native_tactic);
        identifier_info = (uu___792_67897.identifier_info);
        tc_hooks = (uu___792_67897.tc_hooks);
        dsenv = uu____67898;
        nbe = (uu___792_67897.nbe)
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
      | (NoDelta ,uu____67927) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____67930,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____67932,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____67935 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____67949 . unit -> 'Auu____67949 FStar_Util.smap =
  fun uu____67956  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____67962 . unit -> 'Auu____67962 FStar_Util.smap =
  fun uu____67969  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____68107 = new_gamma_cache ()  in
                  let uu____68110 = new_sigtab ()  in
                  let uu____68113 = new_sigtab ()  in
                  let uu____68120 =
                    let uu____68135 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____68135, FStar_Pervasives_Native.None)  in
                  let uu____68156 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____68160 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____68164 = FStar_Options.using_facts_from ()  in
                  let uu____68165 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____68168 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____68107;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____68110;
                    attrtab = uu____68113;
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
                    qtbl_name_and_index = uu____68120;
                    normalized_eff_names = uu____68156;
                    fv_delta_depths = uu____68160;
                    proof_ns = uu____68164;
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
                    is_native_tactic = (fun uu____68230  -> false);
                    identifier_info = uu____68165;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____68168;
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
  fun uu____68342  ->
    let uu____68343 = FStar_ST.op_Bang query_indices  in
    match uu____68343 with
    | [] -> failwith "Empty query indices!"
    | uu____68398 ->
        let uu____68408 =
          let uu____68418 =
            let uu____68426 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____68426  in
          let uu____68480 = FStar_ST.op_Bang query_indices  in uu____68418 ::
            uu____68480
           in
        FStar_ST.op_Colon_Equals query_indices uu____68408
  
let (pop_query_indices : unit -> unit) =
  fun uu____68576  ->
    let uu____68577 = FStar_ST.op_Bang query_indices  in
    match uu____68577 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____68704  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____68741  ->
    match uu____68741 with
    | (l,n1) ->
        let uu____68751 = FStar_ST.op_Bang query_indices  in
        (match uu____68751 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____68873 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____68896  ->
    let uu____68897 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____68897
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____68976 =
       let uu____68979 = FStar_ST.op_Bang stack  in env :: uu____68979  in
     FStar_ST.op_Colon_Equals stack uu____68976);
    (let uu___860_69028 = env  in
     let uu____69029 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____69032 = FStar_Util.smap_copy (sigtab env)  in
     let uu____69035 = FStar_Util.smap_copy (attrtab env)  in
     let uu____69042 =
       let uu____69057 =
         let uu____69061 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____69061  in
       let uu____69093 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____69057, uu____69093)  in
     let uu____69142 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____69145 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____69148 =
       let uu____69151 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____69151  in
     {
       solver = (uu___860_69028.solver);
       range = (uu___860_69028.range);
       curmodule = (uu___860_69028.curmodule);
       gamma = (uu___860_69028.gamma);
       gamma_sig = (uu___860_69028.gamma_sig);
       gamma_cache = uu____69029;
       modules = (uu___860_69028.modules);
       expected_typ = (uu___860_69028.expected_typ);
       sigtab = uu____69032;
       attrtab = uu____69035;
       is_pattern = (uu___860_69028.is_pattern);
       instantiate_imp = (uu___860_69028.instantiate_imp);
       effects = (uu___860_69028.effects);
       generalize = (uu___860_69028.generalize);
       letrecs = (uu___860_69028.letrecs);
       top_level = (uu___860_69028.top_level);
       check_uvars = (uu___860_69028.check_uvars);
       use_eq = (uu___860_69028.use_eq);
       is_iface = (uu___860_69028.is_iface);
       admit = (uu___860_69028.admit);
       lax = (uu___860_69028.lax);
       lax_universes = (uu___860_69028.lax_universes);
       phase1 = (uu___860_69028.phase1);
       failhard = (uu___860_69028.failhard);
       nosynth = (uu___860_69028.nosynth);
       uvar_subtyping = (uu___860_69028.uvar_subtyping);
       tc_term = (uu___860_69028.tc_term);
       type_of = (uu___860_69028.type_of);
       universe_of = (uu___860_69028.universe_of);
       check_type_of = (uu___860_69028.check_type_of);
       use_bv_sorts = (uu___860_69028.use_bv_sorts);
       qtbl_name_and_index = uu____69042;
       normalized_eff_names = uu____69142;
       fv_delta_depths = uu____69145;
       proof_ns = (uu___860_69028.proof_ns);
       synth_hook = (uu___860_69028.synth_hook);
       splice = (uu___860_69028.splice);
       postprocess = (uu___860_69028.postprocess);
       is_native_tactic = (uu___860_69028.is_native_tactic);
       identifier_info = uu____69148;
       tc_hooks = (uu___860_69028.tc_hooks);
       dsenv = (uu___860_69028.dsenv);
       nbe = (uu___860_69028.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____69198  ->
    let uu____69199 = FStar_ST.op_Bang stack  in
    match uu____69199 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____69253 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____69343  ->
           let uu____69344 = snapshot_stack env  in
           match uu____69344 with
           | (stack_depth,env1) ->
               let uu____69378 = snapshot_query_indices ()  in
               (match uu____69378 with
                | (query_indices_depth,()) ->
                    let uu____69411 = (env1.solver).snapshot msg  in
                    (match uu____69411 with
                     | (solver_depth,()) ->
                         let uu____69468 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____69468 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_69535 = env1  in
                                 {
                                   solver = (uu___885_69535.solver);
                                   range = (uu___885_69535.range);
                                   curmodule = (uu___885_69535.curmodule);
                                   gamma = (uu___885_69535.gamma);
                                   gamma_sig = (uu___885_69535.gamma_sig);
                                   gamma_cache = (uu___885_69535.gamma_cache);
                                   modules = (uu___885_69535.modules);
                                   expected_typ =
                                     (uu___885_69535.expected_typ);
                                   sigtab = (uu___885_69535.sigtab);
                                   attrtab = (uu___885_69535.attrtab);
                                   is_pattern = (uu___885_69535.is_pattern);
                                   instantiate_imp =
                                     (uu___885_69535.instantiate_imp);
                                   effects = (uu___885_69535.effects);
                                   generalize = (uu___885_69535.generalize);
                                   letrecs = (uu___885_69535.letrecs);
                                   top_level = (uu___885_69535.top_level);
                                   check_uvars = (uu___885_69535.check_uvars);
                                   use_eq = (uu___885_69535.use_eq);
                                   is_iface = (uu___885_69535.is_iface);
                                   admit = (uu___885_69535.admit);
                                   lax = (uu___885_69535.lax);
                                   lax_universes =
                                     (uu___885_69535.lax_universes);
                                   phase1 = (uu___885_69535.phase1);
                                   failhard = (uu___885_69535.failhard);
                                   nosynth = (uu___885_69535.nosynth);
                                   uvar_subtyping =
                                     (uu___885_69535.uvar_subtyping);
                                   tc_term = (uu___885_69535.tc_term);
                                   type_of = (uu___885_69535.type_of);
                                   universe_of = (uu___885_69535.universe_of);
                                   check_type_of =
                                     (uu___885_69535.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_69535.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_69535.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_69535.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_69535.fv_delta_depths);
                                   proof_ns = (uu___885_69535.proof_ns);
                                   synth_hook = (uu___885_69535.synth_hook);
                                   splice = (uu___885_69535.splice);
                                   postprocess = (uu___885_69535.postprocess);
                                   is_native_tactic =
                                     (uu___885_69535.is_native_tactic);
                                   identifier_info =
                                     (uu___885_69535.identifier_info);
                                   tc_hooks = (uu___885_69535.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_69535.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____69569  ->
             let uu____69570 =
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
             match uu____69570 with
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
                             ((let uu____69750 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____69750
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____69766 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____69766
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____69798,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____69840 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____69870  ->
                  match uu____69870 with
                  | (m,uu____69878) -> FStar_Ident.lid_equals l m))
           in
        (match uu____69840 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_69893 = env  in
               {
                 solver = (uu___930_69893.solver);
                 range = (uu___930_69893.range);
                 curmodule = (uu___930_69893.curmodule);
                 gamma = (uu___930_69893.gamma);
                 gamma_sig = (uu___930_69893.gamma_sig);
                 gamma_cache = (uu___930_69893.gamma_cache);
                 modules = (uu___930_69893.modules);
                 expected_typ = (uu___930_69893.expected_typ);
                 sigtab = (uu___930_69893.sigtab);
                 attrtab = (uu___930_69893.attrtab);
                 is_pattern = (uu___930_69893.is_pattern);
                 instantiate_imp = (uu___930_69893.instantiate_imp);
                 effects = (uu___930_69893.effects);
                 generalize = (uu___930_69893.generalize);
                 letrecs = (uu___930_69893.letrecs);
                 top_level = (uu___930_69893.top_level);
                 check_uvars = (uu___930_69893.check_uvars);
                 use_eq = (uu___930_69893.use_eq);
                 is_iface = (uu___930_69893.is_iface);
                 admit = (uu___930_69893.admit);
                 lax = (uu___930_69893.lax);
                 lax_universes = (uu___930_69893.lax_universes);
                 phase1 = (uu___930_69893.phase1);
                 failhard = (uu___930_69893.failhard);
                 nosynth = (uu___930_69893.nosynth);
                 uvar_subtyping = (uu___930_69893.uvar_subtyping);
                 tc_term = (uu___930_69893.tc_term);
                 type_of = (uu___930_69893.type_of);
                 universe_of = (uu___930_69893.universe_of);
                 check_type_of = (uu___930_69893.check_type_of);
                 use_bv_sorts = (uu___930_69893.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_69893.normalized_eff_names);
                 fv_delta_depths = (uu___930_69893.fv_delta_depths);
                 proof_ns = (uu___930_69893.proof_ns);
                 synth_hook = (uu___930_69893.synth_hook);
                 splice = (uu___930_69893.splice);
                 postprocess = (uu___930_69893.postprocess);
                 is_native_tactic = (uu___930_69893.is_native_tactic);
                 identifier_info = (uu___930_69893.identifier_info);
                 tc_hooks = (uu___930_69893.tc_hooks);
                 dsenv = (uu___930_69893.dsenv);
                 nbe = (uu___930_69893.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____69910,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_69926 = env  in
               {
                 solver = (uu___939_69926.solver);
                 range = (uu___939_69926.range);
                 curmodule = (uu___939_69926.curmodule);
                 gamma = (uu___939_69926.gamma);
                 gamma_sig = (uu___939_69926.gamma_sig);
                 gamma_cache = (uu___939_69926.gamma_cache);
                 modules = (uu___939_69926.modules);
                 expected_typ = (uu___939_69926.expected_typ);
                 sigtab = (uu___939_69926.sigtab);
                 attrtab = (uu___939_69926.attrtab);
                 is_pattern = (uu___939_69926.is_pattern);
                 instantiate_imp = (uu___939_69926.instantiate_imp);
                 effects = (uu___939_69926.effects);
                 generalize = (uu___939_69926.generalize);
                 letrecs = (uu___939_69926.letrecs);
                 top_level = (uu___939_69926.top_level);
                 check_uvars = (uu___939_69926.check_uvars);
                 use_eq = (uu___939_69926.use_eq);
                 is_iface = (uu___939_69926.is_iface);
                 admit = (uu___939_69926.admit);
                 lax = (uu___939_69926.lax);
                 lax_universes = (uu___939_69926.lax_universes);
                 phase1 = (uu___939_69926.phase1);
                 failhard = (uu___939_69926.failhard);
                 nosynth = (uu___939_69926.nosynth);
                 uvar_subtyping = (uu___939_69926.uvar_subtyping);
                 tc_term = (uu___939_69926.tc_term);
                 type_of = (uu___939_69926.type_of);
                 universe_of = (uu___939_69926.universe_of);
                 check_type_of = (uu___939_69926.check_type_of);
                 use_bv_sorts = (uu___939_69926.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_69926.normalized_eff_names);
                 fv_delta_depths = (uu___939_69926.fv_delta_depths);
                 proof_ns = (uu___939_69926.proof_ns);
                 synth_hook = (uu___939_69926.synth_hook);
                 splice = (uu___939_69926.splice);
                 postprocess = (uu___939_69926.postprocess);
                 is_native_tactic = (uu___939_69926.is_native_tactic);
                 identifier_info = (uu___939_69926.identifier_info);
                 tc_hooks = (uu___939_69926.tc_hooks);
                 dsenv = (uu___939_69926.dsenv);
                 nbe = (uu___939_69926.nbe)
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
        (let uu___946_69969 = e  in
         {
           solver = (uu___946_69969.solver);
           range = r;
           curmodule = (uu___946_69969.curmodule);
           gamma = (uu___946_69969.gamma);
           gamma_sig = (uu___946_69969.gamma_sig);
           gamma_cache = (uu___946_69969.gamma_cache);
           modules = (uu___946_69969.modules);
           expected_typ = (uu___946_69969.expected_typ);
           sigtab = (uu___946_69969.sigtab);
           attrtab = (uu___946_69969.attrtab);
           is_pattern = (uu___946_69969.is_pattern);
           instantiate_imp = (uu___946_69969.instantiate_imp);
           effects = (uu___946_69969.effects);
           generalize = (uu___946_69969.generalize);
           letrecs = (uu___946_69969.letrecs);
           top_level = (uu___946_69969.top_level);
           check_uvars = (uu___946_69969.check_uvars);
           use_eq = (uu___946_69969.use_eq);
           is_iface = (uu___946_69969.is_iface);
           admit = (uu___946_69969.admit);
           lax = (uu___946_69969.lax);
           lax_universes = (uu___946_69969.lax_universes);
           phase1 = (uu___946_69969.phase1);
           failhard = (uu___946_69969.failhard);
           nosynth = (uu___946_69969.nosynth);
           uvar_subtyping = (uu___946_69969.uvar_subtyping);
           tc_term = (uu___946_69969.tc_term);
           type_of = (uu___946_69969.type_of);
           universe_of = (uu___946_69969.universe_of);
           check_type_of = (uu___946_69969.check_type_of);
           use_bv_sorts = (uu___946_69969.use_bv_sorts);
           qtbl_name_and_index = (uu___946_69969.qtbl_name_and_index);
           normalized_eff_names = (uu___946_69969.normalized_eff_names);
           fv_delta_depths = (uu___946_69969.fv_delta_depths);
           proof_ns = (uu___946_69969.proof_ns);
           synth_hook = (uu___946_69969.synth_hook);
           splice = (uu___946_69969.splice);
           postprocess = (uu___946_69969.postprocess);
           is_native_tactic = (uu___946_69969.is_native_tactic);
           identifier_info = (uu___946_69969.identifier_info);
           tc_hooks = (uu___946_69969.tc_hooks);
           dsenv = (uu___946_69969.dsenv);
           nbe = (uu___946_69969.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____69989 =
        let uu____69990 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____69990 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____69989
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____70045 =
          let uu____70046 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____70046 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70045
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____70101 =
          let uu____70102 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____70102 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70101
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____70157 =
        let uu____70158 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____70158 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____70157
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_70222 = env  in
      {
        solver = (uu___963_70222.solver);
        range = (uu___963_70222.range);
        curmodule = lid;
        gamma = (uu___963_70222.gamma);
        gamma_sig = (uu___963_70222.gamma_sig);
        gamma_cache = (uu___963_70222.gamma_cache);
        modules = (uu___963_70222.modules);
        expected_typ = (uu___963_70222.expected_typ);
        sigtab = (uu___963_70222.sigtab);
        attrtab = (uu___963_70222.attrtab);
        is_pattern = (uu___963_70222.is_pattern);
        instantiate_imp = (uu___963_70222.instantiate_imp);
        effects = (uu___963_70222.effects);
        generalize = (uu___963_70222.generalize);
        letrecs = (uu___963_70222.letrecs);
        top_level = (uu___963_70222.top_level);
        check_uvars = (uu___963_70222.check_uvars);
        use_eq = (uu___963_70222.use_eq);
        is_iface = (uu___963_70222.is_iface);
        admit = (uu___963_70222.admit);
        lax = (uu___963_70222.lax);
        lax_universes = (uu___963_70222.lax_universes);
        phase1 = (uu___963_70222.phase1);
        failhard = (uu___963_70222.failhard);
        nosynth = (uu___963_70222.nosynth);
        uvar_subtyping = (uu___963_70222.uvar_subtyping);
        tc_term = (uu___963_70222.tc_term);
        type_of = (uu___963_70222.type_of);
        universe_of = (uu___963_70222.universe_of);
        check_type_of = (uu___963_70222.check_type_of);
        use_bv_sorts = (uu___963_70222.use_bv_sorts);
        qtbl_name_and_index = (uu___963_70222.qtbl_name_and_index);
        normalized_eff_names = (uu___963_70222.normalized_eff_names);
        fv_delta_depths = (uu___963_70222.fv_delta_depths);
        proof_ns = (uu___963_70222.proof_ns);
        synth_hook = (uu___963_70222.synth_hook);
        splice = (uu___963_70222.splice);
        postprocess = (uu___963_70222.postprocess);
        is_native_tactic = (uu___963_70222.is_native_tactic);
        identifier_info = (uu___963_70222.identifier_info);
        tc_hooks = (uu___963_70222.tc_hooks);
        dsenv = (uu___963_70222.dsenv);
        nbe = (uu___963_70222.nbe)
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
      let uu____70253 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____70253
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____70266 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____70266)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____70281 =
      let uu____70283 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____70283  in
    (FStar_Errors.Fatal_VariableNotFound, uu____70281)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____70292  ->
    let uu____70293 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____70293
  
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
      | ((formals,t),uu____70393) ->
          let vs = mk_univ_subst formals us  in
          let uu____70417 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____70417)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_70434  ->
    match uu___447_70434 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____70460  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____70480 = inst_tscheme t  in
      match uu____70480 with
      | (us,t1) ->
          let uu____70491 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____70491)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____70512  ->
          match uu____70512 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____70534 =
                         let uu____70536 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____70540 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____70544 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____70546 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____70536 uu____70540 uu____70544 uu____70546
                          in
                       failwith uu____70534)
                    else ();
                    (let uu____70551 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____70551))
               | uu____70560 ->
                   let uu____70561 =
                     let uu____70563 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____70563
                      in
                   failwith uu____70561)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____70575 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____70586 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____70597 -> false
  
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
             | ([],uu____70645) -> Maybe
             | (uu____70652,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____70672 -> No  in
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
          let uu____70766 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____70766 with
          | FStar_Pervasives_Native.None  ->
              let uu____70789 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_70833  ->
                     match uu___448_70833 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____70872 = FStar_Ident.lid_equals lid l  in
                         if uu____70872
                         then
                           let uu____70895 =
                             let uu____70914 =
                               let uu____70929 = inst_tscheme t  in
                               FStar_Util.Inl uu____70929  in
                             let uu____70944 = FStar_Ident.range_of_lid l  in
                             (uu____70914, uu____70944)  in
                           FStar_Pervasives_Native.Some uu____70895
                         else FStar_Pervasives_Native.None
                     | uu____70997 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____70789
                (fun uu____71035  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_71044  ->
                        match uu___449_71044 with
                        | (uu____71047,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____71049);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____71050;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____71051;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____71052;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____71053;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____71073 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____71073
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
                                  uu____71125 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____71132 -> cache t  in
                            let uu____71133 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____71133 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____71139 =
                                   let uu____71140 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____71140)
                                    in
                                 maybe_cache uu____71139)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____71211 = find_in_sigtab env lid  in
         match uu____71211 with
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
      let uu____71292 = lookup_qname env lid  in
      match uu____71292 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____71313,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____71427 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____71427 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____71472 =
          let uu____71475 = lookup_attr env1 attr  in se1 :: uu____71475  in
        FStar_Util.smap_add (attrtab env1) attr uu____71472  in
      FStar_List.iter
        (fun attr  ->
           let uu____71485 =
             let uu____71486 = FStar_Syntax_Subst.compress attr  in
             uu____71486.FStar_Syntax_Syntax.n  in
           match uu____71485 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____71490 =
                 let uu____71492 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____71492.FStar_Ident.str  in
               add_one1 env se uu____71490
           | uu____71493 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____71516) ->
          add_sigelts env ses
      | uu____71525 ->
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
            | uu____71540 -> ()))

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
        (fun uu___450_71572  ->
           match uu___450_71572 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____71590 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____71652,lb::[]),uu____71654) ->
            let uu____71663 =
              let uu____71672 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____71681 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____71672, uu____71681)  in
            FStar_Pervasives_Native.Some uu____71663
        | FStar_Syntax_Syntax.Sig_let ((uu____71694,lbs),uu____71696) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____71728 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____71741 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____71741
                     then
                       let uu____71754 =
                         let uu____71763 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____71772 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____71763, uu____71772)  in
                       FStar_Pervasives_Native.Some uu____71754
                     else FStar_Pervasives_Native.None)
        | uu____71795 -> FStar_Pervasives_Native.None
  
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
          let uu____71855 =
            let uu____71864 =
              let uu____71869 =
                let uu____71870 =
                  let uu____71873 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____71873
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____71870)  in
              inst_tscheme1 uu____71869  in
            (uu____71864, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71855
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____71895,uu____71896) ->
          let uu____71901 =
            let uu____71910 =
              let uu____71915 =
                let uu____71916 =
                  let uu____71919 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____71919  in
                (us, uu____71916)  in
              inst_tscheme1 uu____71915  in
            (uu____71910, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71901
      | uu____71938 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____72027 =
          match uu____72027 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____72123,uvs,t,uu____72126,uu____72127,uu____72128);
                      FStar_Syntax_Syntax.sigrng = uu____72129;
                      FStar_Syntax_Syntax.sigquals = uu____72130;
                      FStar_Syntax_Syntax.sigmeta = uu____72131;
                      FStar_Syntax_Syntax.sigattrs = uu____72132;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72155 =
                     let uu____72164 = inst_tscheme1 (uvs, t)  in
                     (uu____72164, rng)  in
                   FStar_Pervasives_Native.Some uu____72155
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____72188;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____72190;
                      FStar_Syntax_Syntax.sigattrs = uu____72191;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72208 =
                     let uu____72210 = in_cur_mod env l  in uu____72210 = Yes
                      in
                   if uu____72208
                   then
                     let uu____72222 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____72222
                      then
                        let uu____72238 =
                          let uu____72247 = inst_tscheme1 (uvs, t)  in
                          (uu____72247, rng)  in
                        FStar_Pervasives_Native.Some uu____72238
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____72280 =
                        let uu____72289 = inst_tscheme1 (uvs, t)  in
                        (uu____72289, rng)  in
                      FStar_Pervasives_Native.Some uu____72280)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72314,uu____72315);
                      FStar_Syntax_Syntax.sigrng = uu____72316;
                      FStar_Syntax_Syntax.sigquals = uu____72317;
                      FStar_Syntax_Syntax.sigmeta = uu____72318;
                      FStar_Syntax_Syntax.sigattrs = uu____72319;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____72360 =
                          let uu____72369 = inst_tscheme1 (uvs, k)  in
                          (uu____72369, rng)  in
                        FStar_Pervasives_Native.Some uu____72360
                    | uu____72390 ->
                        let uu____72391 =
                          let uu____72400 =
                            let uu____72405 =
                              let uu____72406 =
                                let uu____72409 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72409
                                 in
                              (uvs, uu____72406)  in
                            inst_tscheme1 uu____72405  in
                          (uu____72400, rng)  in
                        FStar_Pervasives_Native.Some uu____72391)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72432,uu____72433);
                      FStar_Syntax_Syntax.sigrng = uu____72434;
                      FStar_Syntax_Syntax.sigquals = uu____72435;
                      FStar_Syntax_Syntax.sigmeta = uu____72436;
                      FStar_Syntax_Syntax.sigattrs = uu____72437;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____72479 =
                          let uu____72488 = inst_tscheme_with (uvs, k) us  in
                          (uu____72488, rng)  in
                        FStar_Pervasives_Native.Some uu____72479
                    | uu____72509 ->
                        let uu____72510 =
                          let uu____72519 =
                            let uu____72524 =
                              let uu____72525 =
                                let uu____72528 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72528
                                 in
                              (uvs, uu____72525)  in
                            inst_tscheme_with uu____72524 us  in
                          (uu____72519, rng)  in
                        FStar_Pervasives_Native.Some uu____72510)
               | FStar_Util.Inr se ->
                   let uu____72564 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____72585;
                          FStar_Syntax_Syntax.sigrng = uu____72586;
                          FStar_Syntax_Syntax.sigquals = uu____72587;
                          FStar_Syntax_Syntax.sigmeta = uu____72588;
                          FStar_Syntax_Syntax.sigattrs = uu____72589;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____72604 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____72564
                     (FStar_Util.map_option
                        (fun uu____72652  ->
                           match uu____72652 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____72683 =
          let uu____72694 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____72694 mapper  in
        match uu____72683 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____72768 =
              let uu____72779 =
                let uu____72786 =
                  let uu___1290_72789 = t  in
                  let uu____72790 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_72789.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____72790;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_72789.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____72786)  in
              (uu____72779, r)  in
            FStar_Pervasives_Native.Some uu____72768
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____72839 = lookup_qname env l  in
      match uu____72839 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____72860 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____72914 = try_lookup_bv env bv  in
      match uu____72914 with
      | FStar_Pervasives_Native.None  ->
          let uu____72929 = variable_not_found bv  in
          FStar_Errors.raise_error uu____72929 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____72945 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____72946 =
            let uu____72947 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____72947  in
          (uu____72945, uu____72946)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____72969 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____72969 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____73035 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____73035  in
          let uu____73036 =
            let uu____73045 =
              let uu____73050 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____73050)  in
            (uu____73045, r1)  in
          FStar_Pervasives_Native.Some uu____73036
  
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
        let uu____73085 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____73085 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____73118,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____73143 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____73143  in
            let uu____73144 =
              let uu____73149 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____73149, r1)  in
            FStar_Pervasives_Native.Some uu____73144
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____73173 = try_lookup_lid env l  in
      match uu____73173 with
      | FStar_Pervasives_Native.None  ->
          let uu____73200 = name_not_found l  in
          let uu____73206 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____73200 uu____73206
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_73249  ->
              match uu___451_73249 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____73253 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____73274 = lookup_qname env lid  in
      match uu____73274 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73283,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73286;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73288;
              FStar_Syntax_Syntax.sigattrs = uu____73289;_},FStar_Pervasives_Native.None
            ),uu____73290)
          ->
          let uu____73339 =
            let uu____73346 =
              let uu____73347 =
                let uu____73350 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____73350 t  in
              (uvs, uu____73347)  in
            (uu____73346, q)  in
          FStar_Pervasives_Native.Some uu____73339
      | uu____73363 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73385 = lookup_qname env lid  in
      match uu____73385 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73390,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73393;
              FStar_Syntax_Syntax.sigquals = uu____73394;
              FStar_Syntax_Syntax.sigmeta = uu____73395;
              FStar_Syntax_Syntax.sigattrs = uu____73396;_},FStar_Pervasives_Native.None
            ),uu____73397)
          ->
          let uu____73446 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73446 (uvs, t)
      | uu____73451 ->
          let uu____73452 = name_not_found lid  in
          let uu____73458 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73452 uu____73458
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73478 = lookup_qname env lid  in
      match uu____73478 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73483,uvs,t,uu____73486,uu____73487,uu____73488);
              FStar_Syntax_Syntax.sigrng = uu____73489;
              FStar_Syntax_Syntax.sigquals = uu____73490;
              FStar_Syntax_Syntax.sigmeta = uu____73491;
              FStar_Syntax_Syntax.sigattrs = uu____73492;_},FStar_Pervasives_Native.None
            ),uu____73493)
          ->
          let uu____73548 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73548 (uvs, t)
      | uu____73553 ->
          let uu____73554 = name_not_found lid  in
          let uu____73560 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73554 uu____73560
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____73583 = lookup_qname env lid  in
      match uu____73583 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____73591,uu____73592,uu____73593,uu____73594,uu____73595,dcs);
              FStar_Syntax_Syntax.sigrng = uu____73597;
              FStar_Syntax_Syntax.sigquals = uu____73598;
              FStar_Syntax_Syntax.sigmeta = uu____73599;
              FStar_Syntax_Syntax.sigattrs = uu____73600;_},uu____73601),uu____73602)
          -> (true, dcs)
      | uu____73665 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____73681 = lookup_qname env lid  in
      match uu____73681 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73682,uu____73683,uu____73684,l,uu____73686,uu____73687);
              FStar_Syntax_Syntax.sigrng = uu____73688;
              FStar_Syntax_Syntax.sigquals = uu____73689;
              FStar_Syntax_Syntax.sigmeta = uu____73690;
              FStar_Syntax_Syntax.sigattrs = uu____73691;_},uu____73692),uu____73693)
          -> l
      | uu____73750 ->
          let uu____73751 =
            let uu____73753 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____73753  in
          failwith uu____73751
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____73823)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____73880) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____73904 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____73904
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____73939 -> FStar_Pervasives_Native.None)
          | uu____73948 -> FStar_Pervasives_Native.None
  
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
        let uu____74010 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____74010
  
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
        let uu____74043 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____74043
  
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
             (FStar_Util.Inl uu____74095,uu____74096) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____74145),uu____74146) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____74195 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____74213 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____74223 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____74240 ->
                  let uu____74247 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____74247
              | FStar_Syntax_Syntax.Sig_let ((uu____74248,lbs),uu____74250)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____74266 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____74266
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____74273 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____74281 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____74282 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____74289 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74290 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____74291 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74292 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____74305 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____74323 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____74323
           (fun d_opt  ->
              let uu____74336 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____74336
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____74346 =
                   let uu____74349 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____74349  in
                 match uu____74346 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____74350 =
                       let uu____74352 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____74352
                        in
                     failwith uu____74350
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____74357 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____74357
                       then
                         let uu____74360 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____74362 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____74364 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____74360 uu____74362 uu____74364
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
        (FStar_Util.Inr (se,uu____74389),uu____74390) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____74439 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____74461),uu____74462) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____74511 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____74533 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____74533
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____74556 = lookup_attrs_of_lid env fv_lid1  in
        match uu____74556 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____74580 =
                      let uu____74581 = FStar_Syntax_Util.un_uinst tm  in
                      uu____74581.FStar_Syntax_Syntax.n  in
                    match uu____74580 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____74586 -> false))
  
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
      let uu____74620 = lookup_qname env ftv  in
      match uu____74620 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____74624) ->
          let uu____74669 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____74669 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____74690,t),r) ->
               let uu____74705 =
                 let uu____74706 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____74706 t  in
               FStar_Pervasives_Native.Some uu____74705)
      | uu____74707 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____74719 = try_lookup_effect_lid env ftv  in
      match uu____74719 with
      | FStar_Pervasives_Native.None  ->
          let uu____74722 = name_not_found ftv  in
          let uu____74728 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____74722 uu____74728
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
        let uu____74752 = lookup_qname env lid0  in
        match uu____74752 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____74763);
                FStar_Syntax_Syntax.sigrng = uu____74764;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____74766;
                FStar_Syntax_Syntax.sigattrs = uu____74767;_},FStar_Pervasives_Native.None
              ),uu____74768)
            ->
            let lid1 =
              let uu____74822 =
                let uu____74823 = FStar_Ident.range_of_lid lid  in
                let uu____74824 =
                  let uu____74825 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____74825  in
                FStar_Range.set_use_range uu____74823 uu____74824  in
              FStar_Ident.set_lid_range lid uu____74822  in
            let uu____74826 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_74832  ->
                      match uu___452_74832 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____74835 -> false))
               in
            if uu____74826
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____74854 =
                      let uu____74856 =
                        let uu____74858 = get_range env  in
                        FStar_Range.string_of_range uu____74858  in
                      let uu____74859 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____74861 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____74856 uu____74859 uu____74861
                       in
                    failwith uu____74854)
                  in
               match (binders, univs1) with
               | ([],uu____74882) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____74908,uu____74909::uu____74910::uu____74911) ->
                   let uu____74932 =
                     let uu____74934 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____74936 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____74934 uu____74936
                      in
                   failwith uu____74932
               | uu____74947 ->
                   let uu____74962 =
                     let uu____74967 =
                       let uu____74968 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____74968)  in
                     inst_tscheme_with uu____74967 insts  in
                   (match uu____74962 with
                    | (uu____74981,t) ->
                        let t1 =
                          let uu____74984 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____74984 t  in
                        let uu____74985 =
                          let uu____74986 = FStar_Syntax_Subst.compress t1
                             in
                          uu____74986.FStar_Syntax_Syntax.n  in
                        (match uu____74985 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____75021 -> failwith "Impossible")))
        | uu____75029 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____75053 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____75053 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____75066,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____75073 = find1 l2  in
            (match uu____75073 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____75080 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____75080 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____75084 = find1 l  in
            (match uu____75084 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____75089 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____75089
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____75104 = lookup_qname env l1  in
      match uu____75104 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____75107;
              FStar_Syntax_Syntax.sigrng = uu____75108;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____75110;
              FStar_Syntax_Syntax.sigattrs = uu____75111;_},uu____75112),uu____75113)
          -> q
      | uu____75164 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____75188 =
          let uu____75189 =
            let uu____75191 = FStar_Util.string_of_int i  in
            let uu____75193 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____75191 uu____75193
             in
          failwith uu____75189  in
        let uu____75196 = lookup_datacon env lid  in
        match uu____75196 with
        | (uu____75201,t) ->
            let uu____75203 =
              let uu____75204 = FStar_Syntax_Subst.compress t  in
              uu____75204.FStar_Syntax_Syntax.n  in
            (match uu____75203 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75208) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____75252 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____75252
                      FStar_Pervasives_Native.fst)
             | uu____75263 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75277 = lookup_qname env l  in
      match uu____75277 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____75279,uu____75280,uu____75281);
              FStar_Syntax_Syntax.sigrng = uu____75282;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75284;
              FStar_Syntax_Syntax.sigattrs = uu____75285;_},uu____75286),uu____75287)
          ->
          FStar_Util.for_some
            (fun uu___453_75340  ->
               match uu___453_75340 with
               | FStar_Syntax_Syntax.Projector uu____75342 -> true
               | uu____75348 -> false) quals
      | uu____75350 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75364 = lookup_qname env lid  in
      match uu____75364 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____75366,uu____75367,uu____75368,uu____75369,uu____75370,uu____75371);
              FStar_Syntax_Syntax.sigrng = uu____75372;
              FStar_Syntax_Syntax.sigquals = uu____75373;
              FStar_Syntax_Syntax.sigmeta = uu____75374;
              FStar_Syntax_Syntax.sigattrs = uu____75375;_},uu____75376),uu____75377)
          -> true
      | uu____75435 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75449 = lookup_qname env lid  in
      match uu____75449 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75451,uu____75452,uu____75453,uu____75454,uu____75455,uu____75456);
              FStar_Syntax_Syntax.sigrng = uu____75457;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75459;
              FStar_Syntax_Syntax.sigattrs = uu____75460;_},uu____75461),uu____75462)
          ->
          FStar_Util.for_some
            (fun uu___454_75523  ->
               match uu___454_75523 with
               | FStar_Syntax_Syntax.RecordType uu____75525 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____75535 -> true
               | uu____75545 -> false) quals
      | uu____75547 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____75557,uu____75558);
            FStar_Syntax_Syntax.sigrng = uu____75559;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____75561;
            FStar_Syntax_Syntax.sigattrs = uu____75562;_},uu____75563),uu____75564)
        ->
        FStar_Util.for_some
          (fun uu___455_75621  ->
             match uu___455_75621 with
             | FStar_Syntax_Syntax.Action uu____75623 -> true
             | uu____75625 -> false) quals
    | uu____75627 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75641 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____75641
  
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
      let uu____75658 =
        let uu____75659 = FStar_Syntax_Util.un_uinst head1  in
        uu____75659.FStar_Syntax_Syntax.n  in
      match uu____75658 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75665 ->
               true
           | uu____75668 -> false)
      | uu____75670 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75684 = lookup_qname env l  in
      match uu____75684 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75687),uu____75688) ->
          FStar_Util.for_some
            (fun uu___456_75736  ->
               match uu___456_75736 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75739 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75741 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75817 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75835) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75853 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75861 ->
                 FStar_Pervasives_Native.Some true
             | uu____75880 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75883 =
        let uu____75887 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75887 mapper  in
      match uu____75883 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75947 = lookup_qname env lid  in
      match uu____75947 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75951,uu____75952,tps,uu____75954,uu____75955,uu____75956);
              FStar_Syntax_Syntax.sigrng = uu____75957;
              FStar_Syntax_Syntax.sigquals = uu____75958;
              FStar_Syntax_Syntax.sigmeta = uu____75959;
              FStar_Syntax_Syntax.sigattrs = uu____75960;_},uu____75961),uu____75962)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____76028 -> FStar_Pervasives_Native.None
  
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
           (fun uu____76074  ->
              match uu____76074 with
              | (d,uu____76083) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____76099 = effect_decl_opt env l  in
      match uu____76099 with
      | FStar_Pervasives_Native.None  ->
          let uu____76114 = name_not_found l  in
          let uu____76120 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76114 uu____76120
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76143  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76162  ->
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
        let uu____76194 = FStar_Ident.lid_equals l1 l2  in
        if uu____76194
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76205 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76205
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76216 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____76269  ->
                        match uu____76269 with
                        | (m1,m2,uu____76283,uu____76284,uu____76285) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76216 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76302 =
                    let uu____76308 =
                      let uu____76310 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____76312 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____76310
                        uu____76312
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____76308)
                     in
                  FStar_Errors.raise_error uu____76302 env.range
              | FStar_Pervasives_Native.Some
                  (uu____76322,uu____76323,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____76357 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____76357
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
  'Auu____76377 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____76377) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____76406 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____76432  ->
                match uu____76432 with
                | (d,uu____76439) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____76406 with
      | FStar_Pervasives_Native.None  ->
          let uu____76450 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____76450
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____76465 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____76465 with
           | (uu____76480,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____76498)::(wp,uu____76500)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____76556 -> failwith "Impossible"))
  
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
          let uu____76614 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____76614
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____76619 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____76619
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
                  let uu____76630 = get_range env  in
                  let uu____76631 =
                    let uu____76638 =
                      let uu____76639 =
                        let uu____76656 =
                          let uu____76667 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____76667]  in
                        (null_wp, uu____76656)  in
                      FStar_Syntax_Syntax.Tm_app uu____76639  in
                    FStar_Syntax_Syntax.mk uu____76638  in
                  uu____76631 FStar_Pervasives_Native.None uu____76630  in
                let uu____76707 =
                  let uu____76708 =
                    let uu____76719 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____76719]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____76708;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____76707))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_76757 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_76757.order);
              joins = (uu___1944_76757.joins)
            }  in
          let uu___1947_76766 = env  in
          {
            solver = (uu___1947_76766.solver);
            range = (uu___1947_76766.range);
            curmodule = (uu___1947_76766.curmodule);
            gamma = (uu___1947_76766.gamma);
            gamma_sig = (uu___1947_76766.gamma_sig);
            gamma_cache = (uu___1947_76766.gamma_cache);
            modules = (uu___1947_76766.modules);
            expected_typ = (uu___1947_76766.expected_typ);
            sigtab = (uu___1947_76766.sigtab);
            attrtab = (uu___1947_76766.attrtab);
            is_pattern = (uu___1947_76766.is_pattern);
            instantiate_imp = (uu___1947_76766.instantiate_imp);
            effects;
            generalize = (uu___1947_76766.generalize);
            letrecs = (uu___1947_76766.letrecs);
            top_level = (uu___1947_76766.top_level);
            check_uvars = (uu___1947_76766.check_uvars);
            use_eq = (uu___1947_76766.use_eq);
            is_iface = (uu___1947_76766.is_iface);
            admit = (uu___1947_76766.admit);
            lax = (uu___1947_76766.lax);
            lax_universes = (uu___1947_76766.lax_universes);
            phase1 = (uu___1947_76766.phase1);
            failhard = (uu___1947_76766.failhard);
            nosynth = (uu___1947_76766.nosynth);
            uvar_subtyping = (uu___1947_76766.uvar_subtyping);
            tc_term = (uu___1947_76766.tc_term);
            type_of = (uu___1947_76766.type_of);
            universe_of = (uu___1947_76766.universe_of);
            check_type_of = (uu___1947_76766.check_type_of);
            use_bv_sorts = (uu___1947_76766.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_76766.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_76766.normalized_eff_names);
            fv_delta_depths = (uu___1947_76766.fv_delta_depths);
            proof_ns = (uu___1947_76766.proof_ns);
            synth_hook = (uu___1947_76766.synth_hook);
            splice = (uu___1947_76766.splice);
            postprocess = (uu___1947_76766.postprocess);
            is_native_tactic = (uu___1947_76766.is_native_tactic);
            identifier_info = (uu___1947_76766.identifier_info);
            tc_hooks = (uu___1947_76766.tc_hooks);
            dsenv = (uu___1947_76766.dsenv);
            nbe = (uu___1947_76766.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____76796 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____76796  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____76954 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____76955 = l1 u t wp e  in
                                l2 u t uu____76954 uu____76955))
                | uu____76956 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____77028 = inst_tscheme_with lift_t [u]  in
            match uu____77028 with
            | (uu____77035,lift_t1) ->
                let uu____77037 =
                  let uu____77044 =
                    let uu____77045 =
                      let uu____77062 =
                        let uu____77073 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77082 =
                          let uu____77093 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____77093]  in
                        uu____77073 :: uu____77082  in
                      (lift_t1, uu____77062)  in
                    FStar_Syntax_Syntax.Tm_app uu____77045  in
                  FStar_Syntax_Syntax.mk uu____77044  in
                uu____77037 FStar_Pervasives_Native.None
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
            let uu____77206 = inst_tscheme_with lift_t [u]  in
            match uu____77206 with
            | (uu____77213,lift_t1) ->
                let uu____77215 =
                  let uu____77222 =
                    let uu____77223 =
                      let uu____77240 =
                        let uu____77251 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77260 =
                          let uu____77271 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____77280 =
                            let uu____77291 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____77291]  in
                          uu____77271 :: uu____77280  in
                        uu____77251 :: uu____77260  in
                      (lift_t1, uu____77240)  in
                    FStar_Syntax_Syntax.Tm_app uu____77223  in
                  FStar_Syntax_Syntax.mk uu____77222  in
                uu____77215 FStar_Pervasives_Native.None
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
              let uu____77396 =
                let uu____77397 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____77397
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____77396  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____77406 =
              let uu____77408 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____77408  in
            let uu____77409 =
              let uu____77411 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____77439 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____77439)
                 in
              FStar_Util.dflt "none" uu____77411  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____77406
              uu____77409
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____77468  ->
                    match uu____77468 with
                    | (e,uu____77476) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____77499 =
            match uu____77499 with
            | (i,j) ->
                let uu____77510 = FStar_Ident.lid_equals i j  in
                if uu____77510
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _77517  -> FStar_Pervasives_Native.Some _77517)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____77546 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____77556 = FStar_Ident.lid_equals i k  in
                        if uu____77556
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____77570 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____77570
                                  then []
                                  else
                                    (let uu____77577 =
                                       let uu____77586 =
                                         find_edge order1 (i, k)  in
                                       let uu____77589 =
                                         find_edge order1 (k, j)  in
                                       (uu____77586, uu____77589)  in
                                     match uu____77577 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____77604 =
                                           compose_edges e1 e2  in
                                         [uu____77604]
                                     | uu____77605 -> [])))))
                 in
              FStar_List.append order1 uu____77546  in
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
                   let uu____77635 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____77638 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____77638
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____77635
                   then
                     let uu____77645 =
                       let uu____77651 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____77651)
                        in
                     let uu____77655 = get_range env  in
                     FStar_Errors.raise_error uu____77645 uu____77655
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____77733 = FStar_Ident.lid_equals i j
                                   in
                                if uu____77733
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____77785 =
                                              let uu____77794 =
                                                find_edge order2 (i, k)  in
                                              let uu____77797 =
                                                find_edge order2 (j, k)  in
                                              (uu____77794, uu____77797)  in
                                            match uu____77785 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____77839,uu____77840)
                                                     ->
                                                     let uu____77847 =
                                                       let uu____77854 =
                                                         let uu____77856 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77856
                                                          in
                                                       let uu____77859 =
                                                         let uu____77861 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77861
                                                          in
                                                       (uu____77854,
                                                         uu____77859)
                                                        in
                                                     (match uu____77847 with
                                                      | (true ,true ) ->
                                                          let uu____77878 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____77878
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
                                            | uu____77921 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_77994 = env.effects  in
              { decls = (uu___2074_77994.decls); order = order2; joins }  in
            let uu___2077_77995 = env  in
            {
              solver = (uu___2077_77995.solver);
              range = (uu___2077_77995.range);
              curmodule = (uu___2077_77995.curmodule);
              gamma = (uu___2077_77995.gamma);
              gamma_sig = (uu___2077_77995.gamma_sig);
              gamma_cache = (uu___2077_77995.gamma_cache);
              modules = (uu___2077_77995.modules);
              expected_typ = (uu___2077_77995.expected_typ);
              sigtab = (uu___2077_77995.sigtab);
              attrtab = (uu___2077_77995.attrtab);
              is_pattern = (uu___2077_77995.is_pattern);
              instantiate_imp = (uu___2077_77995.instantiate_imp);
              effects;
              generalize = (uu___2077_77995.generalize);
              letrecs = (uu___2077_77995.letrecs);
              top_level = (uu___2077_77995.top_level);
              check_uvars = (uu___2077_77995.check_uvars);
              use_eq = (uu___2077_77995.use_eq);
              is_iface = (uu___2077_77995.is_iface);
              admit = (uu___2077_77995.admit);
              lax = (uu___2077_77995.lax);
              lax_universes = (uu___2077_77995.lax_universes);
              phase1 = (uu___2077_77995.phase1);
              failhard = (uu___2077_77995.failhard);
              nosynth = (uu___2077_77995.nosynth);
              uvar_subtyping = (uu___2077_77995.uvar_subtyping);
              tc_term = (uu___2077_77995.tc_term);
              type_of = (uu___2077_77995.type_of);
              universe_of = (uu___2077_77995.universe_of);
              check_type_of = (uu___2077_77995.check_type_of);
              use_bv_sorts = (uu___2077_77995.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_77995.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_77995.normalized_eff_names);
              fv_delta_depths = (uu___2077_77995.fv_delta_depths);
              proof_ns = (uu___2077_77995.proof_ns);
              synth_hook = (uu___2077_77995.synth_hook);
              splice = (uu___2077_77995.splice);
              postprocess = (uu___2077_77995.postprocess);
              is_native_tactic = (uu___2077_77995.is_native_tactic);
              identifier_info = (uu___2077_77995.identifier_info);
              tc_hooks = (uu___2077_77995.tc_hooks);
              dsenv = (uu___2077_77995.dsenv);
              nbe = (uu___2077_77995.nbe)
            }))
      | uu____77996 -> env
  
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
        | uu____78025 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____78038 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____78038 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____78055 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____78055 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____78080 =
                     let uu____78086 =
                       let uu____78088 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____78096 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____78107 =
                         let uu____78109 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____78109  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____78088 uu____78096 uu____78107
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____78086)
                      in
                   FStar_Errors.raise_error uu____78080
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____78117 =
                     let uu____78128 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____78128 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____78165  ->
                        fun uu____78166  ->
                          match (uu____78165, uu____78166) with
                          | ((x,uu____78196),(t,uu____78198)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____78117
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____78229 =
                     let uu___2115_78230 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_78230.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_78230.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_78230.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_78230.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____78229
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____78242 .
    'Auu____78242 ->
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
          let uu____78272 = effect_decl_opt env effect_name  in
          match uu____78272 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____78311 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____78334 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____78373 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____78373
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____78378 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____78378
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____78393 =
                     let uu____78396 = get_range env  in
                     let uu____78397 =
                       let uu____78404 =
                         let uu____78405 =
                           let uu____78422 =
                             let uu____78433 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____78433; wp]  in
                           (repr, uu____78422)  in
                         FStar_Syntax_Syntax.Tm_app uu____78405  in
                       FStar_Syntax_Syntax.mk uu____78404  in
                     uu____78397 FStar_Pervasives_Native.None uu____78396  in
                   FStar_Pervasives_Native.Some uu____78393)
  
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
      | uu____78580 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____78595 =
        let uu____78596 = FStar_Syntax_Subst.compress t  in
        uu____78596.FStar_Syntax_Syntax.n  in
      match uu____78595 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____78600,c) ->
          is_reifiable_comp env c
      | uu____78622 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____78642 =
           let uu____78644 = is_reifiable_effect env l  in
           Prims.op_Negation uu____78644  in
         if uu____78642
         then
           let uu____78647 =
             let uu____78653 =
               let uu____78655 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____78655
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____78653)  in
           let uu____78659 = get_range env  in
           FStar_Errors.raise_error uu____78647 uu____78659
         else ());
        (let uu____78662 = effect_repr_aux true env c u_c  in
         match uu____78662 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_78698 = env  in
        {
          solver = (uu___2180_78698.solver);
          range = (uu___2180_78698.range);
          curmodule = (uu___2180_78698.curmodule);
          gamma = (uu___2180_78698.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_78698.gamma_cache);
          modules = (uu___2180_78698.modules);
          expected_typ = (uu___2180_78698.expected_typ);
          sigtab = (uu___2180_78698.sigtab);
          attrtab = (uu___2180_78698.attrtab);
          is_pattern = (uu___2180_78698.is_pattern);
          instantiate_imp = (uu___2180_78698.instantiate_imp);
          effects = (uu___2180_78698.effects);
          generalize = (uu___2180_78698.generalize);
          letrecs = (uu___2180_78698.letrecs);
          top_level = (uu___2180_78698.top_level);
          check_uvars = (uu___2180_78698.check_uvars);
          use_eq = (uu___2180_78698.use_eq);
          is_iface = (uu___2180_78698.is_iface);
          admit = (uu___2180_78698.admit);
          lax = (uu___2180_78698.lax);
          lax_universes = (uu___2180_78698.lax_universes);
          phase1 = (uu___2180_78698.phase1);
          failhard = (uu___2180_78698.failhard);
          nosynth = (uu___2180_78698.nosynth);
          uvar_subtyping = (uu___2180_78698.uvar_subtyping);
          tc_term = (uu___2180_78698.tc_term);
          type_of = (uu___2180_78698.type_of);
          universe_of = (uu___2180_78698.universe_of);
          check_type_of = (uu___2180_78698.check_type_of);
          use_bv_sorts = (uu___2180_78698.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_78698.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_78698.normalized_eff_names);
          fv_delta_depths = (uu___2180_78698.fv_delta_depths);
          proof_ns = (uu___2180_78698.proof_ns);
          synth_hook = (uu___2180_78698.synth_hook);
          splice = (uu___2180_78698.splice);
          postprocess = (uu___2180_78698.postprocess);
          is_native_tactic = (uu___2180_78698.is_native_tactic);
          identifier_info = (uu___2180_78698.identifier_info);
          tc_hooks = (uu___2180_78698.tc_hooks);
          dsenv = (uu___2180_78698.dsenv);
          nbe = (uu___2180_78698.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_78712 = env  in
      {
        solver = (uu___2187_78712.solver);
        range = (uu___2187_78712.range);
        curmodule = (uu___2187_78712.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_78712.gamma_sig);
        gamma_cache = (uu___2187_78712.gamma_cache);
        modules = (uu___2187_78712.modules);
        expected_typ = (uu___2187_78712.expected_typ);
        sigtab = (uu___2187_78712.sigtab);
        attrtab = (uu___2187_78712.attrtab);
        is_pattern = (uu___2187_78712.is_pattern);
        instantiate_imp = (uu___2187_78712.instantiate_imp);
        effects = (uu___2187_78712.effects);
        generalize = (uu___2187_78712.generalize);
        letrecs = (uu___2187_78712.letrecs);
        top_level = (uu___2187_78712.top_level);
        check_uvars = (uu___2187_78712.check_uvars);
        use_eq = (uu___2187_78712.use_eq);
        is_iface = (uu___2187_78712.is_iface);
        admit = (uu___2187_78712.admit);
        lax = (uu___2187_78712.lax);
        lax_universes = (uu___2187_78712.lax_universes);
        phase1 = (uu___2187_78712.phase1);
        failhard = (uu___2187_78712.failhard);
        nosynth = (uu___2187_78712.nosynth);
        uvar_subtyping = (uu___2187_78712.uvar_subtyping);
        tc_term = (uu___2187_78712.tc_term);
        type_of = (uu___2187_78712.type_of);
        universe_of = (uu___2187_78712.universe_of);
        check_type_of = (uu___2187_78712.check_type_of);
        use_bv_sorts = (uu___2187_78712.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_78712.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_78712.normalized_eff_names);
        fv_delta_depths = (uu___2187_78712.fv_delta_depths);
        proof_ns = (uu___2187_78712.proof_ns);
        synth_hook = (uu___2187_78712.synth_hook);
        splice = (uu___2187_78712.splice);
        postprocess = (uu___2187_78712.postprocess);
        is_native_tactic = (uu___2187_78712.is_native_tactic);
        identifier_info = (uu___2187_78712.identifier_info);
        tc_hooks = (uu___2187_78712.tc_hooks);
        dsenv = (uu___2187_78712.dsenv);
        nbe = (uu___2187_78712.nbe)
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
            (let uu___2200_78770 = env  in
             {
               solver = (uu___2200_78770.solver);
               range = (uu___2200_78770.range);
               curmodule = (uu___2200_78770.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_78770.gamma_sig);
               gamma_cache = (uu___2200_78770.gamma_cache);
               modules = (uu___2200_78770.modules);
               expected_typ = (uu___2200_78770.expected_typ);
               sigtab = (uu___2200_78770.sigtab);
               attrtab = (uu___2200_78770.attrtab);
               is_pattern = (uu___2200_78770.is_pattern);
               instantiate_imp = (uu___2200_78770.instantiate_imp);
               effects = (uu___2200_78770.effects);
               generalize = (uu___2200_78770.generalize);
               letrecs = (uu___2200_78770.letrecs);
               top_level = (uu___2200_78770.top_level);
               check_uvars = (uu___2200_78770.check_uvars);
               use_eq = (uu___2200_78770.use_eq);
               is_iface = (uu___2200_78770.is_iface);
               admit = (uu___2200_78770.admit);
               lax = (uu___2200_78770.lax);
               lax_universes = (uu___2200_78770.lax_universes);
               phase1 = (uu___2200_78770.phase1);
               failhard = (uu___2200_78770.failhard);
               nosynth = (uu___2200_78770.nosynth);
               uvar_subtyping = (uu___2200_78770.uvar_subtyping);
               tc_term = (uu___2200_78770.tc_term);
               type_of = (uu___2200_78770.type_of);
               universe_of = (uu___2200_78770.universe_of);
               check_type_of = (uu___2200_78770.check_type_of);
               use_bv_sorts = (uu___2200_78770.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_78770.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_78770.normalized_eff_names);
               fv_delta_depths = (uu___2200_78770.fv_delta_depths);
               proof_ns = (uu___2200_78770.proof_ns);
               synth_hook = (uu___2200_78770.synth_hook);
               splice = (uu___2200_78770.splice);
               postprocess = (uu___2200_78770.postprocess);
               is_native_tactic = (uu___2200_78770.is_native_tactic);
               identifier_info = (uu___2200_78770.identifier_info);
               tc_hooks = (uu___2200_78770.tc_hooks);
               dsenv = (uu___2200_78770.dsenv);
               nbe = (uu___2200_78770.nbe)
             }))
    | uu____78771 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____78800  ->
             match uu____78800 with | (x,uu____78808) -> push_bv env1 x) env
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
            let uu___2214_78843 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_78843.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_78843.FStar_Syntax_Syntax.index);
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
      (let uu___2225_78885 = env  in
       {
         solver = (uu___2225_78885.solver);
         range = (uu___2225_78885.range);
         curmodule = (uu___2225_78885.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_78885.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_78885.sigtab);
         attrtab = (uu___2225_78885.attrtab);
         is_pattern = (uu___2225_78885.is_pattern);
         instantiate_imp = (uu___2225_78885.instantiate_imp);
         effects = (uu___2225_78885.effects);
         generalize = (uu___2225_78885.generalize);
         letrecs = (uu___2225_78885.letrecs);
         top_level = (uu___2225_78885.top_level);
         check_uvars = (uu___2225_78885.check_uvars);
         use_eq = (uu___2225_78885.use_eq);
         is_iface = (uu___2225_78885.is_iface);
         admit = (uu___2225_78885.admit);
         lax = (uu___2225_78885.lax);
         lax_universes = (uu___2225_78885.lax_universes);
         phase1 = (uu___2225_78885.phase1);
         failhard = (uu___2225_78885.failhard);
         nosynth = (uu___2225_78885.nosynth);
         uvar_subtyping = (uu___2225_78885.uvar_subtyping);
         tc_term = (uu___2225_78885.tc_term);
         type_of = (uu___2225_78885.type_of);
         universe_of = (uu___2225_78885.universe_of);
         check_type_of = (uu___2225_78885.check_type_of);
         use_bv_sorts = (uu___2225_78885.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_78885.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_78885.normalized_eff_names);
         fv_delta_depths = (uu___2225_78885.fv_delta_depths);
         proof_ns = (uu___2225_78885.proof_ns);
         synth_hook = (uu___2225_78885.synth_hook);
         splice = (uu___2225_78885.splice);
         postprocess = (uu___2225_78885.postprocess);
         is_native_tactic = (uu___2225_78885.is_native_tactic);
         identifier_info = (uu___2225_78885.identifier_info);
         tc_hooks = (uu___2225_78885.tc_hooks);
         dsenv = (uu___2225_78885.dsenv);
         nbe = (uu___2225_78885.nbe)
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
        let uu____78929 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____78929 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____78957 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____78957)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_78973 = env  in
      {
        solver = (uu___2240_78973.solver);
        range = (uu___2240_78973.range);
        curmodule = (uu___2240_78973.curmodule);
        gamma = (uu___2240_78973.gamma);
        gamma_sig = (uu___2240_78973.gamma_sig);
        gamma_cache = (uu___2240_78973.gamma_cache);
        modules = (uu___2240_78973.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_78973.sigtab);
        attrtab = (uu___2240_78973.attrtab);
        is_pattern = (uu___2240_78973.is_pattern);
        instantiate_imp = (uu___2240_78973.instantiate_imp);
        effects = (uu___2240_78973.effects);
        generalize = (uu___2240_78973.generalize);
        letrecs = (uu___2240_78973.letrecs);
        top_level = (uu___2240_78973.top_level);
        check_uvars = (uu___2240_78973.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_78973.is_iface);
        admit = (uu___2240_78973.admit);
        lax = (uu___2240_78973.lax);
        lax_universes = (uu___2240_78973.lax_universes);
        phase1 = (uu___2240_78973.phase1);
        failhard = (uu___2240_78973.failhard);
        nosynth = (uu___2240_78973.nosynth);
        uvar_subtyping = (uu___2240_78973.uvar_subtyping);
        tc_term = (uu___2240_78973.tc_term);
        type_of = (uu___2240_78973.type_of);
        universe_of = (uu___2240_78973.universe_of);
        check_type_of = (uu___2240_78973.check_type_of);
        use_bv_sorts = (uu___2240_78973.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_78973.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_78973.normalized_eff_names);
        fv_delta_depths = (uu___2240_78973.fv_delta_depths);
        proof_ns = (uu___2240_78973.proof_ns);
        synth_hook = (uu___2240_78973.synth_hook);
        splice = (uu___2240_78973.splice);
        postprocess = (uu___2240_78973.postprocess);
        is_native_tactic = (uu___2240_78973.is_native_tactic);
        identifier_info = (uu___2240_78973.identifier_info);
        tc_hooks = (uu___2240_78973.tc_hooks);
        dsenv = (uu___2240_78973.dsenv);
        nbe = (uu___2240_78973.nbe)
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
    let uu____79004 = expected_typ env_  in
    ((let uu___2247_79010 = env_  in
      {
        solver = (uu___2247_79010.solver);
        range = (uu___2247_79010.range);
        curmodule = (uu___2247_79010.curmodule);
        gamma = (uu___2247_79010.gamma);
        gamma_sig = (uu___2247_79010.gamma_sig);
        gamma_cache = (uu___2247_79010.gamma_cache);
        modules = (uu___2247_79010.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_79010.sigtab);
        attrtab = (uu___2247_79010.attrtab);
        is_pattern = (uu___2247_79010.is_pattern);
        instantiate_imp = (uu___2247_79010.instantiate_imp);
        effects = (uu___2247_79010.effects);
        generalize = (uu___2247_79010.generalize);
        letrecs = (uu___2247_79010.letrecs);
        top_level = (uu___2247_79010.top_level);
        check_uvars = (uu___2247_79010.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_79010.is_iface);
        admit = (uu___2247_79010.admit);
        lax = (uu___2247_79010.lax);
        lax_universes = (uu___2247_79010.lax_universes);
        phase1 = (uu___2247_79010.phase1);
        failhard = (uu___2247_79010.failhard);
        nosynth = (uu___2247_79010.nosynth);
        uvar_subtyping = (uu___2247_79010.uvar_subtyping);
        tc_term = (uu___2247_79010.tc_term);
        type_of = (uu___2247_79010.type_of);
        universe_of = (uu___2247_79010.universe_of);
        check_type_of = (uu___2247_79010.check_type_of);
        use_bv_sorts = (uu___2247_79010.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_79010.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_79010.normalized_eff_names);
        fv_delta_depths = (uu___2247_79010.fv_delta_depths);
        proof_ns = (uu___2247_79010.proof_ns);
        synth_hook = (uu___2247_79010.synth_hook);
        splice = (uu___2247_79010.splice);
        postprocess = (uu___2247_79010.postprocess);
        is_native_tactic = (uu___2247_79010.is_native_tactic);
        identifier_info = (uu___2247_79010.identifier_info);
        tc_hooks = (uu___2247_79010.tc_hooks);
        dsenv = (uu___2247_79010.dsenv);
        nbe = (uu___2247_79010.nbe)
      }), uu____79004)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____79022 =
      let uu____79025 = FStar_Ident.id_of_text ""  in [uu____79025]  in
    FStar_Ident.lid_of_ids uu____79022  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____79032 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____79032
        then
          let uu____79037 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____79037 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_79065 = env  in
       {
         solver = (uu___2255_79065.solver);
         range = (uu___2255_79065.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_79065.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_79065.expected_typ);
         sigtab = (uu___2255_79065.sigtab);
         attrtab = (uu___2255_79065.attrtab);
         is_pattern = (uu___2255_79065.is_pattern);
         instantiate_imp = (uu___2255_79065.instantiate_imp);
         effects = (uu___2255_79065.effects);
         generalize = (uu___2255_79065.generalize);
         letrecs = (uu___2255_79065.letrecs);
         top_level = (uu___2255_79065.top_level);
         check_uvars = (uu___2255_79065.check_uvars);
         use_eq = (uu___2255_79065.use_eq);
         is_iface = (uu___2255_79065.is_iface);
         admit = (uu___2255_79065.admit);
         lax = (uu___2255_79065.lax);
         lax_universes = (uu___2255_79065.lax_universes);
         phase1 = (uu___2255_79065.phase1);
         failhard = (uu___2255_79065.failhard);
         nosynth = (uu___2255_79065.nosynth);
         uvar_subtyping = (uu___2255_79065.uvar_subtyping);
         tc_term = (uu___2255_79065.tc_term);
         type_of = (uu___2255_79065.type_of);
         universe_of = (uu___2255_79065.universe_of);
         check_type_of = (uu___2255_79065.check_type_of);
         use_bv_sorts = (uu___2255_79065.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_79065.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_79065.normalized_eff_names);
         fv_delta_depths = (uu___2255_79065.fv_delta_depths);
         proof_ns = (uu___2255_79065.proof_ns);
         synth_hook = (uu___2255_79065.synth_hook);
         splice = (uu___2255_79065.splice);
         postprocess = (uu___2255_79065.postprocess);
         is_native_tactic = (uu___2255_79065.is_native_tactic);
         identifier_info = (uu___2255_79065.identifier_info);
         tc_hooks = (uu___2255_79065.tc_hooks);
         dsenv = (uu___2255_79065.dsenv);
         nbe = (uu___2255_79065.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79117)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79121,(uu____79122,t)))::tl1
          ->
          let uu____79143 =
            let uu____79146 = FStar_Syntax_Free.uvars t  in
            ext out uu____79146  in
          aux uu____79143 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79149;
            FStar_Syntax_Syntax.index = uu____79150;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79158 =
            let uu____79161 = FStar_Syntax_Free.uvars t  in
            ext out uu____79161  in
          aux uu____79158 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79219)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79223,(uu____79224,t)))::tl1
          ->
          let uu____79245 =
            let uu____79248 = FStar_Syntax_Free.univs t  in
            ext out uu____79248  in
          aux uu____79245 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79251;
            FStar_Syntax_Syntax.index = uu____79252;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79260 =
            let uu____79263 = FStar_Syntax_Free.univs t  in
            ext out uu____79263  in
          aux uu____79260 tl1
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
          let uu____79325 = FStar_Util.set_add uname out  in
          aux uu____79325 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79328,(uu____79329,t)))::tl1
          ->
          let uu____79350 =
            let uu____79353 = FStar_Syntax_Free.univnames t  in
            ext out uu____79353  in
          aux uu____79350 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79356;
            FStar_Syntax_Syntax.index = uu____79357;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79365 =
            let uu____79368 = FStar_Syntax_Free.univnames t  in
            ext out uu____79368  in
          aux uu____79365 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_79389  ->
            match uu___457_79389 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____79393 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____79406 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____79417 =
      let uu____79426 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____79426
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____79417 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____79474 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_79487  ->
              match uu___458_79487 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____79490 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____79490
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____79496) ->
                  let uu____79513 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____79513))
       in
    FStar_All.pipe_right uu____79474 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_79527  ->
    match uu___459_79527 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____79533 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____79533
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____79556  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____79611) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____79644,uu____79645) -> false  in
      let uu____79659 =
        FStar_List.tryFind
          (fun uu____79681  ->
             match uu____79681 with | (p,uu____79692) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____79659 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____79711,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____79741 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____79741
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_79763 = e  in
        {
          solver = (uu___2398_79763.solver);
          range = (uu___2398_79763.range);
          curmodule = (uu___2398_79763.curmodule);
          gamma = (uu___2398_79763.gamma);
          gamma_sig = (uu___2398_79763.gamma_sig);
          gamma_cache = (uu___2398_79763.gamma_cache);
          modules = (uu___2398_79763.modules);
          expected_typ = (uu___2398_79763.expected_typ);
          sigtab = (uu___2398_79763.sigtab);
          attrtab = (uu___2398_79763.attrtab);
          is_pattern = (uu___2398_79763.is_pattern);
          instantiate_imp = (uu___2398_79763.instantiate_imp);
          effects = (uu___2398_79763.effects);
          generalize = (uu___2398_79763.generalize);
          letrecs = (uu___2398_79763.letrecs);
          top_level = (uu___2398_79763.top_level);
          check_uvars = (uu___2398_79763.check_uvars);
          use_eq = (uu___2398_79763.use_eq);
          is_iface = (uu___2398_79763.is_iface);
          admit = (uu___2398_79763.admit);
          lax = (uu___2398_79763.lax);
          lax_universes = (uu___2398_79763.lax_universes);
          phase1 = (uu___2398_79763.phase1);
          failhard = (uu___2398_79763.failhard);
          nosynth = (uu___2398_79763.nosynth);
          uvar_subtyping = (uu___2398_79763.uvar_subtyping);
          tc_term = (uu___2398_79763.tc_term);
          type_of = (uu___2398_79763.type_of);
          universe_of = (uu___2398_79763.universe_of);
          check_type_of = (uu___2398_79763.check_type_of);
          use_bv_sorts = (uu___2398_79763.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_79763.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_79763.normalized_eff_names);
          fv_delta_depths = (uu___2398_79763.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_79763.synth_hook);
          splice = (uu___2398_79763.splice);
          postprocess = (uu___2398_79763.postprocess);
          is_native_tactic = (uu___2398_79763.is_native_tactic);
          identifier_info = (uu___2398_79763.identifier_info);
          tc_hooks = (uu___2398_79763.tc_hooks);
          dsenv = (uu___2398_79763.dsenv);
          nbe = (uu___2398_79763.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_79811 = e  in
      {
        solver = (uu___2407_79811.solver);
        range = (uu___2407_79811.range);
        curmodule = (uu___2407_79811.curmodule);
        gamma = (uu___2407_79811.gamma);
        gamma_sig = (uu___2407_79811.gamma_sig);
        gamma_cache = (uu___2407_79811.gamma_cache);
        modules = (uu___2407_79811.modules);
        expected_typ = (uu___2407_79811.expected_typ);
        sigtab = (uu___2407_79811.sigtab);
        attrtab = (uu___2407_79811.attrtab);
        is_pattern = (uu___2407_79811.is_pattern);
        instantiate_imp = (uu___2407_79811.instantiate_imp);
        effects = (uu___2407_79811.effects);
        generalize = (uu___2407_79811.generalize);
        letrecs = (uu___2407_79811.letrecs);
        top_level = (uu___2407_79811.top_level);
        check_uvars = (uu___2407_79811.check_uvars);
        use_eq = (uu___2407_79811.use_eq);
        is_iface = (uu___2407_79811.is_iface);
        admit = (uu___2407_79811.admit);
        lax = (uu___2407_79811.lax);
        lax_universes = (uu___2407_79811.lax_universes);
        phase1 = (uu___2407_79811.phase1);
        failhard = (uu___2407_79811.failhard);
        nosynth = (uu___2407_79811.nosynth);
        uvar_subtyping = (uu___2407_79811.uvar_subtyping);
        tc_term = (uu___2407_79811.tc_term);
        type_of = (uu___2407_79811.type_of);
        universe_of = (uu___2407_79811.universe_of);
        check_type_of = (uu___2407_79811.check_type_of);
        use_bv_sorts = (uu___2407_79811.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_79811.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_79811.normalized_eff_names);
        fv_delta_depths = (uu___2407_79811.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_79811.synth_hook);
        splice = (uu___2407_79811.splice);
        postprocess = (uu___2407_79811.postprocess);
        is_native_tactic = (uu___2407_79811.is_native_tactic);
        identifier_info = (uu___2407_79811.identifier_info);
        tc_hooks = (uu___2407_79811.tc_hooks);
        dsenv = (uu___2407_79811.dsenv);
        nbe = (uu___2407_79811.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____79827 = FStar_Syntax_Free.names t  in
      let uu____79830 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____79827 uu____79830
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____79853 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____79853
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____79863 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____79863
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____79884 =
      match uu____79884 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____79904 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____79904)
       in
    let uu____79912 =
      let uu____79916 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____79916 FStar_List.rev  in
    FStar_All.pipe_right uu____79912 (FStar_String.concat " ")
  
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
                  (let uu____79986 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____79986 with
                   | FStar_Pervasives_Native.Some uu____79990 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____79993 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____80003;
        univ_ineqs = uu____80004; implicits = uu____80005;_} -> true
    | uu____80017 -> false
  
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
          let uu___2451_80048 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_80048.deferred);
            univ_ineqs = (uu___2451_80048.univ_ineqs);
            implicits = (uu___2451_80048.implicits)
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
          let uu____80087 = FStar_Options.defensive ()  in
          if uu____80087
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____80093 =
              let uu____80095 =
                let uu____80097 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____80097  in
              Prims.op_Negation uu____80095  in
            (if uu____80093
             then
               let uu____80104 =
                 let uu____80110 =
                   let uu____80112 = FStar_Syntax_Print.term_to_string t  in
                   let uu____80114 =
                     let uu____80116 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____80116
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____80112 uu____80114
                    in
                 (FStar_Errors.Warning_Defensive, uu____80110)  in
               FStar_Errors.log_issue rng uu____80104
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
          let uu____80156 =
            let uu____80158 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80158  in
          if uu____80156
          then ()
          else
            (let uu____80163 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____80163 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____80189 =
            let uu____80191 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80191  in
          if uu____80189
          then ()
          else
            (let uu____80196 = bound_vars e  in
             def_check_closed_in rng msg uu____80196 t)
  
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
          let uu___2488_80235 = g  in
          let uu____80236 =
            let uu____80237 =
              let uu____80238 =
                let uu____80245 =
                  let uu____80246 =
                    let uu____80263 =
                      let uu____80274 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____80274]  in
                    (f, uu____80263)  in
                  FStar_Syntax_Syntax.Tm_app uu____80246  in
                FStar_Syntax_Syntax.mk uu____80245  in
              uu____80238 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _80314  -> FStar_TypeChecker_Common.NonTrivial _80314)
              uu____80237
             in
          {
            guard_f = uu____80236;
            deferred = (uu___2488_80235.deferred);
            univ_ineqs = (uu___2488_80235.univ_ineqs);
            implicits = (uu___2488_80235.implicits)
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
          let uu___2495_80332 = g  in
          let uu____80333 =
            let uu____80334 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80334  in
          {
            guard_f = uu____80333;
            deferred = (uu___2495_80332.deferred);
            univ_ineqs = (uu___2495_80332.univ_ineqs);
            implicits = (uu___2495_80332.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_80351 = g  in
          let uu____80352 =
            let uu____80353 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____80353  in
          {
            guard_f = uu____80352;
            deferred = (uu___2500_80351.deferred);
            univ_ineqs = (uu___2500_80351.univ_ineqs);
            implicits = (uu___2500_80351.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_80355 = g  in
          let uu____80356 =
            let uu____80357 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80357  in
          {
            guard_f = uu____80356;
            deferred = (uu___2504_80355.deferred);
            univ_ineqs = (uu___2504_80355.univ_ineqs);
            implicits = (uu___2504_80355.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____80364 ->
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
          let uu____80381 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____80381
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____80388 =
      let uu____80389 = FStar_Syntax_Util.unmeta t  in
      uu____80389.FStar_Syntax_Syntax.n  in
    match uu____80388 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____80393 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____80436 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____80436;
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
                       let uu____80531 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____80531
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_80538 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_80538.deferred);
              univ_ineqs = (uu___2559_80538.univ_ineqs);
              implicits = (uu___2559_80538.implicits)
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
               let uu____80572 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____80572
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
            let uu___2574_80599 = g  in
            let uu____80600 =
              let uu____80601 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____80601  in
            {
              guard_f = uu____80600;
              deferred = (uu___2574_80599.deferred);
              univ_ineqs = (uu___2574_80599.univ_ineqs);
              implicits = (uu___2574_80599.implicits)
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
              let uu____80659 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____80659 with
              | FStar_Pervasives_Native.Some
                  (uu____80684::(tm,uu____80686)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____80750 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____80768 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____80768;
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
                      let uu___2596_80800 = trivial_guard  in
                      {
                        guard_f = (uu___2596_80800.guard_f);
                        deferred = (uu___2596_80800.deferred);
                        univ_ineqs = (uu___2596_80800.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____80818  -> ());
    push = (fun uu____80820  -> ());
    pop = (fun uu____80823  -> ());
    snapshot =
      (fun uu____80826  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____80845  -> fun uu____80846  -> ());
    encode_sig = (fun uu____80861  -> fun uu____80862  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____80868 =
             let uu____80875 = FStar_Options.peek ()  in (e, g, uu____80875)
              in
           [uu____80868]);
    solve = (fun uu____80891  -> fun uu____80892  -> fun uu____80893  -> ());
    finish = (fun uu____80900  -> ());
    refresh = (fun uu____80902  -> ())
  } 