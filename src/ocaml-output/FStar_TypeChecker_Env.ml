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
    match projectee with | Beta  -> true | uu____56010 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56021 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56032 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56044 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56063 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56074 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56085 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____56096 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____56107 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____56118 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____56130 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56152 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56180 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56208 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____56233 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____56244 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____56255 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____56266 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____56277 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56288 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____56299 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____56310 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____56321 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____56332 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____56343 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56354 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____56365 -> false
  
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
      | uu____56425 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____56451 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____56462 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____56473 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____56485 -> false
  
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
           (fun uu___446_67747  ->
              match uu___446_67747 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____67750 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____67750  in
                  let uu____67751 =
                    let uu____67752 = FStar_Syntax_Subst.compress y  in
                    uu____67752.FStar_Syntax_Syntax.n  in
                  (match uu____67751 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____67756 =
                         let uu___775_67757 = y1  in
                         let uu____67758 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_67757.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_67757.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____67758
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____67756
                   | uu____67761 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_67775 = env  in
      let uu____67776 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_67775.solver);
        range = (uu___781_67775.range);
        curmodule = (uu___781_67775.curmodule);
        gamma = uu____67776;
        gamma_sig = (uu___781_67775.gamma_sig);
        gamma_cache = (uu___781_67775.gamma_cache);
        modules = (uu___781_67775.modules);
        expected_typ = (uu___781_67775.expected_typ);
        sigtab = (uu___781_67775.sigtab);
        attrtab = (uu___781_67775.attrtab);
        is_pattern = (uu___781_67775.is_pattern);
        instantiate_imp = (uu___781_67775.instantiate_imp);
        effects = (uu___781_67775.effects);
        generalize = (uu___781_67775.generalize);
        letrecs = (uu___781_67775.letrecs);
        top_level = (uu___781_67775.top_level);
        check_uvars = (uu___781_67775.check_uvars);
        use_eq = (uu___781_67775.use_eq);
        is_iface = (uu___781_67775.is_iface);
        admit = (uu___781_67775.admit);
        lax = (uu___781_67775.lax);
        lax_universes = (uu___781_67775.lax_universes);
        phase1 = (uu___781_67775.phase1);
        failhard = (uu___781_67775.failhard);
        nosynth = (uu___781_67775.nosynth);
        uvar_subtyping = (uu___781_67775.uvar_subtyping);
        tc_term = (uu___781_67775.tc_term);
        type_of = (uu___781_67775.type_of);
        universe_of = (uu___781_67775.universe_of);
        check_type_of = (uu___781_67775.check_type_of);
        use_bv_sorts = (uu___781_67775.use_bv_sorts);
        qtbl_name_and_index = (uu___781_67775.qtbl_name_and_index);
        normalized_eff_names = (uu___781_67775.normalized_eff_names);
        fv_delta_depths = (uu___781_67775.fv_delta_depths);
        proof_ns = (uu___781_67775.proof_ns);
        synth_hook = (uu___781_67775.synth_hook);
        splice = (uu___781_67775.splice);
        postprocess = (uu___781_67775.postprocess);
        is_native_tactic = (uu___781_67775.is_native_tactic);
        identifier_info = (uu___781_67775.identifier_info);
        tc_hooks = (uu___781_67775.tc_hooks);
        dsenv = (uu___781_67775.dsenv);
        nbe = (uu___781_67775.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____67784  -> fun uu____67785  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_67807 = env  in
      {
        solver = (uu___788_67807.solver);
        range = (uu___788_67807.range);
        curmodule = (uu___788_67807.curmodule);
        gamma = (uu___788_67807.gamma);
        gamma_sig = (uu___788_67807.gamma_sig);
        gamma_cache = (uu___788_67807.gamma_cache);
        modules = (uu___788_67807.modules);
        expected_typ = (uu___788_67807.expected_typ);
        sigtab = (uu___788_67807.sigtab);
        attrtab = (uu___788_67807.attrtab);
        is_pattern = (uu___788_67807.is_pattern);
        instantiate_imp = (uu___788_67807.instantiate_imp);
        effects = (uu___788_67807.effects);
        generalize = (uu___788_67807.generalize);
        letrecs = (uu___788_67807.letrecs);
        top_level = (uu___788_67807.top_level);
        check_uvars = (uu___788_67807.check_uvars);
        use_eq = (uu___788_67807.use_eq);
        is_iface = (uu___788_67807.is_iface);
        admit = (uu___788_67807.admit);
        lax = (uu___788_67807.lax);
        lax_universes = (uu___788_67807.lax_universes);
        phase1 = (uu___788_67807.phase1);
        failhard = (uu___788_67807.failhard);
        nosynth = (uu___788_67807.nosynth);
        uvar_subtyping = (uu___788_67807.uvar_subtyping);
        tc_term = (uu___788_67807.tc_term);
        type_of = (uu___788_67807.type_of);
        universe_of = (uu___788_67807.universe_of);
        check_type_of = (uu___788_67807.check_type_of);
        use_bv_sorts = (uu___788_67807.use_bv_sorts);
        qtbl_name_and_index = (uu___788_67807.qtbl_name_and_index);
        normalized_eff_names = (uu___788_67807.normalized_eff_names);
        fv_delta_depths = (uu___788_67807.fv_delta_depths);
        proof_ns = (uu___788_67807.proof_ns);
        synth_hook = (uu___788_67807.synth_hook);
        splice = (uu___788_67807.splice);
        postprocess = (uu___788_67807.postprocess);
        is_native_tactic = (uu___788_67807.is_native_tactic);
        identifier_info = (uu___788_67807.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_67807.dsenv);
        nbe = (uu___788_67807.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_67819 = e  in
      let uu____67820 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_67819.solver);
        range = (uu___792_67819.range);
        curmodule = (uu___792_67819.curmodule);
        gamma = (uu___792_67819.gamma);
        gamma_sig = (uu___792_67819.gamma_sig);
        gamma_cache = (uu___792_67819.gamma_cache);
        modules = (uu___792_67819.modules);
        expected_typ = (uu___792_67819.expected_typ);
        sigtab = (uu___792_67819.sigtab);
        attrtab = (uu___792_67819.attrtab);
        is_pattern = (uu___792_67819.is_pattern);
        instantiate_imp = (uu___792_67819.instantiate_imp);
        effects = (uu___792_67819.effects);
        generalize = (uu___792_67819.generalize);
        letrecs = (uu___792_67819.letrecs);
        top_level = (uu___792_67819.top_level);
        check_uvars = (uu___792_67819.check_uvars);
        use_eq = (uu___792_67819.use_eq);
        is_iface = (uu___792_67819.is_iface);
        admit = (uu___792_67819.admit);
        lax = (uu___792_67819.lax);
        lax_universes = (uu___792_67819.lax_universes);
        phase1 = (uu___792_67819.phase1);
        failhard = (uu___792_67819.failhard);
        nosynth = (uu___792_67819.nosynth);
        uvar_subtyping = (uu___792_67819.uvar_subtyping);
        tc_term = (uu___792_67819.tc_term);
        type_of = (uu___792_67819.type_of);
        universe_of = (uu___792_67819.universe_of);
        check_type_of = (uu___792_67819.check_type_of);
        use_bv_sorts = (uu___792_67819.use_bv_sorts);
        qtbl_name_and_index = (uu___792_67819.qtbl_name_and_index);
        normalized_eff_names = (uu___792_67819.normalized_eff_names);
        fv_delta_depths = (uu___792_67819.fv_delta_depths);
        proof_ns = (uu___792_67819.proof_ns);
        synth_hook = (uu___792_67819.synth_hook);
        splice = (uu___792_67819.splice);
        postprocess = (uu___792_67819.postprocess);
        is_native_tactic = (uu___792_67819.is_native_tactic);
        identifier_info = (uu___792_67819.identifier_info);
        tc_hooks = (uu___792_67819.tc_hooks);
        dsenv = uu____67820;
        nbe = (uu___792_67819.nbe)
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
      | (NoDelta ,uu____67849) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____67852,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____67854,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____67857 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____67871 . unit -> 'Auu____67871 FStar_Util.smap =
  fun uu____67878  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____67884 . unit -> 'Auu____67884 FStar_Util.smap =
  fun uu____67891  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____68029 = new_gamma_cache ()  in
                  let uu____68032 = new_sigtab ()  in
                  let uu____68035 = new_sigtab ()  in
                  let uu____68042 =
                    let uu____68057 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____68057, FStar_Pervasives_Native.None)  in
                  let uu____68078 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____68082 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____68086 = FStar_Options.using_facts_from ()  in
                  let uu____68087 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____68090 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____68029;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____68032;
                    attrtab = uu____68035;
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
                    qtbl_name_and_index = uu____68042;
                    normalized_eff_names = uu____68078;
                    fv_delta_depths = uu____68082;
                    proof_ns = uu____68086;
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
                    is_native_tactic = (fun uu____68152  -> false);
                    identifier_info = uu____68087;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____68090;
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
  fun uu____68264  ->
    let uu____68265 = FStar_ST.op_Bang query_indices  in
    match uu____68265 with
    | [] -> failwith "Empty query indices!"
    | uu____68320 ->
        let uu____68330 =
          let uu____68340 =
            let uu____68348 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____68348  in
          let uu____68402 = FStar_ST.op_Bang query_indices  in uu____68340 ::
            uu____68402
           in
        FStar_ST.op_Colon_Equals query_indices uu____68330
  
let (pop_query_indices : unit -> unit) =
  fun uu____68498  ->
    let uu____68499 = FStar_ST.op_Bang query_indices  in
    match uu____68499 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____68626  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____68663  ->
    match uu____68663 with
    | (l,n1) ->
        let uu____68673 = FStar_ST.op_Bang query_indices  in
        (match uu____68673 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____68795 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____68818  ->
    let uu____68819 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____68819
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____68898 =
       let uu____68901 = FStar_ST.op_Bang stack  in env :: uu____68901  in
     FStar_ST.op_Colon_Equals stack uu____68898);
    (let uu___860_68950 = env  in
     let uu____68951 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____68954 = FStar_Util.smap_copy (sigtab env)  in
     let uu____68957 = FStar_Util.smap_copy (attrtab env)  in
     let uu____68964 =
       let uu____68979 =
         let uu____68983 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____68983  in
       let uu____69015 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____68979, uu____69015)  in
     let uu____69064 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____69067 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____69070 =
       let uu____69073 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____69073  in
     {
       solver = (uu___860_68950.solver);
       range = (uu___860_68950.range);
       curmodule = (uu___860_68950.curmodule);
       gamma = (uu___860_68950.gamma);
       gamma_sig = (uu___860_68950.gamma_sig);
       gamma_cache = uu____68951;
       modules = (uu___860_68950.modules);
       expected_typ = (uu___860_68950.expected_typ);
       sigtab = uu____68954;
       attrtab = uu____68957;
       is_pattern = (uu___860_68950.is_pattern);
       instantiate_imp = (uu___860_68950.instantiate_imp);
       effects = (uu___860_68950.effects);
       generalize = (uu___860_68950.generalize);
       letrecs = (uu___860_68950.letrecs);
       top_level = (uu___860_68950.top_level);
       check_uvars = (uu___860_68950.check_uvars);
       use_eq = (uu___860_68950.use_eq);
       is_iface = (uu___860_68950.is_iface);
       admit = (uu___860_68950.admit);
       lax = (uu___860_68950.lax);
       lax_universes = (uu___860_68950.lax_universes);
       phase1 = (uu___860_68950.phase1);
       failhard = (uu___860_68950.failhard);
       nosynth = (uu___860_68950.nosynth);
       uvar_subtyping = (uu___860_68950.uvar_subtyping);
       tc_term = (uu___860_68950.tc_term);
       type_of = (uu___860_68950.type_of);
       universe_of = (uu___860_68950.universe_of);
       check_type_of = (uu___860_68950.check_type_of);
       use_bv_sorts = (uu___860_68950.use_bv_sorts);
       qtbl_name_and_index = uu____68964;
       normalized_eff_names = uu____69064;
       fv_delta_depths = uu____69067;
       proof_ns = (uu___860_68950.proof_ns);
       synth_hook = (uu___860_68950.synth_hook);
       splice = (uu___860_68950.splice);
       postprocess = (uu___860_68950.postprocess);
       is_native_tactic = (uu___860_68950.is_native_tactic);
       identifier_info = uu____69070;
       tc_hooks = (uu___860_68950.tc_hooks);
       dsenv = (uu___860_68950.dsenv);
       nbe = (uu___860_68950.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____69120  ->
    let uu____69121 = FStar_ST.op_Bang stack  in
    match uu____69121 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____69175 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____69265  ->
           let uu____69266 = snapshot_stack env  in
           match uu____69266 with
           | (stack_depth,env1) ->
               let uu____69300 = snapshot_query_indices ()  in
               (match uu____69300 with
                | (query_indices_depth,()) ->
                    let uu____69333 = (env1.solver).snapshot msg  in
                    (match uu____69333 with
                     | (solver_depth,()) ->
                         let uu____69390 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____69390 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_69457 = env1  in
                                 {
                                   solver = (uu___885_69457.solver);
                                   range = (uu___885_69457.range);
                                   curmodule = (uu___885_69457.curmodule);
                                   gamma = (uu___885_69457.gamma);
                                   gamma_sig = (uu___885_69457.gamma_sig);
                                   gamma_cache = (uu___885_69457.gamma_cache);
                                   modules = (uu___885_69457.modules);
                                   expected_typ =
                                     (uu___885_69457.expected_typ);
                                   sigtab = (uu___885_69457.sigtab);
                                   attrtab = (uu___885_69457.attrtab);
                                   is_pattern = (uu___885_69457.is_pattern);
                                   instantiate_imp =
                                     (uu___885_69457.instantiate_imp);
                                   effects = (uu___885_69457.effects);
                                   generalize = (uu___885_69457.generalize);
                                   letrecs = (uu___885_69457.letrecs);
                                   top_level = (uu___885_69457.top_level);
                                   check_uvars = (uu___885_69457.check_uvars);
                                   use_eq = (uu___885_69457.use_eq);
                                   is_iface = (uu___885_69457.is_iface);
                                   admit = (uu___885_69457.admit);
                                   lax = (uu___885_69457.lax);
                                   lax_universes =
                                     (uu___885_69457.lax_universes);
                                   phase1 = (uu___885_69457.phase1);
                                   failhard = (uu___885_69457.failhard);
                                   nosynth = (uu___885_69457.nosynth);
                                   uvar_subtyping =
                                     (uu___885_69457.uvar_subtyping);
                                   tc_term = (uu___885_69457.tc_term);
                                   type_of = (uu___885_69457.type_of);
                                   universe_of = (uu___885_69457.universe_of);
                                   check_type_of =
                                     (uu___885_69457.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_69457.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_69457.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_69457.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_69457.fv_delta_depths);
                                   proof_ns = (uu___885_69457.proof_ns);
                                   synth_hook = (uu___885_69457.synth_hook);
                                   splice = (uu___885_69457.splice);
                                   postprocess = (uu___885_69457.postprocess);
                                   is_native_tactic =
                                     (uu___885_69457.is_native_tactic);
                                   identifier_info =
                                     (uu___885_69457.identifier_info);
                                   tc_hooks = (uu___885_69457.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_69457.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____69491  ->
             let uu____69492 =
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
             match uu____69492 with
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
                             ((let uu____69672 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____69672
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____69688 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____69688
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____69720,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____69762 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____69792  ->
                  match uu____69792 with
                  | (m,uu____69800) -> FStar_Ident.lid_equals l m))
           in
        (match uu____69762 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_69815 = env  in
               {
                 solver = (uu___930_69815.solver);
                 range = (uu___930_69815.range);
                 curmodule = (uu___930_69815.curmodule);
                 gamma = (uu___930_69815.gamma);
                 gamma_sig = (uu___930_69815.gamma_sig);
                 gamma_cache = (uu___930_69815.gamma_cache);
                 modules = (uu___930_69815.modules);
                 expected_typ = (uu___930_69815.expected_typ);
                 sigtab = (uu___930_69815.sigtab);
                 attrtab = (uu___930_69815.attrtab);
                 is_pattern = (uu___930_69815.is_pattern);
                 instantiate_imp = (uu___930_69815.instantiate_imp);
                 effects = (uu___930_69815.effects);
                 generalize = (uu___930_69815.generalize);
                 letrecs = (uu___930_69815.letrecs);
                 top_level = (uu___930_69815.top_level);
                 check_uvars = (uu___930_69815.check_uvars);
                 use_eq = (uu___930_69815.use_eq);
                 is_iface = (uu___930_69815.is_iface);
                 admit = (uu___930_69815.admit);
                 lax = (uu___930_69815.lax);
                 lax_universes = (uu___930_69815.lax_universes);
                 phase1 = (uu___930_69815.phase1);
                 failhard = (uu___930_69815.failhard);
                 nosynth = (uu___930_69815.nosynth);
                 uvar_subtyping = (uu___930_69815.uvar_subtyping);
                 tc_term = (uu___930_69815.tc_term);
                 type_of = (uu___930_69815.type_of);
                 universe_of = (uu___930_69815.universe_of);
                 check_type_of = (uu___930_69815.check_type_of);
                 use_bv_sorts = (uu___930_69815.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_69815.normalized_eff_names);
                 fv_delta_depths = (uu___930_69815.fv_delta_depths);
                 proof_ns = (uu___930_69815.proof_ns);
                 synth_hook = (uu___930_69815.synth_hook);
                 splice = (uu___930_69815.splice);
                 postprocess = (uu___930_69815.postprocess);
                 is_native_tactic = (uu___930_69815.is_native_tactic);
                 identifier_info = (uu___930_69815.identifier_info);
                 tc_hooks = (uu___930_69815.tc_hooks);
                 dsenv = (uu___930_69815.dsenv);
                 nbe = (uu___930_69815.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____69832,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_69848 = env  in
               {
                 solver = (uu___939_69848.solver);
                 range = (uu___939_69848.range);
                 curmodule = (uu___939_69848.curmodule);
                 gamma = (uu___939_69848.gamma);
                 gamma_sig = (uu___939_69848.gamma_sig);
                 gamma_cache = (uu___939_69848.gamma_cache);
                 modules = (uu___939_69848.modules);
                 expected_typ = (uu___939_69848.expected_typ);
                 sigtab = (uu___939_69848.sigtab);
                 attrtab = (uu___939_69848.attrtab);
                 is_pattern = (uu___939_69848.is_pattern);
                 instantiate_imp = (uu___939_69848.instantiate_imp);
                 effects = (uu___939_69848.effects);
                 generalize = (uu___939_69848.generalize);
                 letrecs = (uu___939_69848.letrecs);
                 top_level = (uu___939_69848.top_level);
                 check_uvars = (uu___939_69848.check_uvars);
                 use_eq = (uu___939_69848.use_eq);
                 is_iface = (uu___939_69848.is_iface);
                 admit = (uu___939_69848.admit);
                 lax = (uu___939_69848.lax);
                 lax_universes = (uu___939_69848.lax_universes);
                 phase1 = (uu___939_69848.phase1);
                 failhard = (uu___939_69848.failhard);
                 nosynth = (uu___939_69848.nosynth);
                 uvar_subtyping = (uu___939_69848.uvar_subtyping);
                 tc_term = (uu___939_69848.tc_term);
                 type_of = (uu___939_69848.type_of);
                 universe_of = (uu___939_69848.universe_of);
                 check_type_of = (uu___939_69848.check_type_of);
                 use_bv_sorts = (uu___939_69848.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_69848.normalized_eff_names);
                 fv_delta_depths = (uu___939_69848.fv_delta_depths);
                 proof_ns = (uu___939_69848.proof_ns);
                 synth_hook = (uu___939_69848.synth_hook);
                 splice = (uu___939_69848.splice);
                 postprocess = (uu___939_69848.postprocess);
                 is_native_tactic = (uu___939_69848.is_native_tactic);
                 identifier_info = (uu___939_69848.identifier_info);
                 tc_hooks = (uu___939_69848.tc_hooks);
                 dsenv = (uu___939_69848.dsenv);
                 nbe = (uu___939_69848.nbe)
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
        (let uu___946_69891 = e  in
         {
           solver = (uu___946_69891.solver);
           range = r;
           curmodule = (uu___946_69891.curmodule);
           gamma = (uu___946_69891.gamma);
           gamma_sig = (uu___946_69891.gamma_sig);
           gamma_cache = (uu___946_69891.gamma_cache);
           modules = (uu___946_69891.modules);
           expected_typ = (uu___946_69891.expected_typ);
           sigtab = (uu___946_69891.sigtab);
           attrtab = (uu___946_69891.attrtab);
           is_pattern = (uu___946_69891.is_pattern);
           instantiate_imp = (uu___946_69891.instantiate_imp);
           effects = (uu___946_69891.effects);
           generalize = (uu___946_69891.generalize);
           letrecs = (uu___946_69891.letrecs);
           top_level = (uu___946_69891.top_level);
           check_uvars = (uu___946_69891.check_uvars);
           use_eq = (uu___946_69891.use_eq);
           is_iface = (uu___946_69891.is_iface);
           admit = (uu___946_69891.admit);
           lax = (uu___946_69891.lax);
           lax_universes = (uu___946_69891.lax_universes);
           phase1 = (uu___946_69891.phase1);
           failhard = (uu___946_69891.failhard);
           nosynth = (uu___946_69891.nosynth);
           uvar_subtyping = (uu___946_69891.uvar_subtyping);
           tc_term = (uu___946_69891.tc_term);
           type_of = (uu___946_69891.type_of);
           universe_of = (uu___946_69891.universe_of);
           check_type_of = (uu___946_69891.check_type_of);
           use_bv_sorts = (uu___946_69891.use_bv_sorts);
           qtbl_name_and_index = (uu___946_69891.qtbl_name_and_index);
           normalized_eff_names = (uu___946_69891.normalized_eff_names);
           fv_delta_depths = (uu___946_69891.fv_delta_depths);
           proof_ns = (uu___946_69891.proof_ns);
           synth_hook = (uu___946_69891.synth_hook);
           splice = (uu___946_69891.splice);
           postprocess = (uu___946_69891.postprocess);
           is_native_tactic = (uu___946_69891.is_native_tactic);
           identifier_info = (uu___946_69891.identifier_info);
           tc_hooks = (uu___946_69891.tc_hooks);
           dsenv = (uu___946_69891.dsenv);
           nbe = (uu___946_69891.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____69911 =
        let uu____69912 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____69912 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____69911
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____69967 =
          let uu____69968 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____69968 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____69967
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____70023 =
          let uu____70024 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____70024 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70023
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____70079 =
        let uu____70080 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____70080 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____70079
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_70144 = env  in
      {
        solver = (uu___963_70144.solver);
        range = (uu___963_70144.range);
        curmodule = lid;
        gamma = (uu___963_70144.gamma);
        gamma_sig = (uu___963_70144.gamma_sig);
        gamma_cache = (uu___963_70144.gamma_cache);
        modules = (uu___963_70144.modules);
        expected_typ = (uu___963_70144.expected_typ);
        sigtab = (uu___963_70144.sigtab);
        attrtab = (uu___963_70144.attrtab);
        is_pattern = (uu___963_70144.is_pattern);
        instantiate_imp = (uu___963_70144.instantiate_imp);
        effects = (uu___963_70144.effects);
        generalize = (uu___963_70144.generalize);
        letrecs = (uu___963_70144.letrecs);
        top_level = (uu___963_70144.top_level);
        check_uvars = (uu___963_70144.check_uvars);
        use_eq = (uu___963_70144.use_eq);
        is_iface = (uu___963_70144.is_iface);
        admit = (uu___963_70144.admit);
        lax = (uu___963_70144.lax);
        lax_universes = (uu___963_70144.lax_universes);
        phase1 = (uu___963_70144.phase1);
        failhard = (uu___963_70144.failhard);
        nosynth = (uu___963_70144.nosynth);
        uvar_subtyping = (uu___963_70144.uvar_subtyping);
        tc_term = (uu___963_70144.tc_term);
        type_of = (uu___963_70144.type_of);
        universe_of = (uu___963_70144.universe_of);
        check_type_of = (uu___963_70144.check_type_of);
        use_bv_sorts = (uu___963_70144.use_bv_sorts);
        qtbl_name_and_index = (uu___963_70144.qtbl_name_and_index);
        normalized_eff_names = (uu___963_70144.normalized_eff_names);
        fv_delta_depths = (uu___963_70144.fv_delta_depths);
        proof_ns = (uu___963_70144.proof_ns);
        synth_hook = (uu___963_70144.synth_hook);
        splice = (uu___963_70144.splice);
        postprocess = (uu___963_70144.postprocess);
        is_native_tactic = (uu___963_70144.is_native_tactic);
        identifier_info = (uu___963_70144.identifier_info);
        tc_hooks = (uu___963_70144.tc_hooks);
        dsenv = (uu___963_70144.dsenv);
        nbe = (uu___963_70144.nbe)
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
      let uu____70175 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____70175
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____70188 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____70188)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____70203 =
      let uu____70205 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____70205  in
    (FStar_Errors.Fatal_VariableNotFound, uu____70203)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____70214  ->
    let uu____70215 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____70215
  
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
      | ((formals,t),uu____70315) ->
          let vs = mk_univ_subst formals us  in
          let uu____70339 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____70339)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_70356  ->
    match uu___447_70356 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____70382  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____70402 = inst_tscheme t  in
      match uu____70402 with
      | (us,t1) ->
          let uu____70413 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____70413)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____70434  ->
          match uu____70434 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____70456 =
                         let uu____70458 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____70462 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____70466 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____70468 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____70458 uu____70462 uu____70466 uu____70468
                          in
                       failwith uu____70456)
                    else ();
                    (let uu____70473 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____70473))
               | uu____70482 ->
                   let uu____70483 =
                     let uu____70485 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____70485
                      in
                   failwith uu____70483)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____70497 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____70508 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____70519 -> false
  
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
             | ([],uu____70567) -> Maybe
             | (uu____70574,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____70594 -> No  in
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
          let uu____70688 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____70688 with
          | FStar_Pervasives_Native.None  ->
              let uu____70711 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_70755  ->
                     match uu___448_70755 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____70794 = FStar_Ident.lid_equals lid l  in
                         if uu____70794
                         then
                           let uu____70817 =
                             let uu____70836 =
                               let uu____70851 = inst_tscheme t  in
                               FStar_Util.Inl uu____70851  in
                             let uu____70866 = FStar_Ident.range_of_lid l  in
                             (uu____70836, uu____70866)  in
                           FStar_Pervasives_Native.Some uu____70817
                         else FStar_Pervasives_Native.None
                     | uu____70919 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____70711
                (fun uu____70957  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_70966  ->
                        match uu___449_70966 with
                        | (uu____70969,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____70971);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____70972;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____70973;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____70974;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____70975;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____70995 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____70995
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
                                  uu____71047 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____71054 -> cache t  in
                            let uu____71055 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____71055 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____71061 =
                                   let uu____71062 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____71062)
                                    in
                                 maybe_cache uu____71061)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____71133 = find_in_sigtab env lid  in
         match uu____71133 with
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
      let uu____71214 = lookup_qname env lid  in
      match uu____71214 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____71235,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____71349 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____71349 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____71394 =
          let uu____71397 = lookup_attr env1 attr  in se1 :: uu____71397  in
        FStar_Util.smap_add (attrtab env1) attr uu____71394  in
      FStar_List.iter
        (fun attr  ->
           let uu____71407 =
             let uu____71408 = FStar_Syntax_Subst.compress attr  in
             uu____71408.FStar_Syntax_Syntax.n  in
           match uu____71407 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____71412 =
                 let uu____71414 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____71414.FStar_Ident.str  in
               add_one1 env se uu____71412
           | uu____71415 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____71438) ->
          add_sigelts env ses
      | uu____71447 ->
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
            | uu____71462 -> ()))

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
        (fun uu___450_71494  ->
           match uu___450_71494 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____71512 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____71574,lb::[]),uu____71576) ->
            let uu____71585 =
              let uu____71594 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____71603 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____71594, uu____71603)  in
            FStar_Pervasives_Native.Some uu____71585
        | FStar_Syntax_Syntax.Sig_let ((uu____71616,lbs),uu____71618) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____71650 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____71663 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____71663
                     then
                       let uu____71676 =
                         let uu____71685 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____71694 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____71685, uu____71694)  in
                       FStar_Pervasives_Native.Some uu____71676
                     else FStar_Pervasives_Native.None)
        | uu____71717 -> FStar_Pervasives_Native.None
  
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
          let uu____71777 =
            let uu____71786 =
              let uu____71791 =
                let uu____71792 =
                  let uu____71795 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____71795
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____71792)  in
              inst_tscheme1 uu____71791  in
            (uu____71786, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71777
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____71817,uu____71818) ->
          let uu____71823 =
            let uu____71832 =
              let uu____71837 =
                let uu____71838 =
                  let uu____71841 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____71841  in
                (us, uu____71838)  in
              inst_tscheme1 uu____71837  in
            (uu____71832, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71823
      | uu____71860 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____71949 =
          match uu____71949 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____72045,uvs,t,uu____72048,uu____72049,uu____72050);
                      FStar_Syntax_Syntax.sigrng = uu____72051;
                      FStar_Syntax_Syntax.sigquals = uu____72052;
                      FStar_Syntax_Syntax.sigmeta = uu____72053;
                      FStar_Syntax_Syntax.sigattrs = uu____72054;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72077 =
                     let uu____72086 = inst_tscheme1 (uvs, t)  in
                     (uu____72086, rng)  in
                   FStar_Pervasives_Native.Some uu____72077
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____72110;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____72112;
                      FStar_Syntax_Syntax.sigattrs = uu____72113;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72130 =
                     let uu____72132 = in_cur_mod env l  in uu____72132 = Yes
                      in
                   if uu____72130
                   then
                     let uu____72144 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____72144
                      then
                        let uu____72160 =
                          let uu____72169 = inst_tscheme1 (uvs, t)  in
                          (uu____72169, rng)  in
                        FStar_Pervasives_Native.Some uu____72160
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____72202 =
                        let uu____72211 = inst_tscheme1 (uvs, t)  in
                        (uu____72211, rng)  in
                      FStar_Pervasives_Native.Some uu____72202)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72236,uu____72237);
                      FStar_Syntax_Syntax.sigrng = uu____72238;
                      FStar_Syntax_Syntax.sigquals = uu____72239;
                      FStar_Syntax_Syntax.sigmeta = uu____72240;
                      FStar_Syntax_Syntax.sigattrs = uu____72241;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____72282 =
                          let uu____72291 = inst_tscheme1 (uvs, k)  in
                          (uu____72291, rng)  in
                        FStar_Pervasives_Native.Some uu____72282
                    | uu____72312 ->
                        let uu____72313 =
                          let uu____72322 =
                            let uu____72327 =
                              let uu____72328 =
                                let uu____72331 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72331
                                 in
                              (uvs, uu____72328)  in
                            inst_tscheme1 uu____72327  in
                          (uu____72322, rng)  in
                        FStar_Pervasives_Native.Some uu____72313)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72354,uu____72355);
                      FStar_Syntax_Syntax.sigrng = uu____72356;
                      FStar_Syntax_Syntax.sigquals = uu____72357;
                      FStar_Syntax_Syntax.sigmeta = uu____72358;
                      FStar_Syntax_Syntax.sigattrs = uu____72359;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____72401 =
                          let uu____72410 = inst_tscheme_with (uvs, k) us  in
                          (uu____72410, rng)  in
                        FStar_Pervasives_Native.Some uu____72401
                    | uu____72431 ->
                        let uu____72432 =
                          let uu____72441 =
                            let uu____72446 =
                              let uu____72447 =
                                let uu____72450 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72450
                                 in
                              (uvs, uu____72447)  in
                            inst_tscheme_with uu____72446 us  in
                          (uu____72441, rng)  in
                        FStar_Pervasives_Native.Some uu____72432)
               | FStar_Util.Inr se ->
                   let uu____72486 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____72507;
                          FStar_Syntax_Syntax.sigrng = uu____72508;
                          FStar_Syntax_Syntax.sigquals = uu____72509;
                          FStar_Syntax_Syntax.sigmeta = uu____72510;
                          FStar_Syntax_Syntax.sigattrs = uu____72511;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____72526 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____72486
                     (FStar_Util.map_option
                        (fun uu____72574  ->
                           match uu____72574 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____72605 =
          let uu____72616 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____72616 mapper  in
        match uu____72605 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____72690 =
              let uu____72701 =
                let uu____72708 =
                  let uu___1290_72711 = t  in
                  let uu____72712 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_72711.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____72712;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_72711.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____72708)  in
              (uu____72701, r)  in
            FStar_Pervasives_Native.Some uu____72690
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____72761 = lookup_qname env l  in
      match uu____72761 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____72782 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____72836 = try_lookup_bv env bv  in
      match uu____72836 with
      | FStar_Pervasives_Native.None  ->
          let uu____72851 = variable_not_found bv  in
          FStar_Errors.raise_error uu____72851 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____72867 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____72868 =
            let uu____72869 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____72869  in
          (uu____72867, uu____72868)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____72891 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____72891 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____72957 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____72957  in
          let uu____72958 =
            let uu____72967 =
              let uu____72972 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____72972)  in
            (uu____72967, r1)  in
          FStar_Pervasives_Native.Some uu____72958
  
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
        let uu____73007 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____73007 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____73040,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____73065 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____73065  in
            let uu____73066 =
              let uu____73071 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____73071, r1)  in
            FStar_Pervasives_Native.Some uu____73066
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____73095 = try_lookup_lid env l  in
      match uu____73095 with
      | FStar_Pervasives_Native.None  ->
          let uu____73122 = name_not_found l  in
          let uu____73128 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____73122 uu____73128
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_73171  ->
              match uu___451_73171 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____73175 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____73196 = lookup_qname env lid  in
      match uu____73196 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73205,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73208;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73210;
              FStar_Syntax_Syntax.sigattrs = uu____73211;_},FStar_Pervasives_Native.None
            ),uu____73212)
          ->
          let uu____73261 =
            let uu____73268 =
              let uu____73269 =
                let uu____73272 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____73272 t  in
              (uvs, uu____73269)  in
            (uu____73268, q)  in
          FStar_Pervasives_Native.Some uu____73261
      | uu____73285 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73307 = lookup_qname env lid  in
      match uu____73307 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73312,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73315;
              FStar_Syntax_Syntax.sigquals = uu____73316;
              FStar_Syntax_Syntax.sigmeta = uu____73317;
              FStar_Syntax_Syntax.sigattrs = uu____73318;_},FStar_Pervasives_Native.None
            ),uu____73319)
          ->
          let uu____73368 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73368 (uvs, t)
      | uu____73373 ->
          let uu____73374 = name_not_found lid  in
          let uu____73380 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73374 uu____73380
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73400 = lookup_qname env lid  in
      match uu____73400 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73405,uvs,t,uu____73408,uu____73409,uu____73410);
              FStar_Syntax_Syntax.sigrng = uu____73411;
              FStar_Syntax_Syntax.sigquals = uu____73412;
              FStar_Syntax_Syntax.sigmeta = uu____73413;
              FStar_Syntax_Syntax.sigattrs = uu____73414;_},FStar_Pervasives_Native.None
            ),uu____73415)
          ->
          let uu____73470 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73470 (uvs, t)
      | uu____73475 ->
          let uu____73476 = name_not_found lid  in
          let uu____73482 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73476 uu____73482
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____73505 = lookup_qname env lid  in
      match uu____73505 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____73513,uu____73514,uu____73515,uu____73516,uu____73517,dcs);
              FStar_Syntax_Syntax.sigrng = uu____73519;
              FStar_Syntax_Syntax.sigquals = uu____73520;
              FStar_Syntax_Syntax.sigmeta = uu____73521;
              FStar_Syntax_Syntax.sigattrs = uu____73522;_},uu____73523),uu____73524)
          -> (true, dcs)
      | uu____73587 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____73603 = lookup_qname env lid  in
      match uu____73603 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73604,uu____73605,uu____73606,l,uu____73608,uu____73609);
              FStar_Syntax_Syntax.sigrng = uu____73610;
              FStar_Syntax_Syntax.sigquals = uu____73611;
              FStar_Syntax_Syntax.sigmeta = uu____73612;
              FStar_Syntax_Syntax.sigattrs = uu____73613;_},uu____73614),uu____73615)
          -> l
      | uu____73672 ->
          let uu____73673 =
            let uu____73675 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____73675  in
          failwith uu____73673
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____73745)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____73802) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____73826 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____73826
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____73861 -> FStar_Pervasives_Native.None)
          | uu____73870 -> FStar_Pervasives_Native.None
  
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
        let uu____73932 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____73932
  
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
        let uu____73965 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____73965
  
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
             (FStar_Util.Inl uu____74017,uu____74018) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____74067),uu____74068) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____74117 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____74135 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____74145 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____74162 ->
                  let uu____74169 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____74169
              | FStar_Syntax_Syntax.Sig_let ((uu____74170,lbs),uu____74172)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____74188 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____74188
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____74195 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____74203 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____74204 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____74211 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74212 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____74213 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74214 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____74227 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____74245 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____74245
           (fun d_opt  ->
              let uu____74258 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____74258
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____74268 =
                   let uu____74271 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____74271  in
                 match uu____74268 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____74272 =
                       let uu____74274 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____74274
                        in
                     failwith uu____74272
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____74279 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____74279
                       then
                         let uu____74282 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____74284 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____74286 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____74282 uu____74284 uu____74286
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
        (FStar_Util.Inr (se,uu____74311),uu____74312) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____74361 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____74383),uu____74384) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____74433 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____74455 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____74455
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____74478 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____74478 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____74502 =
                      let uu____74503 = FStar_Syntax_Util.un_uinst tm  in
                      uu____74503.FStar_Syntax_Syntax.n  in
                    match uu____74502 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____74508 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____74525 = lookup_qname env ftv  in
      match uu____74525 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____74529) ->
          let uu____74574 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____74574 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____74595,t),r) ->
               let uu____74610 =
                 let uu____74611 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____74611 t  in
               FStar_Pervasives_Native.Some uu____74610)
      | uu____74612 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____74624 = try_lookup_effect_lid env ftv  in
      match uu____74624 with
      | FStar_Pervasives_Native.None  ->
          let uu____74627 = name_not_found ftv  in
          let uu____74633 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____74627 uu____74633
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
        let uu____74657 = lookup_qname env lid0  in
        match uu____74657 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____74668);
                FStar_Syntax_Syntax.sigrng = uu____74669;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____74671;
                FStar_Syntax_Syntax.sigattrs = uu____74672;_},FStar_Pervasives_Native.None
              ),uu____74673)
            ->
            let lid1 =
              let uu____74727 =
                let uu____74728 = FStar_Ident.range_of_lid lid  in
                let uu____74729 =
                  let uu____74730 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____74730  in
                FStar_Range.set_use_range uu____74728 uu____74729  in
              FStar_Ident.set_lid_range lid uu____74727  in
            let uu____74731 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_74737  ->
                      match uu___452_74737 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____74740 -> false))
               in
            if uu____74731
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____74759 =
                      let uu____74761 =
                        let uu____74763 = get_range env  in
                        FStar_Range.string_of_range uu____74763  in
                      let uu____74764 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____74766 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____74761 uu____74764 uu____74766
                       in
                    failwith uu____74759)
                  in
               match (binders, univs1) with
               | ([],uu____74787) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____74813,uu____74814::uu____74815::uu____74816) ->
                   let uu____74837 =
                     let uu____74839 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____74841 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____74839 uu____74841
                      in
                   failwith uu____74837
               | uu____74852 ->
                   let uu____74867 =
                     let uu____74872 =
                       let uu____74873 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____74873)  in
                     inst_tscheme_with uu____74872 insts  in
                   (match uu____74867 with
                    | (uu____74886,t) ->
                        let t1 =
                          let uu____74889 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____74889 t  in
                        let uu____74890 =
                          let uu____74891 = FStar_Syntax_Subst.compress t1
                             in
                          uu____74891.FStar_Syntax_Syntax.n  in
                        (match uu____74890 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____74926 -> failwith "Impossible")))
        | uu____74934 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____74958 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____74958 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____74971,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____74978 = find1 l2  in
            (match uu____74978 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____74985 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____74985 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____74989 = find1 l  in
            (match uu____74989 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____74994 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____74994
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____75009 = lookup_qname env l1  in
      match uu____75009 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____75012;
              FStar_Syntax_Syntax.sigrng = uu____75013;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____75015;
              FStar_Syntax_Syntax.sigattrs = uu____75016;_},uu____75017),uu____75018)
          -> q
      | uu____75069 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____75093 =
          let uu____75094 =
            let uu____75096 = FStar_Util.string_of_int i  in
            let uu____75098 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____75096 uu____75098
             in
          failwith uu____75094  in
        let uu____75101 = lookup_datacon env lid  in
        match uu____75101 with
        | (uu____75106,t) ->
            let uu____75108 =
              let uu____75109 = FStar_Syntax_Subst.compress t  in
              uu____75109.FStar_Syntax_Syntax.n  in
            (match uu____75108 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75113) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____75157 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____75157
                      FStar_Pervasives_Native.fst)
             | uu____75168 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75182 = lookup_qname env l  in
      match uu____75182 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____75184,uu____75185,uu____75186);
              FStar_Syntax_Syntax.sigrng = uu____75187;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75189;
              FStar_Syntax_Syntax.sigattrs = uu____75190;_},uu____75191),uu____75192)
          ->
          FStar_Util.for_some
            (fun uu___453_75245  ->
               match uu___453_75245 with
               | FStar_Syntax_Syntax.Projector uu____75247 -> true
               | uu____75253 -> false) quals
      | uu____75255 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75269 = lookup_qname env lid  in
      match uu____75269 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____75271,uu____75272,uu____75273,uu____75274,uu____75275,uu____75276);
              FStar_Syntax_Syntax.sigrng = uu____75277;
              FStar_Syntax_Syntax.sigquals = uu____75278;
              FStar_Syntax_Syntax.sigmeta = uu____75279;
              FStar_Syntax_Syntax.sigattrs = uu____75280;_},uu____75281),uu____75282)
          -> true
      | uu____75340 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75354 = lookup_qname env lid  in
      match uu____75354 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75356,uu____75357,uu____75358,uu____75359,uu____75360,uu____75361);
              FStar_Syntax_Syntax.sigrng = uu____75362;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75364;
              FStar_Syntax_Syntax.sigattrs = uu____75365;_},uu____75366),uu____75367)
          ->
          FStar_Util.for_some
            (fun uu___454_75428  ->
               match uu___454_75428 with
               | FStar_Syntax_Syntax.RecordType uu____75430 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____75440 -> true
               | uu____75450 -> false) quals
      | uu____75452 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____75462,uu____75463);
            FStar_Syntax_Syntax.sigrng = uu____75464;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____75466;
            FStar_Syntax_Syntax.sigattrs = uu____75467;_},uu____75468),uu____75469)
        ->
        FStar_Util.for_some
          (fun uu___455_75526  ->
             match uu___455_75526 with
             | FStar_Syntax_Syntax.Action uu____75528 -> true
             | uu____75530 -> false) quals
    | uu____75532 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75546 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____75546
  
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
      let uu____75563 =
        let uu____75564 = FStar_Syntax_Util.un_uinst head1  in
        uu____75564.FStar_Syntax_Syntax.n  in
      match uu____75563 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75570 ->
               true
           | uu____75573 -> false)
      | uu____75575 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75589 = lookup_qname env l  in
      match uu____75589 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75592),uu____75593) ->
          FStar_Util.for_some
            (fun uu___456_75641  ->
               match uu___456_75641 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75644 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75646 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75722 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75740) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75758 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75766 ->
                 FStar_Pervasives_Native.Some true
             | uu____75785 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75788 =
        let uu____75792 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75792 mapper  in
      match uu____75788 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75852 = lookup_qname env lid  in
      match uu____75852 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75856,uu____75857,tps,uu____75859,uu____75860,uu____75861);
              FStar_Syntax_Syntax.sigrng = uu____75862;
              FStar_Syntax_Syntax.sigquals = uu____75863;
              FStar_Syntax_Syntax.sigmeta = uu____75864;
              FStar_Syntax_Syntax.sigattrs = uu____75865;_},uu____75866),uu____75867)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____75933 -> FStar_Pervasives_Native.None
  
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
           (fun uu____75979  ->
              match uu____75979 with
              | (d,uu____75988) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____76004 = effect_decl_opt env l  in
      match uu____76004 with
      | FStar_Pervasives_Native.None  ->
          let uu____76019 = name_not_found l  in
          let uu____76025 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76019 uu____76025
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76048  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76067  ->
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
        let uu____76099 = FStar_Ident.lid_equals l1 l2  in
        if uu____76099
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76110 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76110
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76121 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____76174  ->
                        match uu____76174 with
                        | (m1,m2,uu____76188,uu____76189,uu____76190) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76121 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76207 =
                    let uu____76213 =
                      let uu____76215 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____76217 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____76215
                        uu____76217
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____76213)
                     in
                  FStar_Errors.raise_error uu____76207 env.range
              | FStar_Pervasives_Native.Some
                  (uu____76227,uu____76228,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____76262 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____76262
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
  'Auu____76282 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____76282) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____76311 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____76337  ->
                match uu____76337 with
                | (d,uu____76344) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____76311 with
      | FStar_Pervasives_Native.None  ->
          let uu____76355 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____76355
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____76370 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____76370 with
           | (uu____76385,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____76403)::(wp,uu____76405)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____76461 -> failwith "Impossible"))
  
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
          let uu____76519 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____76519
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____76524 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____76524
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
                  let uu____76535 = get_range env  in
                  let uu____76536 =
                    let uu____76543 =
                      let uu____76544 =
                        let uu____76561 =
                          let uu____76572 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____76572]  in
                        (null_wp, uu____76561)  in
                      FStar_Syntax_Syntax.Tm_app uu____76544  in
                    FStar_Syntax_Syntax.mk uu____76543  in
                  uu____76536 FStar_Pervasives_Native.None uu____76535  in
                let uu____76612 =
                  let uu____76613 =
                    let uu____76624 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____76624]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____76613;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____76612))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1939_76662 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1939_76662.order);
              joins = (uu___1939_76662.joins)
            }  in
          let uu___1942_76671 = env  in
          {
            solver = (uu___1942_76671.solver);
            range = (uu___1942_76671.range);
            curmodule = (uu___1942_76671.curmodule);
            gamma = (uu___1942_76671.gamma);
            gamma_sig = (uu___1942_76671.gamma_sig);
            gamma_cache = (uu___1942_76671.gamma_cache);
            modules = (uu___1942_76671.modules);
            expected_typ = (uu___1942_76671.expected_typ);
            sigtab = (uu___1942_76671.sigtab);
            attrtab = (uu___1942_76671.attrtab);
            is_pattern = (uu___1942_76671.is_pattern);
            instantiate_imp = (uu___1942_76671.instantiate_imp);
            effects;
            generalize = (uu___1942_76671.generalize);
            letrecs = (uu___1942_76671.letrecs);
            top_level = (uu___1942_76671.top_level);
            check_uvars = (uu___1942_76671.check_uvars);
            use_eq = (uu___1942_76671.use_eq);
            is_iface = (uu___1942_76671.is_iface);
            admit = (uu___1942_76671.admit);
            lax = (uu___1942_76671.lax);
            lax_universes = (uu___1942_76671.lax_universes);
            phase1 = (uu___1942_76671.phase1);
            failhard = (uu___1942_76671.failhard);
            nosynth = (uu___1942_76671.nosynth);
            uvar_subtyping = (uu___1942_76671.uvar_subtyping);
            tc_term = (uu___1942_76671.tc_term);
            type_of = (uu___1942_76671.type_of);
            universe_of = (uu___1942_76671.universe_of);
            check_type_of = (uu___1942_76671.check_type_of);
            use_bv_sorts = (uu___1942_76671.use_bv_sorts);
            qtbl_name_and_index = (uu___1942_76671.qtbl_name_and_index);
            normalized_eff_names = (uu___1942_76671.normalized_eff_names);
            fv_delta_depths = (uu___1942_76671.fv_delta_depths);
            proof_ns = (uu___1942_76671.proof_ns);
            synth_hook = (uu___1942_76671.synth_hook);
            splice = (uu___1942_76671.splice);
            postprocess = (uu___1942_76671.postprocess);
            is_native_tactic = (uu___1942_76671.is_native_tactic);
            identifier_info = (uu___1942_76671.identifier_info);
            tc_hooks = (uu___1942_76671.tc_hooks);
            dsenv = (uu___1942_76671.dsenv);
            nbe = (uu___1942_76671.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____76701 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____76701  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____76859 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____76860 = l1 u t wp e  in
                                l2 u t uu____76859 uu____76860))
                | uu____76861 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____76933 = inst_tscheme_with lift_t [u]  in
            match uu____76933 with
            | (uu____76940,lift_t1) ->
                let uu____76942 =
                  let uu____76949 =
                    let uu____76950 =
                      let uu____76967 =
                        let uu____76978 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____76987 =
                          let uu____76998 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____76998]  in
                        uu____76978 :: uu____76987  in
                      (lift_t1, uu____76967)  in
                    FStar_Syntax_Syntax.Tm_app uu____76950  in
                  FStar_Syntax_Syntax.mk uu____76949  in
                uu____76942 FStar_Pervasives_Native.None
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
            let uu____77111 = inst_tscheme_with lift_t [u]  in
            match uu____77111 with
            | (uu____77118,lift_t1) ->
                let uu____77120 =
                  let uu____77127 =
                    let uu____77128 =
                      let uu____77145 =
                        let uu____77156 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77165 =
                          let uu____77176 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____77185 =
                            let uu____77196 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____77196]  in
                          uu____77176 :: uu____77185  in
                        uu____77156 :: uu____77165  in
                      (lift_t1, uu____77145)  in
                    FStar_Syntax_Syntax.Tm_app uu____77128  in
                  FStar_Syntax_Syntax.mk uu____77127  in
                uu____77120 FStar_Pervasives_Native.None
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
              let uu____77301 =
                let uu____77302 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____77302
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____77301  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____77311 =
              let uu____77313 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____77313  in
            let uu____77314 =
              let uu____77316 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____77344 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____77344)
                 in
              FStar_Util.dflt "none" uu____77316  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____77311
              uu____77314
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____77373  ->
                    match uu____77373 with
                    | (e,uu____77381) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____77404 =
            match uu____77404 with
            | (i,j) ->
                let uu____77415 = FStar_Ident.lid_equals i j  in
                if uu____77415
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _77422  -> FStar_Pervasives_Native.Some _77422)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____77451 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____77461 = FStar_Ident.lid_equals i k  in
                        if uu____77461
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____77475 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____77475
                                  then []
                                  else
                                    (let uu____77482 =
                                       let uu____77491 =
                                         find_edge order1 (i, k)  in
                                       let uu____77494 =
                                         find_edge order1 (k, j)  in
                                       (uu____77491, uu____77494)  in
                                     match uu____77482 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____77509 =
                                           compose_edges e1 e2  in
                                         [uu____77509]
                                     | uu____77510 -> [])))))
                 in
              FStar_List.append order1 uu____77451  in
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
                   let uu____77540 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____77543 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____77543
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____77540
                   then
                     let uu____77550 =
                       let uu____77556 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____77556)
                        in
                     let uu____77560 = get_range env  in
                     FStar_Errors.raise_error uu____77550 uu____77560
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____77638 = FStar_Ident.lid_equals i j
                                   in
                                if uu____77638
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____77690 =
                                              let uu____77699 =
                                                find_edge order2 (i, k)  in
                                              let uu____77702 =
                                                find_edge order2 (j, k)  in
                                              (uu____77699, uu____77702)  in
                                            match uu____77690 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____77744,uu____77745)
                                                     ->
                                                     let uu____77752 =
                                                       let uu____77759 =
                                                         let uu____77761 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77761
                                                          in
                                                       let uu____77764 =
                                                         let uu____77766 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77766
                                                          in
                                                       (uu____77759,
                                                         uu____77764)
                                                        in
                                                     (match uu____77752 with
                                                      | (true ,true ) ->
                                                          let uu____77783 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____77783
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
                                            | uu____77826 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2069_77899 = env.effects  in
              { decls = (uu___2069_77899.decls); order = order2; joins }  in
            let uu___2072_77900 = env  in
            {
              solver = (uu___2072_77900.solver);
              range = (uu___2072_77900.range);
              curmodule = (uu___2072_77900.curmodule);
              gamma = (uu___2072_77900.gamma);
              gamma_sig = (uu___2072_77900.gamma_sig);
              gamma_cache = (uu___2072_77900.gamma_cache);
              modules = (uu___2072_77900.modules);
              expected_typ = (uu___2072_77900.expected_typ);
              sigtab = (uu___2072_77900.sigtab);
              attrtab = (uu___2072_77900.attrtab);
              is_pattern = (uu___2072_77900.is_pattern);
              instantiate_imp = (uu___2072_77900.instantiate_imp);
              effects;
              generalize = (uu___2072_77900.generalize);
              letrecs = (uu___2072_77900.letrecs);
              top_level = (uu___2072_77900.top_level);
              check_uvars = (uu___2072_77900.check_uvars);
              use_eq = (uu___2072_77900.use_eq);
              is_iface = (uu___2072_77900.is_iface);
              admit = (uu___2072_77900.admit);
              lax = (uu___2072_77900.lax);
              lax_universes = (uu___2072_77900.lax_universes);
              phase1 = (uu___2072_77900.phase1);
              failhard = (uu___2072_77900.failhard);
              nosynth = (uu___2072_77900.nosynth);
              uvar_subtyping = (uu___2072_77900.uvar_subtyping);
              tc_term = (uu___2072_77900.tc_term);
              type_of = (uu___2072_77900.type_of);
              universe_of = (uu___2072_77900.universe_of);
              check_type_of = (uu___2072_77900.check_type_of);
              use_bv_sorts = (uu___2072_77900.use_bv_sorts);
              qtbl_name_and_index = (uu___2072_77900.qtbl_name_and_index);
              normalized_eff_names = (uu___2072_77900.normalized_eff_names);
              fv_delta_depths = (uu___2072_77900.fv_delta_depths);
              proof_ns = (uu___2072_77900.proof_ns);
              synth_hook = (uu___2072_77900.synth_hook);
              splice = (uu___2072_77900.splice);
              postprocess = (uu___2072_77900.postprocess);
              is_native_tactic = (uu___2072_77900.is_native_tactic);
              identifier_info = (uu___2072_77900.identifier_info);
              tc_hooks = (uu___2072_77900.tc_hooks);
              dsenv = (uu___2072_77900.dsenv);
              nbe = (uu___2072_77900.nbe)
            }))
      | uu____77901 -> env
  
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
        | uu____77930 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____77943 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____77943 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____77960 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____77960 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____77985 =
                     let uu____77991 =
                       let uu____77993 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____78001 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____78012 =
                         let uu____78014 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____78014  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____77993 uu____78001 uu____78012
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____77991)
                      in
                   FStar_Errors.raise_error uu____77985
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____78022 =
                     let uu____78033 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____78033 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____78070  ->
                        fun uu____78071  ->
                          match (uu____78070, uu____78071) with
                          | ((x,uu____78101),(t,uu____78103)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____78022
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____78134 =
                     let uu___2110_78135 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2110_78135.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2110_78135.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2110_78135.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2110_78135.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____78134
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____78147 .
    'Auu____78147 ->
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
          let uu____78177 = effect_decl_opt env effect_name  in
          match uu____78177 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____78216 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____78239 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____78278 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____78278
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____78283 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____78283
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____78298 =
                     let uu____78301 = get_range env  in
                     let uu____78302 =
                       let uu____78309 =
                         let uu____78310 =
                           let uu____78327 =
                             let uu____78338 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____78338; wp]  in
                           (repr, uu____78327)  in
                         FStar_Syntax_Syntax.Tm_app uu____78310  in
                       FStar_Syntax_Syntax.mk uu____78309  in
                     uu____78302 FStar_Pervasives_Native.None uu____78301  in
                   FStar_Pervasives_Native.Some uu____78298)
  
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
      | uu____78485 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____78500 =
        let uu____78501 = FStar_Syntax_Subst.compress t  in
        uu____78501.FStar_Syntax_Syntax.n  in
      match uu____78500 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____78505,c) ->
          is_reifiable_comp env c
      | uu____78527 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____78547 =
           let uu____78549 = is_reifiable_effect env l  in
           Prims.op_Negation uu____78549  in
         if uu____78547
         then
           let uu____78552 =
             let uu____78558 =
               let uu____78560 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____78560
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____78558)  in
           let uu____78564 = get_range env  in
           FStar_Errors.raise_error uu____78552 uu____78564
         else ());
        (let uu____78567 = effect_repr_aux true env c u_c  in
         match uu____78567 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2175_78603 = env  in
        {
          solver = (uu___2175_78603.solver);
          range = (uu___2175_78603.range);
          curmodule = (uu___2175_78603.curmodule);
          gamma = (uu___2175_78603.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2175_78603.gamma_cache);
          modules = (uu___2175_78603.modules);
          expected_typ = (uu___2175_78603.expected_typ);
          sigtab = (uu___2175_78603.sigtab);
          attrtab = (uu___2175_78603.attrtab);
          is_pattern = (uu___2175_78603.is_pattern);
          instantiate_imp = (uu___2175_78603.instantiate_imp);
          effects = (uu___2175_78603.effects);
          generalize = (uu___2175_78603.generalize);
          letrecs = (uu___2175_78603.letrecs);
          top_level = (uu___2175_78603.top_level);
          check_uvars = (uu___2175_78603.check_uvars);
          use_eq = (uu___2175_78603.use_eq);
          is_iface = (uu___2175_78603.is_iface);
          admit = (uu___2175_78603.admit);
          lax = (uu___2175_78603.lax);
          lax_universes = (uu___2175_78603.lax_universes);
          phase1 = (uu___2175_78603.phase1);
          failhard = (uu___2175_78603.failhard);
          nosynth = (uu___2175_78603.nosynth);
          uvar_subtyping = (uu___2175_78603.uvar_subtyping);
          tc_term = (uu___2175_78603.tc_term);
          type_of = (uu___2175_78603.type_of);
          universe_of = (uu___2175_78603.universe_of);
          check_type_of = (uu___2175_78603.check_type_of);
          use_bv_sorts = (uu___2175_78603.use_bv_sorts);
          qtbl_name_and_index = (uu___2175_78603.qtbl_name_and_index);
          normalized_eff_names = (uu___2175_78603.normalized_eff_names);
          fv_delta_depths = (uu___2175_78603.fv_delta_depths);
          proof_ns = (uu___2175_78603.proof_ns);
          synth_hook = (uu___2175_78603.synth_hook);
          splice = (uu___2175_78603.splice);
          postprocess = (uu___2175_78603.postprocess);
          is_native_tactic = (uu___2175_78603.is_native_tactic);
          identifier_info = (uu___2175_78603.identifier_info);
          tc_hooks = (uu___2175_78603.tc_hooks);
          dsenv = (uu___2175_78603.dsenv);
          nbe = (uu___2175_78603.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2182_78617 = env  in
      {
        solver = (uu___2182_78617.solver);
        range = (uu___2182_78617.range);
        curmodule = (uu___2182_78617.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2182_78617.gamma_sig);
        gamma_cache = (uu___2182_78617.gamma_cache);
        modules = (uu___2182_78617.modules);
        expected_typ = (uu___2182_78617.expected_typ);
        sigtab = (uu___2182_78617.sigtab);
        attrtab = (uu___2182_78617.attrtab);
        is_pattern = (uu___2182_78617.is_pattern);
        instantiate_imp = (uu___2182_78617.instantiate_imp);
        effects = (uu___2182_78617.effects);
        generalize = (uu___2182_78617.generalize);
        letrecs = (uu___2182_78617.letrecs);
        top_level = (uu___2182_78617.top_level);
        check_uvars = (uu___2182_78617.check_uvars);
        use_eq = (uu___2182_78617.use_eq);
        is_iface = (uu___2182_78617.is_iface);
        admit = (uu___2182_78617.admit);
        lax = (uu___2182_78617.lax);
        lax_universes = (uu___2182_78617.lax_universes);
        phase1 = (uu___2182_78617.phase1);
        failhard = (uu___2182_78617.failhard);
        nosynth = (uu___2182_78617.nosynth);
        uvar_subtyping = (uu___2182_78617.uvar_subtyping);
        tc_term = (uu___2182_78617.tc_term);
        type_of = (uu___2182_78617.type_of);
        universe_of = (uu___2182_78617.universe_of);
        check_type_of = (uu___2182_78617.check_type_of);
        use_bv_sorts = (uu___2182_78617.use_bv_sorts);
        qtbl_name_and_index = (uu___2182_78617.qtbl_name_and_index);
        normalized_eff_names = (uu___2182_78617.normalized_eff_names);
        fv_delta_depths = (uu___2182_78617.fv_delta_depths);
        proof_ns = (uu___2182_78617.proof_ns);
        synth_hook = (uu___2182_78617.synth_hook);
        splice = (uu___2182_78617.splice);
        postprocess = (uu___2182_78617.postprocess);
        is_native_tactic = (uu___2182_78617.is_native_tactic);
        identifier_info = (uu___2182_78617.identifier_info);
        tc_hooks = (uu___2182_78617.tc_hooks);
        dsenv = (uu___2182_78617.dsenv);
        nbe = (uu___2182_78617.nbe)
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
            (let uu___2195_78675 = env  in
             {
               solver = (uu___2195_78675.solver);
               range = (uu___2195_78675.range);
               curmodule = (uu___2195_78675.curmodule);
               gamma = rest;
               gamma_sig = (uu___2195_78675.gamma_sig);
               gamma_cache = (uu___2195_78675.gamma_cache);
               modules = (uu___2195_78675.modules);
               expected_typ = (uu___2195_78675.expected_typ);
               sigtab = (uu___2195_78675.sigtab);
               attrtab = (uu___2195_78675.attrtab);
               is_pattern = (uu___2195_78675.is_pattern);
               instantiate_imp = (uu___2195_78675.instantiate_imp);
               effects = (uu___2195_78675.effects);
               generalize = (uu___2195_78675.generalize);
               letrecs = (uu___2195_78675.letrecs);
               top_level = (uu___2195_78675.top_level);
               check_uvars = (uu___2195_78675.check_uvars);
               use_eq = (uu___2195_78675.use_eq);
               is_iface = (uu___2195_78675.is_iface);
               admit = (uu___2195_78675.admit);
               lax = (uu___2195_78675.lax);
               lax_universes = (uu___2195_78675.lax_universes);
               phase1 = (uu___2195_78675.phase1);
               failhard = (uu___2195_78675.failhard);
               nosynth = (uu___2195_78675.nosynth);
               uvar_subtyping = (uu___2195_78675.uvar_subtyping);
               tc_term = (uu___2195_78675.tc_term);
               type_of = (uu___2195_78675.type_of);
               universe_of = (uu___2195_78675.universe_of);
               check_type_of = (uu___2195_78675.check_type_of);
               use_bv_sorts = (uu___2195_78675.use_bv_sorts);
               qtbl_name_and_index = (uu___2195_78675.qtbl_name_and_index);
               normalized_eff_names = (uu___2195_78675.normalized_eff_names);
               fv_delta_depths = (uu___2195_78675.fv_delta_depths);
               proof_ns = (uu___2195_78675.proof_ns);
               synth_hook = (uu___2195_78675.synth_hook);
               splice = (uu___2195_78675.splice);
               postprocess = (uu___2195_78675.postprocess);
               is_native_tactic = (uu___2195_78675.is_native_tactic);
               identifier_info = (uu___2195_78675.identifier_info);
               tc_hooks = (uu___2195_78675.tc_hooks);
               dsenv = (uu___2195_78675.dsenv);
               nbe = (uu___2195_78675.nbe)
             }))
    | uu____78676 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____78705  ->
             match uu____78705 with | (x,uu____78713) -> push_bv env1 x) env
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
            let uu___2209_78748 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2209_78748.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2209_78748.FStar_Syntax_Syntax.index);
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
      (let uu___2220_78790 = env  in
       {
         solver = (uu___2220_78790.solver);
         range = (uu___2220_78790.range);
         curmodule = (uu___2220_78790.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2220_78790.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2220_78790.sigtab);
         attrtab = (uu___2220_78790.attrtab);
         is_pattern = (uu___2220_78790.is_pattern);
         instantiate_imp = (uu___2220_78790.instantiate_imp);
         effects = (uu___2220_78790.effects);
         generalize = (uu___2220_78790.generalize);
         letrecs = (uu___2220_78790.letrecs);
         top_level = (uu___2220_78790.top_level);
         check_uvars = (uu___2220_78790.check_uvars);
         use_eq = (uu___2220_78790.use_eq);
         is_iface = (uu___2220_78790.is_iface);
         admit = (uu___2220_78790.admit);
         lax = (uu___2220_78790.lax);
         lax_universes = (uu___2220_78790.lax_universes);
         phase1 = (uu___2220_78790.phase1);
         failhard = (uu___2220_78790.failhard);
         nosynth = (uu___2220_78790.nosynth);
         uvar_subtyping = (uu___2220_78790.uvar_subtyping);
         tc_term = (uu___2220_78790.tc_term);
         type_of = (uu___2220_78790.type_of);
         universe_of = (uu___2220_78790.universe_of);
         check_type_of = (uu___2220_78790.check_type_of);
         use_bv_sorts = (uu___2220_78790.use_bv_sorts);
         qtbl_name_and_index = (uu___2220_78790.qtbl_name_and_index);
         normalized_eff_names = (uu___2220_78790.normalized_eff_names);
         fv_delta_depths = (uu___2220_78790.fv_delta_depths);
         proof_ns = (uu___2220_78790.proof_ns);
         synth_hook = (uu___2220_78790.synth_hook);
         splice = (uu___2220_78790.splice);
         postprocess = (uu___2220_78790.postprocess);
         is_native_tactic = (uu___2220_78790.is_native_tactic);
         identifier_info = (uu___2220_78790.identifier_info);
         tc_hooks = (uu___2220_78790.tc_hooks);
         dsenv = (uu___2220_78790.dsenv);
         nbe = (uu___2220_78790.nbe)
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
        let uu____78834 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____78834 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____78862 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____78862)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2235_78878 = env  in
      {
        solver = (uu___2235_78878.solver);
        range = (uu___2235_78878.range);
        curmodule = (uu___2235_78878.curmodule);
        gamma = (uu___2235_78878.gamma);
        gamma_sig = (uu___2235_78878.gamma_sig);
        gamma_cache = (uu___2235_78878.gamma_cache);
        modules = (uu___2235_78878.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2235_78878.sigtab);
        attrtab = (uu___2235_78878.attrtab);
        is_pattern = (uu___2235_78878.is_pattern);
        instantiate_imp = (uu___2235_78878.instantiate_imp);
        effects = (uu___2235_78878.effects);
        generalize = (uu___2235_78878.generalize);
        letrecs = (uu___2235_78878.letrecs);
        top_level = (uu___2235_78878.top_level);
        check_uvars = (uu___2235_78878.check_uvars);
        use_eq = false;
        is_iface = (uu___2235_78878.is_iface);
        admit = (uu___2235_78878.admit);
        lax = (uu___2235_78878.lax);
        lax_universes = (uu___2235_78878.lax_universes);
        phase1 = (uu___2235_78878.phase1);
        failhard = (uu___2235_78878.failhard);
        nosynth = (uu___2235_78878.nosynth);
        uvar_subtyping = (uu___2235_78878.uvar_subtyping);
        tc_term = (uu___2235_78878.tc_term);
        type_of = (uu___2235_78878.type_of);
        universe_of = (uu___2235_78878.universe_of);
        check_type_of = (uu___2235_78878.check_type_of);
        use_bv_sorts = (uu___2235_78878.use_bv_sorts);
        qtbl_name_and_index = (uu___2235_78878.qtbl_name_and_index);
        normalized_eff_names = (uu___2235_78878.normalized_eff_names);
        fv_delta_depths = (uu___2235_78878.fv_delta_depths);
        proof_ns = (uu___2235_78878.proof_ns);
        synth_hook = (uu___2235_78878.synth_hook);
        splice = (uu___2235_78878.splice);
        postprocess = (uu___2235_78878.postprocess);
        is_native_tactic = (uu___2235_78878.is_native_tactic);
        identifier_info = (uu___2235_78878.identifier_info);
        tc_hooks = (uu___2235_78878.tc_hooks);
        dsenv = (uu___2235_78878.dsenv);
        nbe = (uu___2235_78878.nbe)
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
    let uu____78909 = expected_typ env_  in
    ((let uu___2242_78915 = env_  in
      {
        solver = (uu___2242_78915.solver);
        range = (uu___2242_78915.range);
        curmodule = (uu___2242_78915.curmodule);
        gamma = (uu___2242_78915.gamma);
        gamma_sig = (uu___2242_78915.gamma_sig);
        gamma_cache = (uu___2242_78915.gamma_cache);
        modules = (uu___2242_78915.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2242_78915.sigtab);
        attrtab = (uu___2242_78915.attrtab);
        is_pattern = (uu___2242_78915.is_pattern);
        instantiate_imp = (uu___2242_78915.instantiate_imp);
        effects = (uu___2242_78915.effects);
        generalize = (uu___2242_78915.generalize);
        letrecs = (uu___2242_78915.letrecs);
        top_level = (uu___2242_78915.top_level);
        check_uvars = (uu___2242_78915.check_uvars);
        use_eq = false;
        is_iface = (uu___2242_78915.is_iface);
        admit = (uu___2242_78915.admit);
        lax = (uu___2242_78915.lax);
        lax_universes = (uu___2242_78915.lax_universes);
        phase1 = (uu___2242_78915.phase1);
        failhard = (uu___2242_78915.failhard);
        nosynth = (uu___2242_78915.nosynth);
        uvar_subtyping = (uu___2242_78915.uvar_subtyping);
        tc_term = (uu___2242_78915.tc_term);
        type_of = (uu___2242_78915.type_of);
        universe_of = (uu___2242_78915.universe_of);
        check_type_of = (uu___2242_78915.check_type_of);
        use_bv_sorts = (uu___2242_78915.use_bv_sorts);
        qtbl_name_and_index = (uu___2242_78915.qtbl_name_and_index);
        normalized_eff_names = (uu___2242_78915.normalized_eff_names);
        fv_delta_depths = (uu___2242_78915.fv_delta_depths);
        proof_ns = (uu___2242_78915.proof_ns);
        synth_hook = (uu___2242_78915.synth_hook);
        splice = (uu___2242_78915.splice);
        postprocess = (uu___2242_78915.postprocess);
        is_native_tactic = (uu___2242_78915.is_native_tactic);
        identifier_info = (uu___2242_78915.identifier_info);
        tc_hooks = (uu___2242_78915.tc_hooks);
        dsenv = (uu___2242_78915.dsenv);
        nbe = (uu___2242_78915.nbe)
      }), uu____78909)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____78927 =
      let uu____78930 = FStar_Ident.id_of_text ""  in [uu____78930]  in
    FStar_Ident.lid_of_ids uu____78927  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____78937 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____78937
        then
          let uu____78942 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____78942 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2250_78970 = env  in
       {
         solver = (uu___2250_78970.solver);
         range = (uu___2250_78970.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2250_78970.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2250_78970.expected_typ);
         sigtab = (uu___2250_78970.sigtab);
         attrtab = (uu___2250_78970.attrtab);
         is_pattern = (uu___2250_78970.is_pattern);
         instantiate_imp = (uu___2250_78970.instantiate_imp);
         effects = (uu___2250_78970.effects);
         generalize = (uu___2250_78970.generalize);
         letrecs = (uu___2250_78970.letrecs);
         top_level = (uu___2250_78970.top_level);
         check_uvars = (uu___2250_78970.check_uvars);
         use_eq = (uu___2250_78970.use_eq);
         is_iface = (uu___2250_78970.is_iface);
         admit = (uu___2250_78970.admit);
         lax = (uu___2250_78970.lax);
         lax_universes = (uu___2250_78970.lax_universes);
         phase1 = (uu___2250_78970.phase1);
         failhard = (uu___2250_78970.failhard);
         nosynth = (uu___2250_78970.nosynth);
         uvar_subtyping = (uu___2250_78970.uvar_subtyping);
         tc_term = (uu___2250_78970.tc_term);
         type_of = (uu___2250_78970.type_of);
         universe_of = (uu___2250_78970.universe_of);
         check_type_of = (uu___2250_78970.check_type_of);
         use_bv_sorts = (uu___2250_78970.use_bv_sorts);
         qtbl_name_and_index = (uu___2250_78970.qtbl_name_and_index);
         normalized_eff_names = (uu___2250_78970.normalized_eff_names);
         fv_delta_depths = (uu___2250_78970.fv_delta_depths);
         proof_ns = (uu___2250_78970.proof_ns);
         synth_hook = (uu___2250_78970.synth_hook);
         splice = (uu___2250_78970.splice);
         postprocess = (uu___2250_78970.postprocess);
         is_native_tactic = (uu___2250_78970.is_native_tactic);
         identifier_info = (uu___2250_78970.identifier_info);
         tc_hooks = (uu___2250_78970.tc_hooks);
         dsenv = (uu___2250_78970.dsenv);
         nbe = (uu___2250_78970.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79022)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79026,(uu____79027,t)))::tl1
          ->
          let uu____79048 =
            let uu____79051 = FStar_Syntax_Free.uvars t  in
            ext out uu____79051  in
          aux uu____79048 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79054;
            FStar_Syntax_Syntax.index = uu____79055;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79063 =
            let uu____79066 = FStar_Syntax_Free.uvars t  in
            ext out uu____79066  in
          aux uu____79063 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79124)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79128,(uu____79129,t)))::tl1
          ->
          let uu____79150 =
            let uu____79153 = FStar_Syntax_Free.univs t  in
            ext out uu____79153  in
          aux uu____79150 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79156;
            FStar_Syntax_Syntax.index = uu____79157;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79165 =
            let uu____79168 = FStar_Syntax_Free.univs t  in
            ext out uu____79168  in
          aux uu____79165 tl1
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
          let uu____79230 = FStar_Util.set_add uname out  in
          aux uu____79230 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79233,(uu____79234,t)))::tl1
          ->
          let uu____79255 =
            let uu____79258 = FStar_Syntax_Free.univnames t  in
            ext out uu____79258  in
          aux uu____79255 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79261;
            FStar_Syntax_Syntax.index = uu____79262;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79270 =
            let uu____79273 = FStar_Syntax_Free.univnames t  in
            ext out uu____79273  in
          aux uu____79270 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_79294  ->
            match uu___457_79294 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____79298 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____79311 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____79322 =
      let uu____79331 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____79331
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____79322 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____79379 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_79392  ->
              match uu___458_79392 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____79395 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____79395
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____79401) ->
                  let uu____79418 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____79418))
       in
    FStar_All.pipe_right uu____79379 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_79432  ->
    match uu___459_79432 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____79438 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____79438
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____79461  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____79516) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____79549,uu____79550) -> false  in
      let uu____79564 =
        FStar_List.tryFind
          (fun uu____79586  ->
             match uu____79586 with | (p,uu____79597) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____79564 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____79616,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____79646 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____79646
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2393_79668 = e  in
        {
          solver = (uu___2393_79668.solver);
          range = (uu___2393_79668.range);
          curmodule = (uu___2393_79668.curmodule);
          gamma = (uu___2393_79668.gamma);
          gamma_sig = (uu___2393_79668.gamma_sig);
          gamma_cache = (uu___2393_79668.gamma_cache);
          modules = (uu___2393_79668.modules);
          expected_typ = (uu___2393_79668.expected_typ);
          sigtab = (uu___2393_79668.sigtab);
          attrtab = (uu___2393_79668.attrtab);
          is_pattern = (uu___2393_79668.is_pattern);
          instantiate_imp = (uu___2393_79668.instantiate_imp);
          effects = (uu___2393_79668.effects);
          generalize = (uu___2393_79668.generalize);
          letrecs = (uu___2393_79668.letrecs);
          top_level = (uu___2393_79668.top_level);
          check_uvars = (uu___2393_79668.check_uvars);
          use_eq = (uu___2393_79668.use_eq);
          is_iface = (uu___2393_79668.is_iface);
          admit = (uu___2393_79668.admit);
          lax = (uu___2393_79668.lax);
          lax_universes = (uu___2393_79668.lax_universes);
          phase1 = (uu___2393_79668.phase1);
          failhard = (uu___2393_79668.failhard);
          nosynth = (uu___2393_79668.nosynth);
          uvar_subtyping = (uu___2393_79668.uvar_subtyping);
          tc_term = (uu___2393_79668.tc_term);
          type_of = (uu___2393_79668.type_of);
          universe_of = (uu___2393_79668.universe_of);
          check_type_of = (uu___2393_79668.check_type_of);
          use_bv_sorts = (uu___2393_79668.use_bv_sorts);
          qtbl_name_and_index = (uu___2393_79668.qtbl_name_and_index);
          normalized_eff_names = (uu___2393_79668.normalized_eff_names);
          fv_delta_depths = (uu___2393_79668.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2393_79668.synth_hook);
          splice = (uu___2393_79668.splice);
          postprocess = (uu___2393_79668.postprocess);
          is_native_tactic = (uu___2393_79668.is_native_tactic);
          identifier_info = (uu___2393_79668.identifier_info);
          tc_hooks = (uu___2393_79668.tc_hooks);
          dsenv = (uu___2393_79668.dsenv);
          nbe = (uu___2393_79668.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2402_79716 = e  in
      {
        solver = (uu___2402_79716.solver);
        range = (uu___2402_79716.range);
        curmodule = (uu___2402_79716.curmodule);
        gamma = (uu___2402_79716.gamma);
        gamma_sig = (uu___2402_79716.gamma_sig);
        gamma_cache = (uu___2402_79716.gamma_cache);
        modules = (uu___2402_79716.modules);
        expected_typ = (uu___2402_79716.expected_typ);
        sigtab = (uu___2402_79716.sigtab);
        attrtab = (uu___2402_79716.attrtab);
        is_pattern = (uu___2402_79716.is_pattern);
        instantiate_imp = (uu___2402_79716.instantiate_imp);
        effects = (uu___2402_79716.effects);
        generalize = (uu___2402_79716.generalize);
        letrecs = (uu___2402_79716.letrecs);
        top_level = (uu___2402_79716.top_level);
        check_uvars = (uu___2402_79716.check_uvars);
        use_eq = (uu___2402_79716.use_eq);
        is_iface = (uu___2402_79716.is_iface);
        admit = (uu___2402_79716.admit);
        lax = (uu___2402_79716.lax);
        lax_universes = (uu___2402_79716.lax_universes);
        phase1 = (uu___2402_79716.phase1);
        failhard = (uu___2402_79716.failhard);
        nosynth = (uu___2402_79716.nosynth);
        uvar_subtyping = (uu___2402_79716.uvar_subtyping);
        tc_term = (uu___2402_79716.tc_term);
        type_of = (uu___2402_79716.type_of);
        universe_of = (uu___2402_79716.universe_of);
        check_type_of = (uu___2402_79716.check_type_of);
        use_bv_sorts = (uu___2402_79716.use_bv_sorts);
        qtbl_name_and_index = (uu___2402_79716.qtbl_name_and_index);
        normalized_eff_names = (uu___2402_79716.normalized_eff_names);
        fv_delta_depths = (uu___2402_79716.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2402_79716.synth_hook);
        splice = (uu___2402_79716.splice);
        postprocess = (uu___2402_79716.postprocess);
        is_native_tactic = (uu___2402_79716.is_native_tactic);
        identifier_info = (uu___2402_79716.identifier_info);
        tc_hooks = (uu___2402_79716.tc_hooks);
        dsenv = (uu___2402_79716.dsenv);
        nbe = (uu___2402_79716.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____79732 = FStar_Syntax_Free.names t  in
      let uu____79735 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____79732 uu____79735
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____79758 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____79758
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____79768 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____79768
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____79789 =
      match uu____79789 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____79809 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____79809)
       in
    let uu____79817 =
      let uu____79821 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____79821 FStar_List.rev  in
    FStar_All.pipe_right uu____79817 (FStar_String.concat " ")
  
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
                  (let uu____79891 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____79891 with
                   | FStar_Pervasives_Native.Some uu____79895 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____79898 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____79908;
        univ_ineqs = uu____79909; implicits = uu____79910;_} -> true
    | uu____79922 -> false
  
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
          let uu___2446_79953 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2446_79953.deferred);
            univ_ineqs = (uu___2446_79953.univ_ineqs);
            implicits = (uu___2446_79953.implicits)
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
          let uu____79992 = FStar_Options.defensive ()  in
          if uu____79992
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____79998 =
              let uu____80000 =
                let uu____80002 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____80002  in
              Prims.op_Negation uu____80000  in
            (if uu____79998
             then
               let uu____80009 =
                 let uu____80015 =
                   let uu____80017 = FStar_Syntax_Print.term_to_string t  in
                   let uu____80019 =
                     let uu____80021 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____80021
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____80017 uu____80019
                    in
                 (FStar_Errors.Warning_Defensive, uu____80015)  in
               FStar_Errors.log_issue rng uu____80009
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
          let uu____80061 =
            let uu____80063 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80063  in
          if uu____80061
          then ()
          else
            (let uu____80068 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____80068 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____80094 =
            let uu____80096 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80096  in
          if uu____80094
          then ()
          else
            (let uu____80101 = bound_vars e  in
             def_check_closed_in rng msg uu____80101 t)
  
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
          let uu___2483_80140 = g  in
          let uu____80141 =
            let uu____80142 =
              let uu____80143 =
                let uu____80150 =
                  let uu____80151 =
                    let uu____80168 =
                      let uu____80179 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____80179]  in
                    (f, uu____80168)  in
                  FStar_Syntax_Syntax.Tm_app uu____80151  in
                FStar_Syntax_Syntax.mk uu____80150  in
              uu____80143 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _80219  -> FStar_TypeChecker_Common.NonTrivial _80219)
              uu____80142
             in
          {
            guard_f = uu____80141;
            deferred = (uu___2483_80140.deferred);
            univ_ineqs = (uu___2483_80140.univ_ineqs);
            implicits = (uu___2483_80140.implicits)
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
          let uu___2490_80237 = g  in
          let uu____80238 =
            let uu____80239 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80239  in
          {
            guard_f = uu____80238;
            deferred = (uu___2490_80237.deferred);
            univ_ineqs = (uu___2490_80237.univ_ineqs);
            implicits = (uu___2490_80237.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2495_80256 = g  in
          let uu____80257 =
            let uu____80258 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____80258  in
          {
            guard_f = uu____80257;
            deferred = (uu___2495_80256.deferred);
            univ_ineqs = (uu___2495_80256.univ_ineqs);
            implicits = (uu___2495_80256.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2499_80260 = g  in
          let uu____80261 =
            let uu____80262 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80262  in
          {
            guard_f = uu____80261;
            deferred = (uu___2499_80260.deferred);
            univ_ineqs = (uu___2499_80260.univ_ineqs);
            implicits = (uu___2499_80260.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____80269 ->
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
          let uu____80286 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____80286
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____80293 =
      let uu____80294 = FStar_Syntax_Util.unmeta t  in
      uu____80294.FStar_Syntax_Syntax.n  in
    match uu____80293 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____80298 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____80341 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____80341;
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
                       let uu____80436 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____80436
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2554_80443 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2554_80443.deferred);
              univ_ineqs = (uu___2554_80443.univ_ineqs);
              implicits = (uu___2554_80443.implicits)
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
               let uu____80477 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____80477
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
            let uu___2569_80504 = g  in
            let uu____80505 =
              let uu____80506 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____80506  in
            {
              guard_f = uu____80505;
              deferred = (uu___2569_80504.deferred);
              univ_ineqs = (uu___2569_80504.univ_ineqs);
              implicits = (uu___2569_80504.implicits)
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
              let uu____80564 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____80564 with
              | FStar_Pervasives_Native.Some
                  (uu____80589::(tm,uu____80591)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____80655 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____80673 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____80673;
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
                      let uu___2591_80705 = trivial_guard  in
                      {
                        guard_f = (uu___2591_80705.guard_f);
                        deferred = (uu___2591_80705.deferred);
                        univ_ineqs = (uu___2591_80705.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____80723  -> ());
    push = (fun uu____80725  -> ());
    pop = (fun uu____80728  -> ());
    snapshot =
      (fun uu____80731  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____80750  -> fun uu____80751  -> ());
    encode_sig = (fun uu____80766  -> fun uu____80767  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____80773 =
             let uu____80780 = FStar_Options.peek ()  in (e, g, uu____80780)
              in
           [uu____80773]);
    solve = (fun uu____80796  -> fun uu____80797  -> fun uu____80798  -> ());
    finish = (fun uu____80805  -> ());
    refresh = (fun uu____80807  -> ())
  } 