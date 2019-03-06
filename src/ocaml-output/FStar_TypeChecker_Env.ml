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
    match projectee with | Beta  -> true | uu____52179 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____52190 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____52201 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____52213 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____52232 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____52243 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____52254 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____52265 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____52276 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____52287 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____52299 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____52321 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____52349 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____52377 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____52402 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____52413 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____52424 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____52435 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____52446 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____52457 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____52468 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____52479 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____52490 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____52501 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____52512 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____52523 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____52534 -> false
  
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
      | uu____52594 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____52620 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____52631 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____52642 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____52654 -> false
  
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
           (fun uu___446_63872  ->
              match uu___446_63872 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____63875 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____63875  in
                  let uu____63876 =
                    let uu____63877 = FStar_Syntax_Subst.compress y  in
                    uu____63877.FStar_Syntax_Syntax.n  in
                  (match uu____63876 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____63881 =
                         let uu___775_63882 = y1  in
                         let uu____63883 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_63882.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_63882.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____63883
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____63881
                   | uu____63886 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_63900 = env  in
      let uu____63901 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_63900.solver);
        range = (uu___781_63900.range);
        curmodule = (uu___781_63900.curmodule);
        gamma = uu____63901;
        gamma_sig = (uu___781_63900.gamma_sig);
        gamma_cache = (uu___781_63900.gamma_cache);
        modules = (uu___781_63900.modules);
        expected_typ = (uu___781_63900.expected_typ);
        sigtab = (uu___781_63900.sigtab);
        attrtab = (uu___781_63900.attrtab);
        is_pattern = (uu___781_63900.is_pattern);
        instantiate_imp = (uu___781_63900.instantiate_imp);
        effects = (uu___781_63900.effects);
        generalize = (uu___781_63900.generalize);
        letrecs = (uu___781_63900.letrecs);
        top_level = (uu___781_63900.top_level);
        check_uvars = (uu___781_63900.check_uvars);
        use_eq = (uu___781_63900.use_eq);
        is_iface = (uu___781_63900.is_iface);
        admit = (uu___781_63900.admit);
        lax = (uu___781_63900.lax);
        lax_universes = (uu___781_63900.lax_universes);
        phase1 = (uu___781_63900.phase1);
        failhard = (uu___781_63900.failhard);
        nosynth = (uu___781_63900.nosynth);
        uvar_subtyping = (uu___781_63900.uvar_subtyping);
        tc_term = (uu___781_63900.tc_term);
        type_of = (uu___781_63900.type_of);
        universe_of = (uu___781_63900.universe_of);
        check_type_of = (uu___781_63900.check_type_of);
        use_bv_sorts = (uu___781_63900.use_bv_sorts);
        qtbl_name_and_index = (uu___781_63900.qtbl_name_and_index);
        normalized_eff_names = (uu___781_63900.normalized_eff_names);
        fv_delta_depths = (uu___781_63900.fv_delta_depths);
        proof_ns = (uu___781_63900.proof_ns);
        synth_hook = (uu___781_63900.synth_hook);
        splice = (uu___781_63900.splice);
        postprocess = (uu___781_63900.postprocess);
        is_native_tactic = (uu___781_63900.is_native_tactic);
        identifier_info = (uu___781_63900.identifier_info);
        tc_hooks = (uu___781_63900.tc_hooks);
        dsenv = (uu___781_63900.dsenv);
        nbe = (uu___781_63900.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____63909  -> fun uu____63910  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_63932 = env  in
      {
        solver = (uu___788_63932.solver);
        range = (uu___788_63932.range);
        curmodule = (uu___788_63932.curmodule);
        gamma = (uu___788_63932.gamma);
        gamma_sig = (uu___788_63932.gamma_sig);
        gamma_cache = (uu___788_63932.gamma_cache);
        modules = (uu___788_63932.modules);
        expected_typ = (uu___788_63932.expected_typ);
        sigtab = (uu___788_63932.sigtab);
        attrtab = (uu___788_63932.attrtab);
        is_pattern = (uu___788_63932.is_pattern);
        instantiate_imp = (uu___788_63932.instantiate_imp);
        effects = (uu___788_63932.effects);
        generalize = (uu___788_63932.generalize);
        letrecs = (uu___788_63932.letrecs);
        top_level = (uu___788_63932.top_level);
        check_uvars = (uu___788_63932.check_uvars);
        use_eq = (uu___788_63932.use_eq);
        is_iface = (uu___788_63932.is_iface);
        admit = (uu___788_63932.admit);
        lax = (uu___788_63932.lax);
        lax_universes = (uu___788_63932.lax_universes);
        phase1 = (uu___788_63932.phase1);
        failhard = (uu___788_63932.failhard);
        nosynth = (uu___788_63932.nosynth);
        uvar_subtyping = (uu___788_63932.uvar_subtyping);
        tc_term = (uu___788_63932.tc_term);
        type_of = (uu___788_63932.type_of);
        universe_of = (uu___788_63932.universe_of);
        check_type_of = (uu___788_63932.check_type_of);
        use_bv_sorts = (uu___788_63932.use_bv_sorts);
        qtbl_name_and_index = (uu___788_63932.qtbl_name_and_index);
        normalized_eff_names = (uu___788_63932.normalized_eff_names);
        fv_delta_depths = (uu___788_63932.fv_delta_depths);
        proof_ns = (uu___788_63932.proof_ns);
        synth_hook = (uu___788_63932.synth_hook);
        splice = (uu___788_63932.splice);
        postprocess = (uu___788_63932.postprocess);
        is_native_tactic = (uu___788_63932.is_native_tactic);
        identifier_info = (uu___788_63932.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_63932.dsenv);
        nbe = (uu___788_63932.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_63944 = e  in
      let uu____63945 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_63944.solver);
        range = (uu___792_63944.range);
        curmodule = (uu___792_63944.curmodule);
        gamma = (uu___792_63944.gamma);
        gamma_sig = (uu___792_63944.gamma_sig);
        gamma_cache = (uu___792_63944.gamma_cache);
        modules = (uu___792_63944.modules);
        expected_typ = (uu___792_63944.expected_typ);
        sigtab = (uu___792_63944.sigtab);
        attrtab = (uu___792_63944.attrtab);
        is_pattern = (uu___792_63944.is_pattern);
        instantiate_imp = (uu___792_63944.instantiate_imp);
        effects = (uu___792_63944.effects);
        generalize = (uu___792_63944.generalize);
        letrecs = (uu___792_63944.letrecs);
        top_level = (uu___792_63944.top_level);
        check_uvars = (uu___792_63944.check_uvars);
        use_eq = (uu___792_63944.use_eq);
        is_iface = (uu___792_63944.is_iface);
        admit = (uu___792_63944.admit);
        lax = (uu___792_63944.lax);
        lax_universes = (uu___792_63944.lax_universes);
        phase1 = (uu___792_63944.phase1);
        failhard = (uu___792_63944.failhard);
        nosynth = (uu___792_63944.nosynth);
        uvar_subtyping = (uu___792_63944.uvar_subtyping);
        tc_term = (uu___792_63944.tc_term);
        type_of = (uu___792_63944.type_of);
        universe_of = (uu___792_63944.universe_of);
        check_type_of = (uu___792_63944.check_type_of);
        use_bv_sorts = (uu___792_63944.use_bv_sorts);
        qtbl_name_and_index = (uu___792_63944.qtbl_name_and_index);
        normalized_eff_names = (uu___792_63944.normalized_eff_names);
        fv_delta_depths = (uu___792_63944.fv_delta_depths);
        proof_ns = (uu___792_63944.proof_ns);
        synth_hook = (uu___792_63944.synth_hook);
        splice = (uu___792_63944.splice);
        postprocess = (uu___792_63944.postprocess);
        is_native_tactic = (uu___792_63944.is_native_tactic);
        identifier_info = (uu___792_63944.identifier_info);
        tc_hooks = (uu___792_63944.tc_hooks);
        dsenv = uu____63945;
        nbe = (uu___792_63944.nbe)
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
      | (NoDelta ,uu____63974) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____63977,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____63979,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____63982 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____63996 . unit -> 'Auu____63996 FStar_Util.smap =
  fun uu____64003  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____64009 . unit -> 'Auu____64009 FStar_Util.smap =
  fun uu____64016  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____64154 = new_gamma_cache ()  in
                  let uu____64157 = new_sigtab ()  in
                  let uu____64160 = new_sigtab ()  in
                  let uu____64167 =
                    let uu____64182 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____64182, FStar_Pervasives_Native.None)  in
                  let uu____64203 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____64207 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____64211 = FStar_Options.using_facts_from ()  in
                  let uu____64212 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____64215 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____64154;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____64157;
                    attrtab = uu____64160;
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
                    qtbl_name_and_index = uu____64167;
                    normalized_eff_names = uu____64203;
                    fv_delta_depths = uu____64207;
                    proof_ns = uu____64211;
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
                    is_native_tactic = (fun uu____64277  -> false);
                    identifier_info = uu____64212;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____64215;
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
  fun uu____64356  ->
    let uu____64357 = FStar_ST.op_Bang query_indices  in
    match uu____64357 with
    | [] -> failwith "Empty query indices!"
    | uu____64412 ->
        let uu____64422 =
          let uu____64432 =
            let uu____64440 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____64440  in
          let uu____64494 = FStar_ST.op_Bang query_indices  in uu____64432 ::
            uu____64494
           in
        FStar_ST.op_Colon_Equals query_indices uu____64422
  
let (pop_query_indices : unit -> unit) =
  fun uu____64590  ->
    let uu____64591 = FStar_ST.op_Bang query_indices  in
    match uu____64591 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____64718  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____64755  ->
    match uu____64755 with
    | (l,n1) ->
        let uu____64765 = FStar_ST.op_Bang query_indices  in
        (match uu____64765 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____64887 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____64910  ->
    let uu____64911 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____64911
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____64979 =
       let uu____64982 = FStar_ST.op_Bang stack  in env :: uu____64982  in
     FStar_ST.op_Colon_Equals stack uu____64979);
    (let uu___860_65031 = env  in
     let uu____65032 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____65035 = FStar_Util.smap_copy (sigtab env)  in
     let uu____65038 = FStar_Util.smap_copy (attrtab env)  in
     let uu____65045 =
       let uu____65060 =
         let uu____65064 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____65064  in
       let uu____65096 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____65060, uu____65096)  in
     let uu____65145 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____65148 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____65151 =
       let uu____65154 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____65154  in
     {
       solver = (uu___860_65031.solver);
       range = (uu___860_65031.range);
       curmodule = (uu___860_65031.curmodule);
       gamma = (uu___860_65031.gamma);
       gamma_sig = (uu___860_65031.gamma_sig);
       gamma_cache = uu____65032;
       modules = (uu___860_65031.modules);
       expected_typ = (uu___860_65031.expected_typ);
       sigtab = uu____65035;
       attrtab = uu____65038;
       is_pattern = (uu___860_65031.is_pattern);
       instantiate_imp = (uu___860_65031.instantiate_imp);
       effects = (uu___860_65031.effects);
       generalize = (uu___860_65031.generalize);
       letrecs = (uu___860_65031.letrecs);
       top_level = (uu___860_65031.top_level);
       check_uvars = (uu___860_65031.check_uvars);
       use_eq = (uu___860_65031.use_eq);
       is_iface = (uu___860_65031.is_iface);
       admit = (uu___860_65031.admit);
       lax = (uu___860_65031.lax);
       lax_universes = (uu___860_65031.lax_universes);
       phase1 = (uu___860_65031.phase1);
       failhard = (uu___860_65031.failhard);
       nosynth = (uu___860_65031.nosynth);
       uvar_subtyping = (uu___860_65031.uvar_subtyping);
       tc_term = (uu___860_65031.tc_term);
       type_of = (uu___860_65031.type_of);
       universe_of = (uu___860_65031.universe_of);
       check_type_of = (uu___860_65031.check_type_of);
       use_bv_sorts = (uu___860_65031.use_bv_sorts);
       qtbl_name_and_index = uu____65045;
       normalized_eff_names = uu____65145;
       fv_delta_depths = uu____65148;
       proof_ns = (uu___860_65031.proof_ns);
       synth_hook = (uu___860_65031.synth_hook);
       splice = (uu___860_65031.splice);
       postprocess = (uu___860_65031.postprocess);
       is_native_tactic = (uu___860_65031.is_native_tactic);
       identifier_info = uu____65151;
       tc_hooks = (uu___860_65031.tc_hooks);
       dsenv = (uu___860_65031.dsenv);
       nbe = (uu___860_65031.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____65179  ->
    let uu____65180 = FStar_ST.op_Bang stack  in
    match uu____65180 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____65234 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____65324  ->
           let uu____65325 = snapshot_stack env  in
           match uu____65325 with
           | (stack_depth,env1) ->
               let uu____65359 = snapshot_query_indices ()  in
               (match uu____65359 with
                | (query_indices_depth,()) ->
                    let uu____65392 = (env1.solver).snapshot msg  in
                    (match uu____65392 with
                     | (solver_depth,()) ->
                         let uu____65449 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____65449 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_65516 = env1  in
                                 {
                                   solver = (uu___885_65516.solver);
                                   range = (uu___885_65516.range);
                                   curmodule = (uu___885_65516.curmodule);
                                   gamma = (uu___885_65516.gamma);
                                   gamma_sig = (uu___885_65516.gamma_sig);
                                   gamma_cache = (uu___885_65516.gamma_cache);
                                   modules = (uu___885_65516.modules);
                                   expected_typ =
                                     (uu___885_65516.expected_typ);
                                   sigtab = (uu___885_65516.sigtab);
                                   attrtab = (uu___885_65516.attrtab);
                                   is_pattern = (uu___885_65516.is_pattern);
                                   instantiate_imp =
                                     (uu___885_65516.instantiate_imp);
                                   effects = (uu___885_65516.effects);
                                   generalize = (uu___885_65516.generalize);
                                   letrecs = (uu___885_65516.letrecs);
                                   top_level = (uu___885_65516.top_level);
                                   check_uvars = (uu___885_65516.check_uvars);
                                   use_eq = (uu___885_65516.use_eq);
                                   is_iface = (uu___885_65516.is_iface);
                                   admit = (uu___885_65516.admit);
                                   lax = (uu___885_65516.lax);
                                   lax_universes =
                                     (uu___885_65516.lax_universes);
                                   phase1 = (uu___885_65516.phase1);
                                   failhard = (uu___885_65516.failhard);
                                   nosynth = (uu___885_65516.nosynth);
                                   uvar_subtyping =
                                     (uu___885_65516.uvar_subtyping);
                                   tc_term = (uu___885_65516.tc_term);
                                   type_of = (uu___885_65516.type_of);
                                   universe_of = (uu___885_65516.universe_of);
                                   check_type_of =
                                     (uu___885_65516.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_65516.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_65516.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_65516.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_65516.fv_delta_depths);
                                   proof_ns = (uu___885_65516.proof_ns);
                                   synth_hook = (uu___885_65516.synth_hook);
                                   splice = (uu___885_65516.splice);
                                   postprocess = (uu___885_65516.postprocess);
                                   is_native_tactic =
                                     (uu___885_65516.is_native_tactic);
                                   identifier_info =
                                     (uu___885_65516.identifier_info);
                                   tc_hooks = (uu___885_65516.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_65516.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____65550  ->
             let uu____65551 =
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
             match uu____65551 with
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
                             ((let uu____65731 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____65731
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____65747 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____65747
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____65779,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____65821 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____65851  ->
                  match uu____65851 with
                  | (m,uu____65859) -> FStar_Ident.lid_equals l m))
           in
        (match uu____65821 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_65874 = env  in
               {
                 solver = (uu___930_65874.solver);
                 range = (uu___930_65874.range);
                 curmodule = (uu___930_65874.curmodule);
                 gamma = (uu___930_65874.gamma);
                 gamma_sig = (uu___930_65874.gamma_sig);
                 gamma_cache = (uu___930_65874.gamma_cache);
                 modules = (uu___930_65874.modules);
                 expected_typ = (uu___930_65874.expected_typ);
                 sigtab = (uu___930_65874.sigtab);
                 attrtab = (uu___930_65874.attrtab);
                 is_pattern = (uu___930_65874.is_pattern);
                 instantiate_imp = (uu___930_65874.instantiate_imp);
                 effects = (uu___930_65874.effects);
                 generalize = (uu___930_65874.generalize);
                 letrecs = (uu___930_65874.letrecs);
                 top_level = (uu___930_65874.top_level);
                 check_uvars = (uu___930_65874.check_uvars);
                 use_eq = (uu___930_65874.use_eq);
                 is_iface = (uu___930_65874.is_iface);
                 admit = (uu___930_65874.admit);
                 lax = (uu___930_65874.lax);
                 lax_universes = (uu___930_65874.lax_universes);
                 phase1 = (uu___930_65874.phase1);
                 failhard = (uu___930_65874.failhard);
                 nosynth = (uu___930_65874.nosynth);
                 uvar_subtyping = (uu___930_65874.uvar_subtyping);
                 tc_term = (uu___930_65874.tc_term);
                 type_of = (uu___930_65874.type_of);
                 universe_of = (uu___930_65874.universe_of);
                 check_type_of = (uu___930_65874.check_type_of);
                 use_bv_sorts = (uu___930_65874.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_65874.normalized_eff_names);
                 fv_delta_depths = (uu___930_65874.fv_delta_depths);
                 proof_ns = (uu___930_65874.proof_ns);
                 synth_hook = (uu___930_65874.synth_hook);
                 splice = (uu___930_65874.splice);
                 postprocess = (uu___930_65874.postprocess);
                 is_native_tactic = (uu___930_65874.is_native_tactic);
                 identifier_info = (uu___930_65874.identifier_info);
                 tc_hooks = (uu___930_65874.tc_hooks);
                 dsenv = (uu___930_65874.dsenv);
                 nbe = (uu___930_65874.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____65891,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_65907 = env  in
               {
                 solver = (uu___939_65907.solver);
                 range = (uu___939_65907.range);
                 curmodule = (uu___939_65907.curmodule);
                 gamma = (uu___939_65907.gamma);
                 gamma_sig = (uu___939_65907.gamma_sig);
                 gamma_cache = (uu___939_65907.gamma_cache);
                 modules = (uu___939_65907.modules);
                 expected_typ = (uu___939_65907.expected_typ);
                 sigtab = (uu___939_65907.sigtab);
                 attrtab = (uu___939_65907.attrtab);
                 is_pattern = (uu___939_65907.is_pattern);
                 instantiate_imp = (uu___939_65907.instantiate_imp);
                 effects = (uu___939_65907.effects);
                 generalize = (uu___939_65907.generalize);
                 letrecs = (uu___939_65907.letrecs);
                 top_level = (uu___939_65907.top_level);
                 check_uvars = (uu___939_65907.check_uvars);
                 use_eq = (uu___939_65907.use_eq);
                 is_iface = (uu___939_65907.is_iface);
                 admit = (uu___939_65907.admit);
                 lax = (uu___939_65907.lax);
                 lax_universes = (uu___939_65907.lax_universes);
                 phase1 = (uu___939_65907.phase1);
                 failhard = (uu___939_65907.failhard);
                 nosynth = (uu___939_65907.nosynth);
                 uvar_subtyping = (uu___939_65907.uvar_subtyping);
                 tc_term = (uu___939_65907.tc_term);
                 type_of = (uu___939_65907.type_of);
                 universe_of = (uu___939_65907.universe_of);
                 check_type_of = (uu___939_65907.check_type_of);
                 use_bv_sorts = (uu___939_65907.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_65907.normalized_eff_names);
                 fv_delta_depths = (uu___939_65907.fv_delta_depths);
                 proof_ns = (uu___939_65907.proof_ns);
                 synth_hook = (uu___939_65907.synth_hook);
                 splice = (uu___939_65907.splice);
                 postprocess = (uu___939_65907.postprocess);
                 is_native_tactic = (uu___939_65907.is_native_tactic);
                 identifier_info = (uu___939_65907.identifier_info);
                 tc_hooks = (uu___939_65907.tc_hooks);
                 dsenv = (uu___939_65907.dsenv);
                 nbe = (uu___939_65907.nbe)
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
        (let uu___946_65950 = e  in
         {
           solver = (uu___946_65950.solver);
           range = r;
           curmodule = (uu___946_65950.curmodule);
           gamma = (uu___946_65950.gamma);
           gamma_sig = (uu___946_65950.gamma_sig);
           gamma_cache = (uu___946_65950.gamma_cache);
           modules = (uu___946_65950.modules);
           expected_typ = (uu___946_65950.expected_typ);
           sigtab = (uu___946_65950.sigtab);
           attrtab = (uu___946_65950.attrtab);
           is_pattern = (uu___946_65950.is_pattern);
           instantiate_imp = (uu___946_65950.instantiate_imp);
           effects = (uu___946_65950.effects);
           generalize = (uu___946_65950.generalize);
           letrecs = (uu___946_65950.letrecs);
           top_level = (uu___946_65950.top_level);
           check_uvars = (uu___946_65950.check_uvars);
           use_eq = (uu___946_65950.use_eq);
           is_iface = (uu___946_65950.is_iface);
           admit = (uu___946_65950.admit);
           lax = (uu___946_65950.lax);
           lax_universes = (uu___946_65950.lax_universes);
           phase1 = (uu___946_65950.phase1);
           failhard = (uu___946_65950.failhard);
           nosynth = (uu___946_65950.nosynth);
           uvar_subtyping = (uu___946_65950.uvar_subtyping);
           tc_term = (uu___946_65950.tc_term);
           type_of = (uu___946_65950.type_of);
           universe_of = (uu___946_65950.universe_of);
           check_type_of = (uu___946_65950.check_type_of);
           use_bv_sorts = (uu___946_65950.use_bv_sorts);
           qtbl_name_and_index = (uu___946_65950.qtbl_name_and_index);
           normalized_eff_names = (uu___946_65950.normalized_eff_names);
           fv_delta_depths = (uu___946_65950.fv_delta_depths);
           proof_ns = (uu___946_65950.proof_ns);
           synth_hook = (uu___946_65950.synth_hook);
           splice = (uu___946_65950.splice);
           postprocess = (uu___946_65950.postprocess);
           is_native_tactic = (uu___946_65950.is_native_tactic);
           identifier_info = (uu___946_65950.identifier_info);
           tc_hooks = (uu___946_65950.tc_hooks);
           dsenv = (uu___946_65950.dsenv);
           nbe = (uu___946_65950.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____65970 =
        let uu____65971 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____65971 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____65970
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____66026 =
          let uu____66027 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____66027 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____66026
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____66082 =
          let uu____66083 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____66083 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____66082
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____66138 =
        let uu____66139 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____66139 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____66138
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_66203 = env  in
      {
        solver = (uu___963_66203.solver);
        range = (uu___963_66203.range);
        curmodule = lid;
        gamma = (uu___963_66203.gamma);
        gamma_sig = (uu___963_66203.gamma_sig);
        gamma_cache = (uu___963_66203.gamma_cache);
        modules = (uu___963_66203.modules);
        expected_typ = (uu___963_66203.expected_typ);
        sigtab = (uu___963_66203.sigtab);
        attrtab = (uu___963_66203.attrtab);
        is_pattern = (uu___963_66203.is_pattern);
        instantiate_imp = (uu___963_66203.instantiate_imp);
        effects = (uu___963_66203.effects);
        generalize = (uu___963_66203.generalize);
        letrecs = (uu___963_66203.letrecs);
        top_level = (uu___963_66203.top_level);
        check_uvars = (uu___963_66203.check_uvars);
        use_eq = (uu___963_66203.use_eq);
        is_iface = (uu___963_66203.is_iface);
        admit = (uu___963_66203.admit);
        lax = (uu___963_66203.lax);
        lax_universes = (uu___963_66203.lax_universes);
        phase1 = (uu___963_66203.phase1);
        failhard = (uu___963_66203.failhard);
        nosynth = (uu___963_66203.nosynth);
        uvar_subtyping = (uu___963_66203.uvar_subtyping);
        tc_term = (uu___963_66203.tc_term);
        type_of = (uu___963_66203.type_of);
        universe_of = (uu___963_66203.universe_of);
        check_type_of = (uu___963_66203.check_type_of);
        use_bv_sorts = (uu___963_66203.use_bv_sorts);
        qtbl_name_and_index = (uu___963_66203.qtbl_name_and_index);
        normalized_eff_names = (uu___963_66203.normalized_eff_names);
        fv_delta_depths = (uu___963_66203.fv_delta_depths);
        proof_ns = (uu___963_66203.proof_ns);
        synth_hook = (uu___963_66203.synth_hook);
        splice = (uu___963_66203.splice);
        postprocess = (uu___963_66203.postprocess);
        is_native_tactic = (uu___963_66203.is_native_tactic);
        identifier_info = (uu___963_66203.identifier_info);
        tc_hooks = (uu___963_66203.tc_hooks);
        dsenv = (uu___963_66203.dsenv);
        nbe = (uu___963_66203.nbe)
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
      let uu____66234 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____66234
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____66247 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____66247)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____66262 =
      let uu____66264 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____66264  in
    (FStar_Errors.Fatal_VariableNotFound, uu____66262)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____66273  ->
    let uu____66274 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____66274
  
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
      | ((formals,t),uu____66374) ->
          let vs = mk_univ_subst formals us  in
          let uu____66398 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____66398)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_66415  ->
    match uu___447_66415 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____66441  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____66461 = inst_tscheme t  in
      match uu____66461 with
      | (us,t1) ->
          let uu____66472 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____66472)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____66493  ->
          match uu____66493 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____66515 =
                         let uu____66517 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____66521 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____66525 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____66527 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____66517 uu____66521 uu____66525 uu____66527
                          in
                       failwith uu____66515)
                    else ();
                    (let uu____66532 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____66532))
               | uu____66541 ->
                   let uu____66542 =
                     let uu____66544 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____66544
                      in
                   failwith uu____66542)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____66556 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____66567 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____66578 -> false
  
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
             | ([],uu____66626) -> Maybe
             | (uu____66633,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____66653 -> No  in
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
          let uu____66747 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____66747 with
          | FStar_Pervasives_Native.None  ->
              let uu____66770 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_66814  ->
                     match uu___448_66814 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____66853 = FStar_Ident.lid_equals lid l  in
                         if uu____66853
                         then
                           let uu____66876 =
                             let uu____66895 =
                               let uu____66910 = inst_tscheme t  in
                               FStar_Util.Inl uu____66910  in
                             let uu____66925 = FStar_Ident.range_of_lid l  in
                             (uu____66895, uu____66925)  in
                           FStar_Pervasives_Native.Some uu____66876
                         else FStar_Pervasives_Native.None
                     | uu____66978 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____66770
                (fun uu____67016  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_67025  ->
                        match uu___449_67025 with
                        | (uu____67028,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____67030);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____67031;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____67032;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____67033;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____67034;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____67054 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____67054
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
                                  uu____67106 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____67113 -> cache t  in
                            let uu____67114 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____67114 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____67120 =
                                   let uu____67121 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____67121)
                                    in
                                 maybe_cache uu____67120)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____67192 = find_in_sigtab env lid  in
         match uu____67192 with
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
      let uu____67273 = lookup_qname env lid  in
      match uu____67273 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____67294,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____67408 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____67408 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____67453 =
          let uu____67456 = lookup_attr env1 attr  in se1 :: uu____67456  in
        FStar_Util.smap_add (attrtab env1) attr uu____67453  in
      FStar_List.iter
        (fun attr  ->
           let uu____67466 =
             let uu____67467 = FStar_Syntax_Subst.compress attr  in
             uu____67467.FStar_Syntax_Syntax.n  in
           match uu____67466 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____67471 =
                 let uu____67473 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____67473.FStar_Ident.str  in
               add_one1 env se uu____67471
           | uu____67474 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____67497) ->
          add_sigelts env ses
      | uu____67506 ->
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
            | uu____67521 -> ()))

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
        (fun uu___450_67553  ->
           match uu___450_67553 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____67571 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____67633,lb::[]),uu____67635) ->
            let uu____67644 =
              let uu____67653 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____67662 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____67653, uu____67662)  in
            FStar_Pervasives_Native.Some uu____67644
        | FStar_Syntax_Syntax.Sig_let ((uu____67675,lbs),uu____67677) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____67709 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____67722 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____67722
                     then
                       let uu____67735 =
                         let uu____67744 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____67753 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____67744, uu____67753)  in
                       FStar_Pervasives_Native.Some uu____67735
                     else FStar_Pervasives_Native.None)
        | uu____67776 -> FStar_Pervasives_Native.None
  
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
          let uu____67836 =
            let uu____67845 =
              let uu____67850 =
                let uu____67851 =
                  let uu____67854 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____67854
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____67851)  in
              inst_tscheme1 uu____67850  in
            (uu____67845, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67836
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____67876,uu____67877) ->
          let uu____67882 =
            let uu____67891 =
              let uu____67896 =
                let uu____67897 =
                  let uu____67900 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____67900  in
                (us, uu____67897)  in
              inst_tscheme1 uu____67896  in
            (uu____67891, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____67882
      | uu____67919 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____68008 =
          match uu____68008 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____68104,uvs,t,uu____68107,uu____68108,uu____68109);
                      FStar_Syntax_Syntax.sigrng = uu____68110;
                      FStar_Syntax_Syntax.sigquals = uu____68111;
                      FStar_Syntax_Syntax.sigmeta = uu____68112;
                      FStar_Syntax_Syntax.sigattrs = uu____68113;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____68136 =
                     let uu____68145 = inst_tscheme1 (uvs, t)  in
                     (uu____68145, rng)  in
                   FStar_Pervasives_Native.Some uu____68136
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____68169;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____68171;
                      FStar_Syntax_Syntax.sigattrs = uu____68172;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____68189 =
                     let uu____68191 = in_cur_mod env l  in uu____68191 = Yes
                      in
                   if uu____68189
                   then
                     let uu____68203 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____68203
                      then
                        let uu____68219 =
                          let uu____68228 = inst_tscheme1 (uvs, t)  in
                          (uu____68228, rng)  in
                        FStar_Pervasives_Native.Some uu____68219
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____68261 =
                        let uu____68270 = inst_tscheme1 (uvs, t)  in
                        (uu____68270, rng)  in
                      FStar_Pervasives_Native.Some uu____68261)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____68295,uu____68296);
                      FStar_Syntax_Syntax.sigrng = uu____68297;
                      FStar_Syntax_Syntax.sigquals = uu____68298;
                      FStar_Syntax_Syntax.sigmeta = uu____68299;
                      FStar_Syntax_Syntax.sigattrs = uu____68300;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____68341 =
                          let uu____68350 = inst_tscheme1 (uvs, k)  in
                          (uu____68350, rng)  in
                        FStar_Pervasives_Native.Some uu____68341
                    | uu____68371 ->
                        let uu____68372 =
                          let uu____68381 =
                            let uu____68386 =
                              let uu____68387 =
                                let uu____68390 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____68390
                                 in
                              (uvs, uu____68387)  in
                            inst_tscheme1 uu____68386  in
                          (uu____68381, rng)  in
                        FStar_Pervasives_Native.Some uu____68372)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____68413,uu____68414);
                      FStar_Syntax_Syntax.sigrng = uu____68415;
                      FStar_Syntax_Syntax.sigquals = uu____68416;
                      FStar_Syntax_Syntax.sigmeta = uu____68417;
                      FStar_Syntax_Syntax.sigattrs = uu____68418;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____68460 =
                          let uu____68469 = inst_tscheme_with (uvs, k) us  in
                          (uu____68469, rng)  in
                        FStar_Pervasives_Native.Some uu____68460
                    | uu____68490 ->
                        let uu____68491 =
                          let uu____68500 =
                            let uu____68505 =
                              let uu____68506 =
                                let uu____68509 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____68509
                                 in
                              (uvs, uu____68506)  in
                            inst_tscheme_with uu____68505 us  in
                          (uu____68500, rng)  in
                        FStar_Pervasives_Native.Some uu____68491)
               | FStar_Util.Inr se ->
                   let uu____68545 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____68566;
                          FStar_Syntax_Syntax.sigrng = uu____68567;
                          FStar_Syntax_Syntax.sigquals = uu____68568;
                          FStar_Syntax_Syntax.sigmeta = uu____68569;
                          FStar_Syntax_Syntax.sigattrs = uu____68570;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____68585 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____68545
                     (FStar_Util.map_option
                        (fun uu____68633  ->
                           match uu____68633 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____68664 =
          let uu____68675 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____68675 mapper  in
        match uu____68664 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____68749 =
              let uu____68760 =
                let uu____68767 =
                  let uu___1290_68770 = t  in
                  let uu____68771 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_68770.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____68771;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_68770.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____68767)  in
              (uu____68760, r)  in
            FStar_Pervasives_Native.Some uu____68749
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____68820 = lookup_qname env l  in
      match uu____68820 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____68841 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____68895 = try_lookup_bv env bv  in
      match uu____68895 with
      | FStar_Pervasives_Native.None  ->
          let uu____68910 = variable_not_found bv  in
          FStar_Errors.raise_error uu____68910 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____68926 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____68927 =
            let uu____68928 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____68928  in
          (uu____68926, uu____68927)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____68950 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____68950 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____69016 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____69016  in
          let uu____69017 =
            let uu____69026 =
              let uu____69031 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____69031)  in
            (uu____69026, r1)  in
          FStar_Pervasives_Native.Some uu____69017
  
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
        let uu____69066 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____69066 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____69099,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____69124 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____69124  in
            let uu____69125 =
              let uu____69130 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____69130, r1)  in
            FStar_Pervasives_Native.Some uu____69125
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____69154 = try_lookup_lid env l  in
      match uu____69154 with
      | FStar_Pervasives_Native.None  ->
          let uu____69181 = name_not_found l  in
          let uu____69187 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____69181 uu____69187
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_69230  ->
              match uu___451_69230 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____69234 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____69255 = lookup_qname env lid  in
      match uu____69255 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____69264,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____69267;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____69269;
              FStar_Syntax_Syntax.sigattrs = uu____69270;_},FStar_Pervasives_Native.None
            ),uu____69271)
          ->
          let uu____69320 =
            let uu____69327 =
              let uu____69328 =
                let uu____69331 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____69331 t  in
              (uvs, uu____69328)  in
            (uu____69327, q)  in
          FStar_Pervasives_Native.Some uu____69320
      | uu____69344 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____69366 = lookup_qname env lid  in
      match uu____69366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____69371,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____69374;
              FStar_Syntax_Syntax.sigquals = uu____69375;
              FStar_Syntax_Syntax.sigmeta = uu____69376;
              FStar_Syntax_Syntax.sigattrs = uu____69377;_},FStar_Pervasives_Native.None
            ),uu____69378)
          ->
          let uu____69427 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____69427 (uvs, t)
      | uu____69432 ->
          let uu____69433 = name_not_found lid  in
          let uu____69439 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____69433 uu____69439
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____69459 = lookup_qname env lid  in
      match uu____69459 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____69464,uvs,t,uu____69467,uu____69468,uu____69469);
              FStar_Syntax_Syntax.sigrng = uu____69470;
              FStar_Syntax_Syntax.sigquals = uu____69471;
              FStar_Syntax_Syntax.sigmeta = uu____69472;
              FStar_Syntax_Syntax.sigattrs = uu____69473;_},FStar_Pervasives_Native.None
            ),uu____69474)
          ->
          let uu____69529 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____69529 (uvs, t)
      | uu____69534 ->
          let uu____69535 = name_not_found lid  in
          let uu____69541 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____69535 uu____69541
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____69564 = lookup_qname env lid  in
      match uu____69564 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____69572,uu____69573,uu____69574,uu____69575,uu____69576,dcs);
              FStar_Syntax_Syntax.sigrng = uu____69578;
              FStar_Syntax_Syntax.sigquals = uu____69579;
              FStar_Syntax_Syntax.sigmeta = uu____69580;
              FStar_Syntax_Syntax.sigattrs = uu____69581;_},uu____69582),uu____69583)
          -> (true, dcs)
      | uu____69646 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____69662 = lookup_qname env lid  in
      match uu____69662 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____69663,uu____69664,uu____69665,l,uu____69667,uu____69668);
              FStar_Syntax_Syntax.sigrng = uu____69669;
              FStar_Syntax_Syntax.sigquals = uu____69670;
              FStar_Syntax_Syntax.sigmeta = uu____69671;
              FStar_Syntax_Syntax.sigattrs = uu____69672;_},uu____69673),uu____69674)
          -> l
      | uu____69731 ->
          let uu____69732 =
            let uu____69734 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____69734  in
          failwith uu____69732
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____69804)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____69861) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____69885 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____69885
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____69920 -> FStar_Pervasives_Native.None)
          | uu____69929 -> FStar_Pervasives_Native.None
  
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
        let uu____69991 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____69991
  
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
        let uu____70024 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____70024
  
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
             (FStar_Util.Inl uu____70076,uu____70077) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____70126),uu____70127) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____70176 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____70194 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____70204 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____70221 ->
                  let uu____70228 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____70228
              | FStar_Syntax_Syntax.Sig_let ((uu____70229,lbs),uu____70231)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____70247 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____70247
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____70254 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____70262 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____70263 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____70270 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____70271 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____70272 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____70273 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____70286 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____70304 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____70304
           (fun d_opt  ->
              let uu____70317 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____70317
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____70327 =
                   let uu____70330 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____70330  in
                 match uu____70327 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____70331 =
                       let uu____70333 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____70333
                        in
                     failwith uu____70331
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____70338 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____70338
                       then
                         let uu____70341 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____70343 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____70345 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____70341 uu____70343 uu____70345
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
        (FStar_Util.Inr (se,uu____70370),uu____70371) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____70420 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____70442),uu____70443) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____70492 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____70514 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____70514
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____70537 = lookup_attrs_of_lid env fv_lid1  in
        match uu____70537 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____70561 =
                      let uu____70562 = FStar_Syntax_Util.un_uinst tm  in
                      uu____70562.FStar_Syntax_Syntax.n  in
                    match uu____70561 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____70567 -> false))
  
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
      let uu____70601 = lookup_qname env ftv  in
      match uu____70601 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____70605) ->
          let uu____70650 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____70650 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____70671,t),r) ->
               let uu____70686 =
                 let uu____70687 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____70687 t  in
               FStar_Pervasives_Native.Some uu____70686)
      | uu____70688 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____70700 = try_lookup_effect_lid env ftv  in
      match uu____70700 with
      | FStar_Pervasives_Native.None  ->
          let uu____70703 = name_not_found ftv  in
          let uu____70709 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____70703 uu____70709
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
        let uu____70733 = lookup_qname env lid0  in
        match uu____70733 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____70744);
                FStar_Syntax_Syntax.sigrng = uu____70745;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____70747;
                FStar_Syntax_Syntax.sigattrs = uu____70748;_},FStar_Pervasives_Native.None
              ),uu____70749)
            ->
            let lid1 =
              let uu____70803 =
                let uu____70804 = FStar_Ident.range_of_lid lid  in
                let uu____70805 =
                  let uu____70806 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____70806  in
                FStar_Range.set_use_range uu____70804 uu____70805  in
              FStar_Ident.set_lid_range lid uu____70803  in
            let uu____70807 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_70813  ->
                      match uu___452_70813 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____70816 -> false))
               in
            if uu____70807
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____70835 =
                      let uu____70837 =
                        let uu____70839 = get_range env  in
                        FStar_Range.string_of_range uu____70839  in
                      let uu____70840 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____70842 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____70837 uu____70840 uu____70842
                       in
                    failwith uu____70835)
                  in
               match (binders, univs1) with
               | ([],uu____70863) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____70889,uu____70890::uu____70891::uu____70892) ->
                   let uu____70913 =
                     let uu____70915 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____70917 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____70915 uu____70917
                      in
                   failwith uu____70913
               | uu____70928 ->
                   let uu____70943 =
                     let uu____70948 =
                       let uu____70949 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____70949)  in
                     inst_tscheme_with uu____70948 insts  in
                   (match uu____70943 with
                    | (uu____70962,t) ->
                        let t1 =
                          let uu____70965 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____70965 t  in
                        let uu____70966 =
                          let uu____70967 = FStar_Syntax_Subst.compress t1
                             in
                          uu____70967.FStar_Syntax_Syntax.n  in
                        (match uu____70966 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____71002 -> failwith "Impossible")))
        | uu____71010 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____71034 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____71034 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____71047,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____71054 = find1 l2  in
            (match uu____71054 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____71061 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____71061 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____71065 = find1 l  in
            (match uu____71065 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____71070 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____71070
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____71085 = lookup_qname env l1  in
      match uu____71085 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____71088;
              FStar_Syntax_Syntax.sigrng = uu____71089;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____71091;
              FStar_Syntax_Syntax.sigattrs = uu____71092;_},uu____71093),uu____71094)
          -> q
      | uu____71145 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____71169 =
          let uu____71170 =
            let uu____71172 = FStar_Util.string_of_int i  in
            let uu____71174 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____71172 uu____71174
             in
          failwith uu____71170  in
        let uu____71177 = lookup_datacon env lid  in
        match uu____71177 with
        | (uu____71182,t) ->
            let uu____71184 =
              let uu____71185 = FStar_Syntax_Subst.compress t  in
              uu____71185.FStar_Syntax_Syntax.n  in
            (match uu____71184 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____71189) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____71233 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____71233
                      FStar_Pervasives_Native.fst)
             | uu____71244 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____71258 = lookup_qname env l  in
      match uu____71258 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____71260,uu____71261,uu____71262);
              FStar_Syntax_Syntax.sigrng = uu____71263;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____71265;
              FStar_Syntax_Syntax.sigattrs = uu____71266;_},uu____71267),uu____71268)
          ->
          FStar_Util.for_some
            (fun uu___453_71321  ->
               match uu___453_71321 with
               | FStar_Syntax_Syntax.Projector uu____71323 -> true
               | uu____71329 -> false) quals
      | uu____71331 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____71345 = lookup_qname env lid  in
      match uu____71345 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____71347,uu____71348,uu____71349,uu____71350,uu____71351,uu____71352);
              FStar_Syntax_Syntax.sigrng = uu____71353;
              FStar_Syntax_Syntax.sigquals = uu____71354;
              FStar_Syntax_Syntax.sigmeta = uu____71355;
              FStar_Syntax_Syntax.sigattrs = uu____71356;_},uu____71357),uu____71358)
          -> true
      | uu____71416 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____71430 = lookup_qname env lid  in
      match uu____71430 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71432,uu____71433,uu____71434,uu____71435,uu____71436,uu____71437);
              FStar_Syntax_Syntax.sigrng = uu____71438;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____71440;
              FStar_Syntax_Syntax.sigattrs = uu____71441;_},uu____71442),uu____71443)
          ->
          FStar_Util.for_some
            (fun uu___454_71504  ->
               match uu___454_71504 with
               | FStar_Syntax_Syntax.RecordType uu____71506 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____71516 -> true
               | uu____71526 -> false) quals
      | uu____71528 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____71538,uu____71539);
            FStar_Syntax_Syntax.sigrng = uu____71540;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____71542;
            FStar_Syntax_Syntax.sigattrs = uu____71543;_},uu____71544),uu____71545)
        ->
        FStar_Util.for_some
          (fun uu___455_71602  ->
             match uu___455_71602 with
             | FStar_Syntax_Syntax.Action uu____71604 -> true
             | uu____71606 -> false) quals
    | uu____71608 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____71622 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____71622
  
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
      let uu____71639 =
        let uu____71640 = FStar_Syntax_Util.un_uinst head1  in
        uu____71640.FStar_Syntax_Syntax.n  in
      match uu____71639 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____71646 ->
               true
           | uu____71649 -> false)
      | uu____71651 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____71665 = lookup_qname env l  in
      match uu____71665 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____71668),uu____71669) ->
          FStar_Util.for_some
            (fun uu___456_71717  ->
               match uu___456_71717 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____71720 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____71722 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____71798 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____71816) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____71834 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____71842 ->
                 FStar_Pervasives_Native.Some true
             | uu____71861 -> FStar_Pervasives_Native.Some false)
         in
      let uu____71864 =
        let uu____71868 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____71868 mapper  in
      match uu____71864 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____71928 = lookup_qname env lid  in
      match uu____71928 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____71932,uu____71933,tps,uu____71935,uu____71936,uu____71937);
              FStar_Syntax_Syntax.sigrng = uu____71938;
              FStar_Syntax_Syntax.sigquals = uu____71939;
              FStar_Syntax_Syntax.sigmeta = uu____71940;
              FStar_Syntax_Syntax.sigattrs = uu____71941;_},uu____71942),uu____71943)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____72009 -> FStar_Pervasives_Native.None
  
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
           (fun uu____72055  ->
              match uu____72055 with
              | (d,uu____72064) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____72080 = effect_decl_opt env l  in
      match uu____72080 with
      | FStar_Pervasives_Native.None  ->
          let uu____72095 = name_not_found l  in
          let uu____72101 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____72095 uu____72101
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____72124  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____72143  ->
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
        let uu____72175 = FStar_Ident.lid_equals l1 l2  in
        if uu____72175
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____72186 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____72186
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____72197 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____72250  ->
                        match uu____72250 with
                        | (m1,m2,uu____72264,uu____72265,uu____72266) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____72197 with
              | FStar_Pervasives_Native.None  ->
                  let uu____72283 =
                    let uu____72289 =
                      let uu____72291 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____72293 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____72291
                        uu____72293
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____72289)
                     in
                  FStar_Errors.raise_error uu____72283 env.range
              | FStar_Pervasives_Native.Some
                  (uu____72303,uu____72304,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____72338 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____72338
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
  'Auu____72358 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____72358) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____72387 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____72413  ->
                match uu____72413 with
                | (d,uu____72420) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____72387 with
      | FStar_Pervasives_Native.None  ->
          let uu____72431 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____72431
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____72446 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____72446 with
           | (uu____72461,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____72479)::(wp,uu____72481)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____72537 -> failwith "Impossible"))
  
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
          let uu____72595 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____72595
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____72600 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____72600
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
                  let uu____72611 = get_range env  in
                  let uu____72612 =
                    let uu____72619 =
                      let uu____72620 =
                        let uu____72637 =
                          let uu____72648 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____72648]  in
                        (null_wp, uu____72637)  in
                      FStar_Syntax_Syntax.Tm_app uu____72620  in
                    FStar_Syntax_Syntax.mk uu____72619  in
                  uu____72612 FStar_Pervasives_Native.None uu____72611  in
                let uu____72685 =
                  let uu____72686 =
                    let uu____72697 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____72697]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____72686;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____72685))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_72735 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_72735.order);
              joins = (uu___1944_72735.joins)
            }  in
          let uu___1947_72744 = env  in
          {
            solver = (uu___1947_72744.solver);
            range = (uu___1947_72744.range);
            curmodule = (uu___1947_72744.curmodule);
            gamma = (uu___1947_72744.gamma);
            gamma_sig = (uu___1947_72744.gamma_sig);
            gamma_cache = (uu___1947_72744.gamma_cache);
            modules = (uu___1947_72744.modules);
            expected_typ = (uu___1947_72744.expected_typ);
            sigtab = (uu___1947_72744.sigtab);
            attrtab = (uu___1947_72744.attrtab);
            is_pattern = (uu___1947_72744.is_pattern);
            instantiate_imp = (uu___1947_72744.instantiate_imp);
            effects;
            generalize = (uu___1947_72744.generalize);
            letrecs = (uu___1947_72744.letrecs);
            top_level = (uu___1947_72744.top_level);
            check_uvars = (uu___1947_72744.check_uvars);
            use_eq = (uu___1947_72744.use_eq);
            is_iface = (uu___1947_72744.is_iface);
            admit = (uu___1947_72744.admit);
            lax = (uu___1947_72744.lax);
            lax_universes = (uu___1947_72744.lax_universes);
            phase1 = (uu___1947_72744.phase1);
            failhard = (uu___1947_72744.failhard);
            nosynth = (uu___1947_72744.nosynth);
            uvar_subtyping = (uu___1947_72744.uvar_subtyping);
            tc_term = (uu___1947_72744.tc_term);
            type_of = (uu___1947_72744.type_of);
            universe_of = (uu___1947_72744.universe_of);
            check_type_of = (uu___1947_72744.check_type_of);
            use_bv_sorts = (uu___1947_72744.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_72744.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_72744.normalized_eff_names);
            fv_delta_depths = (uu___1947_72744.fv_delta_depths);
            proof_ns = (uu___1947_72744.proof_ns);
            synth_hook = (uu___1947_72744.synth_hook);
            splice = (uu___1947_72744.splice);
            postprocess = (uu___1947_72744.postprocess);
            is_native_tactic = (uu___1947_72744.is_native_tactic);
            identifier_info = (uu___1947_72744.identifier_info);
            tc_hooks = (uu___1947_72744.tc_hooks);
            dsenv = (uu___1947_72744.dsenv);
            nbe = (uu___1947_72744.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____72774 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____72774  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____72932 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____72933 = l1 u t wp e  in
                                l2 u t uu____72932 uu____72933))
                | uu____72934 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____73006 = inst_tscheme_with lift_t [u]  in
            match uu____73006 with
            | (uu____73013,lift_t1) ->
                let uu____73015 =
                  let uu____73022 =
                    let uu____73023 =
                      let uu____73040 =
                        let uu____73051 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____73060 =
                          let uu____73071 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____73071]  in
                        uu____73051 :: uu____73060  in
                      (lift_t1, uu____73040)  in
                    FStar_Syntax_Syntax.Tm_app uu____73023  in
                  FStar_Syntax_Syntax.mk uu____73022  in
                uu____73015 FStar_Pervasives_Native.None
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
            let uu____73181 = inst_tscheme_with lift_t [u]  in
            match uu____73181 with
            | (uu____73188,lift_t1) ->
                let uu____73190 =
                  let uu____73197 =
                    let uu____73198 =
                      let uu____73215 =
                        let uu____73226 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____73235 =
                          let uu____73246 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____73255 =
                            let uu____73266 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____73266]  in
                          uu____73246 :: uu____73255  in
                        uu____73226 :: uu____73235  in
                      (lift_t1, uu____73215)  in
                    FStar_Syntax_Syntax.Tm_app uu____73198  in
                  FStar_Syntax_Syntax.mk uu____73197  in
                uu____73190 FStar_Pervasives_Native.None
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
              let uu____73368 =
                let uu____73369 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____73369
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____73368  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____73378 =
              let uu____73380 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____73380  in
            let uu____73381 =
              let uu____73383 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____73411 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____73411)
                 in
              FStar_Util.dflt "none" uu____73383  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____73378
              uu____73381
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____73440  ->
                    match uu____73440 with
                    | (e,uu____73448) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____73471 =
            match uu____73471 with
            | (i,j) ->
                let uu____73482 = FStar_Ident.lid_equals i j  in
                if uu____73482
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _73489  -> FStar_Pervasives_Native.Some _73489)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____73518 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____73528 = FStar_Ident.lid_equals i k  in
                        if uu____73528
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____73542 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____73542
                                  then []
                                  else
                                    (let uu____73549 =
                                       let uu____73558 =
                                         find_edge order1 (i, k)  in
                                       let uu____73561 =
                                         find_edge order1 (k, j)  in
                                       (uu____73558, uu____73561)  in
                                     match uu____73549 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____73576 =
                                           compose_edges e1 e2  in
                                         [uu____73576]
                                     | uu____73577 -> [])))))
                 in
              FStar_List.append order1 uu____73518  in
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
                   let uu____73607 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____73610 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____73610
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____73607
                   then
                     let uu____73617 =
                       let uu____73623 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____73623)
                        in
                     let uu____73627 = get_range env  in
                     FStar_Errors.raise_error uu____73617 uu____73627
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____73705 = FStar_Ident.lid_equals i j
                                   in
                                if uu____73705
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____73757 =
                                              let uu____73766 =
                                                find_edge order2 (i, k)  in
                                              let uu____73769 =
                                                find_edge order2 (j, k)  in
                                              (uu____73766, uu____73769)  in
                                            match uu____73757 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____73811,uu____73812)
                                                     ->
                                                     let uu____73819 =
                                                       let uu____73826 =
                                                         let uu____73828 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73828
                                                          in
                                                       let uu____73831 =
                                                         let uu____73833 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____73833
                                                          in
                                                       (uu____73826,
                                                         uu____73831)
                                                        in
                                                     (match uu____73819 with
                                                      | (true ,true ) ->
                                                          let uu____73850 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____73850
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
                                            | uu____73893 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_73966 = env.effects  in
              { decls = (uu___2074_73966.decls); order = order2; joins }  in
            let uu___2077_73967 = env  in
            {
              solver = (uu___2077_73967.solver);
              range = (uu___2077_73967.range);
              curmodule = (uu___2077_73967.curmodule);
              gamma = (uu___2077_73967.gamma);
              gamma_sig = (uu___2077_73967.gamma_sig);
              gamma_cache = (uu___2077_73967.gamma_cache);
              modules = (uu___2077_73967.modules);
              expected_typ = (uu___2077_73967.expected_typ);
              sigtab = (uu___2077_73967.sigtab);
              attrtab = (uu___2077_73967.attrtab);
              is_pattern = (uu___2077_73967.is_pattern);
              instantiate_imp = (uu___2077_73967.instantiate_imp);
              effects;
              generalize = (uu___2077_73967.generalize);
              letrecs = (uu___2077_73967.letrecs);
              top_level = (uu___2077_73967.top_level);
              check_uvars = (uu___2077_73967.check_uvars);
              use_eq = (uu___2077_73967.use_eq);
              is_iface = (uu___2077_73967.is_iface);
              admit = (uu___2077_73967.admit);
              lax = (uu___2077_73967.lax);
              lax_universes = (uu___2077_73967.lax_universes);
              phase1 = (uu___2077_73967.phase1);
              failhard = (uu___2077_73967.failhard);
              nosynth = (uu___2077_73967.nosynth);
              uvar_subtyping = (uu___2077_73967.uvar_subtyping);
              tc_term = (uu___2077_73967.tc_term);
              type_of = (uu___2077_73967.type_of);
              universe_of = (uu___2077_73967.universe_of);
              check_type_of = (uu___2077_73967.check_type_of);
              use_bv_sorts = (uu___2077_73967.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_73967.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_73967.normalized_eff_names);
              fv_delta_depths = (uu___2077_73967.fv_delta_depths);
              proof_ns = (uu___2077_73967.proof_ns);
              synth_hook = (uu___2077_73967.synth_hook);
              splice = (uu___2077_73967.splice);
              postprocess = (uu___2077_73967.postprocess);
              is_native_tactic = (uu___2077_73967.is_native_tactic);
              identifier_info = (uu___2077_73967.identifier_info);
              tc_hooks = (uu___2077_73967.tc_hooks);
              dsenv = (uu___2077_73967.dsenv);
              nbe = (uu___2077_73967.nbe)
            }))
      | uu____73968 -> env
  
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
        | uu____73997 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____74010 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____74010 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____74027 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____74027 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____74052 =
                     let uu____74058 =
                       let uu____74060 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____74068 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____74079 =
                         let uu____74081 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____74081  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____74060 uu____74068 uu____74079
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____74058)
                      in
                   FStar_Errors.raise_error uu____74052
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____74089 =
                     let uu____74100 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____74100 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____74137  ->
                        fun uu____74138  ->
                          match (uu____74137, uu____74138) with
                          | ((x,uu____74168),(t,uu____74170)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____74089
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____74201 =
                     let uu___2115_74202 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_74202.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_74202.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_74202.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_74202.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____74201
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____74214 .
    'Auu____74214 ->
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
          let uu____74244 = effect_decl_opt env effect_name  in
          match uu____74244 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____74283 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____74306 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____74345 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____74345
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____74350 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____74350
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____74365 =
                     let uu____74368 = get_range env  in
                     let uu____74369 =
                       let uu____74376 =
                         let uu____74377 =
                           let uu____74394 =
                             let uu____74405 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____74405; wp]  in
                           (repr, uu____74394)  in
                         FStar_Syntax_Syntax.Tm_app uu____74377  in
                       FStar_Syntax_Syntax.mk uu____74376  in
                     uu____74369 FStar_Pervasives_Native.None uu____74368  in
                   FStar_Pervasives_Native.Some uu____74365)
  
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
      | uu____74549 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____74564 =
        let uu____74565 = FStar_Syntax_Subst.compress t  in
        uu____74565.FStar_Syntax_Syntax.n  in
      match uu____74564 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____74569,c) ->
          is_reifiable_comp env c
      | uu____74591 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____74611 =
           let uu____74613 = is_reifiable_effect env l  in
           Prims.op_Negation uu____74613  in
         if uu____74611
         then
           let uu____74616 =
             let uu____74622 =
               let uu____74624 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____74624
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____74622)  in
           let uu____74628 = get_range env  in
           FStar_Errors.raise_error uu____74616 uu____74628
         else ());
        (let uu____74631 = effect_repr_aux true env c u_c  in
         match uu____74631 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_74667 = env  in
        {
          solver = (uu___2180_74667.solver);
          range = (uu___2180_74667.range);
          curmodule = (uu___2180_74667.curmodule);
          gamma = (uu___2180_74667.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_74667.gamma_cache);
          modules = (uu___2180_74667.modules);
          expected_typ = (uu___2180_74667.expected_typ);
          sigtab = (uu___2180_74667.sigtab);
          attrtab = (uu___2180_74667.attrtab);
          is_pattern = (uu___2180_74667.is_pattern);
          instantiate_imp = (uu___2180_74667.instantiate_imp);
          effects = (uu___2180_74667.effects);
          generalize = (uu___2180_74667.generalize);
          letrecs = (uu___2180_74667.letrecs);
          top_level = (uu___2180_74667.top_level);
          check_uvars = (uu___2180_74667.check_uvars);
          use_eq = (uu___2180_74667.use_eq);
          is_iface = (uu___2180_74667.is_iface);
          admit = (uu___2180_74667.admit);
          lax = (uu___2180_74667.lax);
          lax_universes = (uu___2180_74667.lax_universes);
          phase1 = (uu___2180_74667.phase1);
          failhard = (uu___2180_74667.failhard);
          nosynth = (uu___2180_74667.nosynth);
          uvar_subtyping = (uu___2180_74667.uvar_subtyping);
          tc_term = (uu___2180_74667.tc_term);
          type_of = (uu___2180_74667.type_of);
          universe_of = (uu___2180_74667.universe_of);
          check_type_of = (uu___2180_74667.check_type_of);
          use_bv_sorts = (uu___2180_74667.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_74667.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_74667.normalized_eff_names);
          fv_delta_depths = (uu___2180_74667.fv_delta_depths);
          proof_ns = (uu___2180_74667.proof_ns);
          synth_hook = (uu___2180_74667.synth_hook);
          splice = (uu___2180_74667.splice);
          postprocess = (uu___2180_74667.postprocess);
          is_native_tactic = (uu___2180_74667.is_native_tactic);
          identifier_info = (uu___2180_74667.identifier_info);
          tc_hooks = (uu___2180_74667.tc_hooks);
          dsenv = (uu___2180_74667.dsenv);
          nbe = (uu___2180_74667.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_74681 = env  in
      {
        solver = (uu___2187_74681.solver);
        range = (uu___2187_74681.range);
        curmodule = (uu___2187_74681.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_74681.gamma_sig);
        gamma_cache = (uu___2187_74681.gamma_cache);
        modules = (uu___2187_74681.modules);
        expected_typ = (uu___2187_74681.expected_typ);
        sigtab = (uu___2187_74681.sigtab);
        attrtab = (uu___2187_74681.attrtab);
        is_pattern = (uu___2187_74681.is_pattern);
        instantiate_imp = (uu___2187_74681.instantiate_imp);
        effects = (uu___2187_74681.effects);
        generalize = (uu___2187_74681.generalize);
        letrecs = (uu___2187_74681.letrecs);
        top_level = (uu___2187_74681.top_level);
        check_uvars = (uu___2187_74681.check_uvars);
        use_eq = (uu___2187_74681.use_eq);
        is_iface = (uu___2187_74681.is_iface);
        admit = (uu___2187_74681.admit);
        lax = (uu___2187_74681.lax);
        lax_universes = (uu___2187_74681.lax_universes);
        phase1 = (uu___2187_74681.phase1);
        failhard = (uu___2187_74681.failhard);
        nosynth = (uu___2187_74681.nosynth);
        uvar_subtyping = (uu___2187_74681.uvar_subtyping);
        tc_term = (uu___2187_74681.tc_term);
        type_of = (uu___2187_74681.type_of);
        universe_of = (uu___2187_74681.universe_of);
        check_type_of = (uu___2187_74681.check_type_of);
        use_bv_sorts = (uu___2187_74681.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_74681.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_74681.normalized_eff_names);
        fv_delta_depths = (uu___2187_74681.fv_delta_depths);
        proof_ns = (uu___2187_74681.proof_ns);
        synth_hook = (uu___2187_74681.synth_hook);
        splice = (uu___2187_74681.splice);
        postprocess = (uu___2187_74681.postprocess);
        is_native_tactic = (uu___2187_74681.is_native_tactic);
        identifier_info = (uu___2187_74681.identifier_info);
        tc_hooks = (uu___2187_74681.tc_hooks);
        dsenv = (uu___2187_74681.dsenv);
        nbe = (uu___2187_74681.nbe)
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
            (let uu___2200_74739 = env  in
             {
               solver = (uu___2200_74739.solver);
               range = (uu___2200_74739.range);
               curmodule = (uu___2200_74739.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_74739.gamma_sig);
               gamma_cache = (uu___2200_74739.gamma_cache);
               modules = (uu___2200_74739.modules);
               expected_typ = (uu___2200_74739.expected_typ);
               sigtab = (uu___2200_74739.sigtab);
               attrtab = (uu___2200_74739.attrtab);
               is_pattern = (uu___2200_74739.is_pattern);
               instantiate_imp = (uu___2200_74739.instantiate_imp);
               effects = (uu___2200_74739.effects);
               generalize = (uu___2200_74739.generalize);
               letrecs = (uu___2200_74739.letrecs);
               top_level = (uu___2200_74739.top_level);
               check_uvars = (uu___2200_74739.check_uvars);
               use_eq = (uu___2200_74739.use_eq);
               is_iface = (uu___2200_74739.is_iface);
               admit = (uu___2200_74739.admit);
               lax = (uu___2200_74739.lax);
               lax_universes = (uu___2200_74739.lax_universes);
               phase1 = (uu___2200_74739.phase1);
               failhard = (uu___2200_74739.failhard);
               nosynth = (uu___2200_74739.nosynth);
               uvar_subtyping = (uu___2200_74739.uvar_subtyping);
               tc_term = (uu___2200_74739.tc_term);
               type_of = (uu___2200_74739.type_of);
               universe_of = (uu___2200_74739.universe_of);
               check_type_of = (uu___2200_74739.check_type_of);
               use_bv_sorts = (uu___2200_74739.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_74739.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_74739.normalized_eff_names);
               fv_delta_depths = (uu___2200_74739.fv_delta_depths);
               proof_ns = (uu___2200_74739.proof_ns);
               synth_hook = (uu___2200_74739.synth_hook);
               splice = (uu___2200_74739.splice);
               postprocess = (uu___2200_74739.postprocess);
               is_native_tactic = (uu___2200_74739.is_native_tactic);
               identifier_info = (uu___2200_74739.identifier_info);
               tc_hooks = (uu___2200_74739.tc_hooks);
               dsenv = (uu___2200_74739.dsenv);
               nbe = (uu___2200_74739.nbe)
             }))
    | uu____74740 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____74769  ->
             match uu____74769 with | (x,uu____74777) -> push_bv env1 x) env
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
            let uu___2214_74812 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_74812.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_74812.FStar_Syntax_Syntax.index);
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
      (let uu___2225_74854 = env  in
       {
         solver = (uu___2225_74854.solver);
         range = (uu___2225_74854.range);
         curmodule = (uu___2225_74854.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_74854.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_74854.sigtab);
         attrtab = (uu___2225_74854.attrtab);
         is_pattern = (uu___2225_74854.is_pattern);
         instantiate_imp = (uu___2225_74854.instantiate_imp);
         effects = (uu___2225_74854.effects);
         generalize = (uu___2225_74854.generalize);
         letrecs = (uu___2225_74854.letrecs);
         top_level = (uu___2225_74854.top_level);
         check_uvars = (uu___2225_74854.check_uvars);
         use_eq = (uu___2225_74854.use_eq);
         is_iface = (uu___2225_74854.is_iface);
         admit = (uu___2225_74854.admit);
         lax = (uu___2225_74854.lax);
         lax_universes = (uu___2225_74854.lax_universes);
         phase1 = (uu___2225_74854.phase1);
         failhard = (uu___2225_74854.failhard);
         nosynth = (uu___2225_74854.nosynth);
         uvar_subtyping = (uu___2225_74854.uvar_subtyping);
         tc_term = (uu___2225_74854.tc_term);
         type_of = (uu___2225_74854.type_of);
         universe_of = (uu___2225_74854.universe_of);
         check_type_of = (uu___2225_74854.check_type_of);
         use_bv_sorts = (uu___2225_74854.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_74854.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_74854.normalized_eff_names);
         fv_delta_depths = (uu___2225_74854.fv_delta_depths);
         proof_ns = (uu___2225_74854.proof_ns);
         synth_hook = (uu___2225_74854.synth_hook);
         splice = (uu___2225_74854.splice);
         postprocess = (uu___2225_74854.postprocess);
         is_native_tactic = (uu___2225_74854.is_native_tactic);
         identifier_info = (uu___2225_74854.identifier_info);
         tc_hooks = (uu___2225_74854.tc_hooks);
         dsenv = (uu___2225_74854.dsenv);
         nbe = (uu___2225_74854.nbe)
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
        let uu____74898 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____74898 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____74926 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____74926)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_74942 = env  in
      {
        solver = (uu___2240_74942.solver);
        range = (uu___2240_74942.range);
        curmodule = (uu___2240_74942.curmodule);
        gamma = (uu___2240_74942.gamma);
        gamma_sig = (uu___2240_74942.gamma_sig);
        gamma_cache = (uu___2240_74942.gamma_cache);
        modules = (uu___2240_74942.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_74942.sigtab);
        attrtab = (uu___2240_74942.attrtab);
        is_pattern = (uu___2240_74942.is_pattern);
        instantiate_imp = (uu___2240_74942.instantiate_imp);
        effects = (uu___2240_74942.effects);
        generalize = (uu___2240_74942.generalize);
        letrecs = (uu___2240_74942.letrecs);
        top_level = (uu___2240_74942.top_level);
        check_uvars = (uu___2240_74942.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_74942.is_iface);
        admit = (uu___2240_74942.admit);
        lax = (uu___2240_74942.lax);
        lax_universes = (uu___2240_74942.lax_universes);
        phase1 = (uu___2240_74942.phase1);
        failhard = (uu___2240_74942.failhard);
        nosynth = (uu___2240_74942.nosynth);
        uvar_subtyping = (uu___2240_74942.uvar_subtyping);
        tc_term = (uu___2240_74942.tc_term);
        type_of = (uu___2240_74942.type_of);
        universe_of = (uu___2240_74942.universe_of);
        check_type_of = (uu___2240_74942.check_type_of);
        use_bv_sorts = (uu___2240_74942.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_74942.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_74942.normalized_eff_names);
        fv_delta_depths = (uu___2240_74942.fv_delta_depths);
        proof_ns = (uu___2240_74942.proof_ns);
        synth_hook = (uu___2240_74942.synth_hook);
        splice = (uu___2240_74942.splice);
        postprocess = (uu___2240_74942.postprocess);
        is_native_tactic = (uu___2240_74942.is_native_tactic);
        identifier_info = (uu___2240_74942.identifier_info);
        tc_hooks = (uu___2240_74942.tc_hooks);
        dsenv = (uu___2240_74942.dsenv);
        nbe = (uu___2240_74942.nbe)
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
    let uu____74973 = expected_typ env_  in
    ((let uu___2247_74979 = env_  in
      {
        solver = (uu___2247_74979.solver);
        range = (uu___2247_74979.range);
        curmodule = (uu___2247_74979.curmodule);
        gamma = (uu___2247_74979.gamma);
        gamma_sig = (uu___2247_74979.gamma_sig);
        gamma_cache = (uu___2247_74979.gamma_cache);
        modules = (uu___2247_74979.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_74979.sigtab);
        attrtab = (uu___2247_74979.attrtab);
        is_pattern = (uu___2247_74979.is_pattern);
        instantiate_imp = (uu___2247_74979.instantiate_imp);
        effects = (uu___2247_74979.effects);
        generalize = (uu___2247_74979.generalize);
        letrecs = (uu___2247_74979.letrecs);
        top_level = (uu___2247_74979.top_level);
        check_uvars = (uu___2247_74979.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_74979.is_iface);
        admit = (uu___2247_74979.admit);
        lax = (uu___2247_74979.lax);
        lax_universes = (uu___2247_74979.lax_universes);
        phase1 = (uu___2247_74979.phase1);
        failhard = (uu___2247_74979.failhard);
        nosynth = (uu___2247_74979.nosynth);
        uvar_subtyping = (uu___2247_74979.uvar_subtyping);
        tc_term = (uu___2247_74979.tc_term);
        type_of = (uu___2247_74979.type_of);
        universe_of = (uu___2247_74979.universe_of);
        check_type_of = (uu___2247_74979.check_type_of);
        use_bv_sorts = (uu___2247_74979.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_74979.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_74979.normalized_eff_names);
        fv_delta_depths = (uu___2247_74979.fv_delta_depths);
        proof_ns = (uu___2247_74979.proof_ns);
        synth_hook = (uu___2247_74979.synth_hook);
        splice = (uu___2247_74979.splice);
        postprocess = (uu___2247_74979.postprocess);
        is_native_tactic = (uu___2247_74979.is_native_tactic);
        identifier_info = (uu___2247_74979.identifier_info);
        tc_hooks = (uu___2247_74979.tc_hooks);
        dsenv = (uu___2247_74979.dsenv);
        nbe = (uu___2247_74979.nbe)
      }), uu____74973)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____74991 =
      let uu____74994 = FStar_Ident.id_of_text ""  in [uu____74994]  in
    FStar_Ident.lid_of_ids uu____74991  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____75001 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____75001
        then
          let uu____75006 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____75006 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_75034 = env  in
       {
         solver = (uu___2255_75034.solver);
         range = (uu___2255_75034.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_75034.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_75034.expected_typ);
         sigtab = (uu___2255_75034.sigtab);
         attrtab = (uu___2255_75034.attrtab);
         is_pattern = (uu___2255_75034.is_pattern);
         instantiate_imp = (uu___2255_75034.instantiate_imp);
         effects = (uu___2255_75034.effects);
         generalize = (uu___2255_75034.generalize);
         letrecs = (uu___2255_75034.letrecs);
         top_level = (uu___2255_75034.top_level);
         check_uvars = (uu___2255_75034.check_uvars);
         use_eq = (uu___2255_75034.use_eq);
         is_iface = (uu___2255_75034.is_iface);
         admit = (uu___2255_75034.admit);
         lax = (uu___2255_75034.lax);
         lax_universes = (uu___2255_75034.lax_universes);
         phase1 = (uu___2255_75034.phase1);
         failhard = (uu___2255_75034.failhard);
         nosynth = (uu___2255_75034.nosynth);
         uvar_subtyping = (uu___2255_75034.uvar_subtyping);
         tc_term = (uu___2255_75034.tc_term);
         type_of = (uu___2255_75034.type_of);
         universe_of = (uu___2255_75034.universe_of);
         check_type_of = (uu___2255_75034.check_type_of);
         use_bv_sorts = (uu___2255_75034.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_75034.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_75034.normalized_eff_names);
         fv_delta_depths = (uu___2255_75034.fv_delta_depths);
         proof_ns = (uu___2255_75034.proof_ns);
         synth_hook = (uu___2255_75034.synth_hook);
         splice = (uu___2255_75034.splice);
         postprocess = (uu___2255_75034.postprocess);
         is_native_tactic = (uu___2255_75034.is_native_tactic);
         identifier_info = (uu___2255_75034.identifier_info);
         tc_hooks = (uu___2255_75034.tc_hooks);
         dsenv = (uu___2255_75034.dsenv);
         nbe = (uu___2255_75034.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____75086)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____75090,(uu____75091,t)))::tl1
          ->
          let uu____75112 =
            let uu____75115 = FStar_Syntax_Free.uvars t  in
            ext out uu____75115  in
          aux uu____75112 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____75118;
            FStar_Syntax_Syntax.index = uu____75119;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____75127 =
            let uu____75130 = FStar_Syntax_Free.uvars t  in
            ext out uu____75130  in
          aux uu____75127 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____75188)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____75192,(uu____75193,t)))::tl1
          ->
          let uu____75214 =
            let uu____75217 = FStar_Syntax_Free.univs t  in
            ext out uu____75217  in
          aux uu____75214 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____75220;
            FStar_Syntax_Syntax.index = uu____75221;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____75229 =
            let uu____75232 = FStar_Syntax_Free.univs t  in
            ext out uu____75232  in
          aux uu____75229 tl1
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
          let uu____75294 = FStar_Util.set_add uname out  in
          aux uu____75294 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____75297,(uu____75298,t)))::tl1
          ->
          let uu____75319 =
            let uu____75322 = FStar_Syntax_Free.univnames t  in
            ext out uu____75322  in
          aux uu____75319 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____75325;
            FStar_Syntax_Syntax.index = uu____75326;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____75334 =
            let uu____75337 = FStar_Syntax_Free.univnames t  in
            ext out uu____75337  in
          aux uu____75334 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_75358  ->
            match uu___457_75358 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____75362 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____75375 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____75386 =
      let uu____75395 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____75395
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____75386 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____75443 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_75456  ->
              match uu___458_75456 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____75459 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____75459
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____75465) ->
                  let uu____75482 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____75482))
       in
    FStar_All.pipe_right uu____75443 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_75496  ->
    match uu___459_75496 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____75502 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____75502
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____75525  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____75580) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____75613,uu____75614) -> false  in
      let uu____75628 =
        FStar_List.tryFind
          (fun uu____75650  ->
             match uu____75650 with | (p,uu____75661) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____75628 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____75680,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75710 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____75710
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_75732 = e  in
        {
          solver = (uu___2398_75732.solver);
          range = (uu___2398_75732.range);
          curmodule = (uu___2398_75732.curmodule);
          gamma = (uu___2398_75732.gamma);
          gamma_sig = (uu___2398_75732.gamma_sig);
          gamma_cache = (uu___2398_75732.gamma_cache);
          modules = (uu___2398_75732.modules);
          expected_typ = (uu___2398_75732.expected_typ);
          sigtab = (uu___2398_75732.sigtab);
          attrtab = (uu___2398_75732.attrtab);
          is_pattern = (uu___2398_75732.is_pattern);
          instantiate_imp = (uu___2398_75732.instantiate_imp);
          effects = (uu___2398_75732.effects);
          generalize = (uu___2398_75732.generalize);
          letrecs = (uu___2398_75732.letrecs);
          top_level = (uu___2398_75732.top_level);
          check_uvars = (uu___2398_75732.check_uvars);
          use_eq = (uu___2398_75732.use_eq);
          is_iface = (uu___2398_75732.is_iface);
          admit = (uu___2398_75732.admit);
          lax = (uu___2398_75732.lax);
          lax_universes = (uu___2398_75732.lax_universes);
          phase1 = (uu___2398_75732.phase1);
          failhard = (uu___2398_75732.failhard);
          nosynth = (uu___2398_75732.nosynth);
          uvar_subtyping = (uu___2398_75732.uvar_subtyping);
          tc_term = (uu___2398_75732.tc_term);
          type_of = (uu___2398_75732.type_of);
          universe_of = (uu___2398_75732.universe_of);
          check_type_of = (uu___2398_75732.check_type_of);
          use_bv_sorts = (uu___2398_75732.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_75732.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_75732.normalized_eff_names);
          fv_delta_depths = (uu___2398_75732.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_75732.synth_hook);
          splice = (uu___2398_75732.splice);
          postprocess = (uu___2398_75732.postprocess);
          is_native_tactic = (uu___2398_75732.is_native_tactic);
          identifier_info = (uu___2398_75732.identifier_info);
          tc_hooks = (uu___2398_75732.tc_hooks);
          dsenv = (uu___2398_75732.dsenv);
          nbe = (uu___2398_75732.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_75780 = e  in
      {
        solver = (uu___2407_75780.solver);
        range = (uu___2407_75780.range);
        curmodule = (uu___2407_75780.curmodule);
        gamma = (uu___2407_75780.gamma);
        gamma_sig = (uu___2407_75780.gamma_sig);
        gamma_cache = (uu___2407_75780.gamma_cache);
        modules = (uu___2407_75780.modules);
        expected_typ = (uu___2407_75780.expected_typ);
        sigtab = (uu___2407_75780.sigtab);
        attrtab = (uu___2407_75780.attrtab);
        is_pattern = (uu___2407_75780.is_pattern);
        instantiate_imp = (uu___2407_75780.instantiate_imp);
        effects = (uu___2407_75780.effects);
        generalize = (uu___2407_75780.generalize);
        letrecs = (uu___2407_75780.letrecs);
        top_level = (uu___2407_75780.top_level);
        check_uvars = (uu___2407_75780.check_uvars);
        use_eq = (uu___2407_75780.use_eq);
        is_iface = (uu___2407_75780.is_iface);
        admit = (uu___2407_75780.admit);
        lax = (uu___2407_75780.lax);
        lax_universes = (uu___2407_75780.lax_universes);
        phase1 = (uu___2407_75780.phase1);
        failhard = (uu___2407_75780.failhard);
        nosynth = (uu___2407_75780.nosynth);
        uvar_subtyping = (uu___2407_75780.uvar_subtyping);
        tc_term = (uu___2407_75780.tc_term);
        type_of = (uu___2407_75780.type_of);
        universe_of = (uu___2407_75780.universe_of);
        check_type_of = (uu___2407_75780.check_type_of);
        use_bv_sorts = (uu___2407_75780.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_75780.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_75780.normalized_eff_names);
        fv_delta_depths = (uu___2407_75780.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_75780.synth_hook);
        splice = (uu___2407_75780.splice);
        postprocess = (uu___2407_75780.postprocess);
        is_native_tactic = (uu___2407_75780.is_native_tactic);
        identifier_info = (uu___2407_75780.identifier_info);
        tc_hooks = (uu___2407_75780.tc_hooks);
        dsenv = (uu___2407_75780.dsenv);
        nbe = (uu___2407_75780.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____75796 = FStar_Syntax_Free.names t  in
      let uu____75799 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____75796 uu____75799
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____75822 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____75822
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____75832 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____75832
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____75853 =
      match uu____75853 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____75873 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____75873)
       in
    let uu____75881 =
      let uu____75885 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____75885 FStar_List.rev  in
    FStar_All.pipe_right uu____75881 (FStar_String.concat " ")
  
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
                  (let uu____75955 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____75955 with
                   | FStar_Pervasives_Native.Some uu____75959 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____75962 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____75972;
        univ_ineqs = uu____75973; implicits = uu____75974;_} -> true
    | uu____75986 -> false
  
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
          let uu___2451_76017 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_76017.deferred);
            univ_ineqs = (uu___2451_76017.univ_ineqs);
            implicits = (uu___2451_76017.implicits)
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
          let uu____76056 = FStar_Options.defensive ()  in
          if uu____76056
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____76062 =
              let uu____76064 =
                let uu____76066 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____76066  in
              Prims.op_Negation uu____76064  in
            (if uu____76062
             then
               let uu____76073 =
                 let uu____76079 =
                   let uu____76081 = FStar_Syntax_Print.term_to_string t  in
                   let uu____76083 =
                     let uu____76085 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____76085
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____76081 uu____76083
                    in
                 (FStar_Errors.Warning_Defensive, uu____76079)  in
               FStar_Errors.log_issue rng uu____76073
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
          let uu____76125 =
            let uu____76127 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____76127  in
          if uu____76125
          then ()
          else
            (let uu____76132 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____76132 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____76158 =
            let uu____76160 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____76160  in
          if uu____76158
          then ()
          else
            (let uu____76165 = bound_vars e  in
             def_check_closed_in rng msg uu____76165 t)
  
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
          let uu___2488_76204 = g  in
          let uu____76205 =
            let uu____76206 =
              let uu____76207 =
                let uu____76214 =
                  let uu____76215 =
                    let uu____76232 =
                      let uu____76243 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____76243]  in
                    (f, uu____76232)  in
                  FStar_Syntax_Syntax.Tm_app uu____76215  in
                FStar_Syntax_Syntax.mk uu____76214  in
              uu____76207 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _76280  -> FStar_TypeChecker_Common.NonTrivial _76280)
              uu____76206
             in
          {
            guard_f = uu____76205;
            deferred = (uu___2488_76204.deferred);
            univ_ineqs = (uu___2488_76204.univ_ineqs);
            implicits = (uu___2488_76204.implicits)
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
          let uu___2495_76298 = g  in
          let uu____76299 =
            let uu____76300 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____76300  in
          {
            guard_f = uu____76299;
            deferred = (uu___2495_76298.deferred);
            univ_ineqs = (uu___2495_76298.univ_ineqs);
            implicits = (uu___2495_76298.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_76317 = g  in
          let uu____76318 =
            let uu____76319 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____76319  in
          {
            guard_f = uu____76318;
            deferred = (uu___2500_76317.deferred);
            univ_ineqs = (uu___2500_76317.univ_ineqs);
            implicits = (uu___2500_76317.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_76321 = g  in
          let uu____76322 =
            let uu____76323 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____76323  in
          {
            guard_f = uu____76322;
            deferred = (uu___2504_76321.deferred);
            univ_ineqs = (uu___2504_76321.univ_ineqs);
            implicits = (uu___2504_76321.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____76330 ->
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
          let uu____76347 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____76347
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____76354 =
      let uu____76355 = FStar_Syntax_Util.unmeta t  in
      uu____76355.FStar_Syntax_Syntax.n  in
    match uu____76354 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____76359 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____76402 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____76402;
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
                       let uu____76497 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____76497
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_76504 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_76504.deferred);
              univ_ineqs = (uu___2559_76504.univ_ineqs);
              implicits = (uu___2559_76504.implicits)
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
               let uu____76538 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____76538
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
            let uu___2574_76565 = g  in
            let uu____76566 =
              let uu____76567 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____76567  in
            {
              guard_f = uu____76566;
              deferred = (uu___2574_76565.deferred);
              univ_ineqs = (uu___2574_76565.univ_ineqs);
              implicits = (uu___2574_76565.implicits)
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
              let uu____76625 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____76625 with
              | FStar_Pervasives_Native.Some
                  (uu____76650::(tm,uu____76652)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____76716 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____76734 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____76734;
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
                      let uu___2596_76766 = trivial_guard  in
                      {
                        guard_f = (uu___2596_76766.guard_f);
                        deferred = (uu___2596_76766.deferred);
                        univ_ineqs = (uu___2596_76766.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____76784  -> ());
    push = (fun uu____76786  -> ());
    pop = (fun uu____76789  -> ());
    snapshot =
      (fun uu____76792  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____76811  -> fun uu____76812  -> ());
    encode_sig = (fun uu____76827  -> fun uu____76828  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____76834 =
             let uu____76841 = FStar_Options.peek ()  in (e, g, uu____76841)
              in
           [uu____76834]);
    solve = (fun uu____76857  -> fun uu____76858  -> fun uu____76859  -> ());
    finish = (fun uu____76866  -> ());
    refresh = (fun uu____76868  -> ())
  } 