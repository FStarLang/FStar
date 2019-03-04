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
    match projectee with | Beta  -> true | uu____56079 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56090 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56101 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56113 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56132 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56143 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56154 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____56165 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____56176 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____56187 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____56199 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56221 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56249 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56277 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____56302 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____56313 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____56324 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____56335 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____56346 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56357 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____56368 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____56379 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____56390 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____56401 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____56412 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56423 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____56434 -> false
  
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
      | uu____56494 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____56520 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____56531 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____56542 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____56554 -> false
  
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
           (fun uu___446_67816  ->
              match uu___446_67816 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____67819 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____67819  in
                  let uu____67820 =
                    let uu____67821 = FStar_Syntax_Subst.compress y  in
                    uu____67821.FStar_Syntax_Syntax.n  in
                  (match uu____67820 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____67825 =
                         let uu___775_67826 = y1  in
                         let uu____67827 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_67826.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_67826.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____67827
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____67825
                   | uu____67830 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_67844 = env  in
      let uu____67845 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_67844.solver);
        range = (uu___781_67844.range);
        curmodule = (uu___781_67844.curmodule);
        gamma = uu____67845;
        gamma_sig = (uu___781_67844.gamma_sig);
        gamma_cache = (uu___781_67844.gamma_cache);
        modules = (uu___781_67844.modules);
        expected_typ = (uu___781_67844.expected_typ);
        sigtab = (uu___781_67844.sigtab);
        attrtab = (uu___781_67844.attrtab);
        is_pattern = (uu___781_67844.is_pattern);
        instantiate_imp = (uu___781_67844.instantiate_imp);
        effects = (uu___781_67844.effects);
        generalize = (uu___781_67844.generalize);
        letrecs = (uu___781_67844.letrecs);
        top_level = (uu___781_67844.top_level);
        check_uvars = (uu___781_67844.check_uvars);
        use_eq = (uu___781_67844.use_eq);
        is_iface = (uu___781_67844.is_iface);
        admit = (uu___781_67844.admit);
        lax = (uu___781_67844.lax);
        lax_universes = (uu___781_67844.lax_universes);
        phase1 = (uu___781_67844.phase1);
        failhard = (uu___781_67844.failhard);
        nosynth = (uu___781_67844.nosynth);
        uvar_subtyping = (uu___781_67844.uvar_subtyping);
        tc_term = (uu___781_67844.tc_term);
        type_of = (uu___781_67844.type_of);
        universe_of = (uu___781_67844.universe_of);
        check_type_of = (uu___781_67844.check_type_of);
        use_bv_sorts = (uu___781_67844.use_bv_sorts);
        qtbl_name_and_index = (uu___781_67844.qtbl_name_and_index);
        normalized_eff_names = (uu___781_67844.normalized_eff_names);
        fv_delta_depths = (uu___781_67844.fv_delta_depths);
        proof_ns = (uu___781_67844.proof_ns);
        synth_hook = (uu___781_67844.synth_hook);
        splice = (uu___781_67844.splice);
        postprocess = (uu___781_67844.postprocess);
        is_native_tactic = (uu___781_67844.is_native_tactic);
        identifier_info = (uu___781_67844.identifier_info);
        tc_hooks = (uu___781_67844.tc_hooks);
        dsenv = (uu___781_67844.dsenv);
        nbe = (uu___781_67844.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____67853  -> fun uu____67854  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_67876 = env  in
      {
        solver = (uu___788_67876.solver);
        range = (uu___788_67876.range);
        curmodule = (uu___788_67876.curmodule);
        gamma = (uu___788_67876.gamma);
        gamma_sig = (uu___788_67876.gamma_sig);
        gamma_cache = (uu___788_67876.gamma_cache);
        modules = (uu___788_67876.modules);
        expected_typ = (uu___788_67876.expected_typ);
        sigtab = (uu___788_67876.sigtab);
        attrtab = (uu___788_67876.attrtab);
        is_pattern = (uu___788_67876.is_pattern);
        instantiate_imp = (uu___788_67876.instantiate_imp);
        effects = (uu___788_67876.effects);
        generalize = (uu___788_67876.generalize);
        letrecs = (uu___788_67876.letrecs);
        top_level = (uu___788_67876.top_level);
        check_uvars = (uu___788_67876.check_uvars);
        use_eq = (uu___788_67876.use_eq);
        is_iface = (uu___788_67876.is_iface);
        admit = (uu___788_67876.admit);
        lax = (uu___788_67876.lax);
        lax_universes = (uu___788_67876.lax_universes);
        phase1 = (uu___788_67876.phase1);
        failhard = (uu___788_67876.failhard);
        nosynth = (uu___788_67876.nosynth);
        uvar_subtyping = (uu___788_67876.uvar_subtyping);
        tc_term = (uu___788_67876.tc_term);
        type_of = (uu___788_67876.type_of);
        universe_of = (uu___788_67876.universe_of);
        check_type_of = (uu___788_67876.check_type_of);
        use_bv_sorts = (uu___788_67876.use_bv_sorts);
        qtbl_name_and_index = (uu___788_67876.qtbl_name_and_index);
        normalized_eff_names = (uu___788_67876.normalized_eff_names);
        fv_delta_depths = (uu___788_67876.fv_delta_depths);
        proof_ns = (uu___788_67876.proof_ns);
        synth_hook = (uu___788_67876.synth_hook);
        splice = (uu___788_67876.splice);
        postprocess = (uu___788_67876.postprocess);
        is_native_tactic = (uu___788_67876.is_native_tactic);
        identifier_info = (uu___788_67876.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_67876.dsenv);
        nbe = (uu___788_67876.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_67888 = e  in
      let uu____67889 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_67888.solver);
        range = (uu___792_67888.range);
        curmodule = (uu___792_67888.curmodule);
        gamma = (uu___792_67888.gamma);
        gamma_sig = (uu___792_67888.gamma_sig);
        gamma_cache = (uu___792_67888.gamma_cache);
        modules = (uu___792_67888.modules);
        expected_typ = (uu___792_67888.expected_typ);
        sigtab = (uu___792_67888.sigtab);
        attrtab = (uu___792_67888.attrtab);
        is_pattern = (uu___792_67888.is_pattern);
        instantiate_imp = (uu___792_67888.instantiate_imp);
        effects = (uu___792_67888.effects);
        generalize = (uu___792_67888.generalize);
        letrecs = (uu___792_67888.letrecs);
        top_level = (uu___792_67888.top_level);
        check_uvars = (uu___792_67888.check_uvars);
        use_eq = (uu___792_67888.use_eq);
        is_iface = (uu___792_67888.is_iface);
        admit = (uu___792_67888.admit);
        lax = (uu___792_67888.lax);
        lax_universes = (uu___792_67888.lax_universes);
        phase1 = (uu___792_67888.phase1);
        failhard = (uu___792_67888.failhard);
        nosynth = (uu___792_67888.nosynth);
        uvar_subtyping = (uu___792_67888.uvar_subtyping);
        tc_term = (uu___792_67888.tc_term);
        type_of = (uu___792_67888.type_of);
        universe_of = (uu___792_67888.universe_of);
        check_type_of = (uu___792_67888.check_type_of);
        use_bv_sorts = (uu___792_67888.use_bv_sorts);
        qtbl_name_and_index = (uu___792_67888.qtbl_name_and_index);
        normalized_eff_names = (uu___792_67888.normalized_eff_names);
        fv_delta_depths = (uu___792_67888.fv_delta_depths);
        proof_ns = (uu___792_67888.proof_ns);
        synth_hook = (uu___792_67888.synth_hook);
        splice = (uu___792_67888.splice);
        postprocess = (uu___792_67888.postprocess);
        is_native_tactic = (uu___792_67888.is_native_tactic);
        identifier_info = (uu___792_67888.identifier_info);
        tc_hooks = (uu___792_67888.tc_hooks);
        dsenv = uu____67889;
        nbe = (uu___792_67888.nbe)
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
      | (NoDelta ,uu____67918) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____67921,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____67923,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____67926 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____67940 . unit -> 'Auu____67940 FStar_Util.smap =
  fun uu____67947  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____67953 . unit -> 'Auu____67953 FStar_Util.smap =
  fun uu____67960  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____68098 = new_gamma_cache ()  in
                  let uu____68101 = new_sigtab ()  in
                  let uu____68104 = new_sigtab ()  in
                  let uu____68111 =
                    let uu____68126 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____68126, FStar_Pervasives_Native.None)  in
                  let uu____68147 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____68151 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____68155 = FStar_Options.using_facts_from ()  in
                  let uu____68156 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____68159 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____68098;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____68101;
                    attrtab = uu____68104;
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
                    qtbl_name_and_index = uu____68111;
                    normalized_eff_names = uu____68147;
                    fv_delta_depths = uu____68151;
                    proof_ns = uu____68155;
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
                    is_native_tactic = (fun uu____68221  -> false);
                    identifier_info = uu____68156;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____68159;
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
  fun uu____68333  ->
    let uu____68334 = FStar_ST.op_Bang query_indices  in
    match uu____68334 with
    | [] -> failwith "Empty query indices!"
    | uu____68389 ->
        let uu____68399 =
          let uu____68409 =
            let uu____68417 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____68417  in
          let uu____68471 = FStar_ST.op_Bang query_indices  in uu____68409 ::
            uu____68471
           in
        FStar_ST.op_Colon_Equals query_indices uu____68399
  
let (pop_query_indices : unit -> unit) =
  fun uu____68567  ->
    let uu____68568 = FStar_ST.op_Bang query_indices  in
    match uu____68568 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____68695  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____68732  ->
    match uu____68732 with
    | (l,n1) ->
        let uu____68742 = FStar_ST.op_Bang query_indices  in
        (match uu____68742 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____68864 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____68887  ->
    let uu____68888 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____68888
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____68967 =
       let uu____68970 = FStar_ST.op_Bang stack  in env :: uu____68970  in
     FStar_ST.op_Colon_Equals stack uu____68967);
    (let uu___860_69019 = env  in
     let uu____69020 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____69023 = FStar_Util.smap_copy (sigtab env)  in
     let uu____69026 = FStar_Util.smap_copy (attrtab env)  in
     let uu____69033 =
       let uu____69048 =
         let uu____69052 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____69052  in
       let uu____69084 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____69048, uu____69084)  in
     let uu____69133 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____69136 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____69139 =
       let uu____69142 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____69142  in
     {
       solver = (uu___860_69019.solver);
       range = (uu___860_69019.range);
       curmodule = (uu___860_69019.curmodule);
       gamma = (uu___860_69019.gamma);
       gamma_sig = (uu___860_69019.gamma_sig);
       gamma_cache = uu____69020;
       modules = (uu___860_69019.modules);
       expected_typ = (uu___860_69019.expected_typ);
       sigtab = uu____69023;
       attrtab = uu____69026;
       is_pattern = (uu___860_69019.is_pattern);
       instantiate_imp = (uu___860_69019.instantiate_imp);
       effects = (uu___860_69019.effects);
       generalize = (uu___860_69019.generalize);
       letrecs = (uu___860_69019.letrecs);
       top_level = (uu___860_69019.top_level);
       check_uvars = (uu___860_69019.check_uvars);
       use_eq = (uu___860_69019.use_eq);
       is_iface = (uu___860_69019.is_iface);
       admit = (uu___860_69019.admit);
       lax = (uu___860_69019.lax);
       lax_universes = (uu___860_69019.lax_universes);
       phase1 = (uu___860_69019.phase1);
       failhard = (uu___860_69019.failhard);
       nosynth = (uu___860_69019.nosynth);
       uvar_subtyping = (uu___860_69019.uvar_subtyping);
       tc_term = (uu___860_69019.tc_term);
       type_of = (uu___860_69019.type_of);
       universe_of = (uu___860_69019.universe_of);
       check_type_of = (uu___860_69019.check_type_of);
       use_bv_sorts = (uu___860_69019.use_bv_sorts);
       qtbl_name_and_index = uu____69033;
       normalized_eff_names = uu____69133;
       fv_delta_depths = uu____69136;
       proof_ns = (uu___860_69019.proof_ns);
       synth_hook = (uu___860_69019.synth_hook);
       splice = (uu___860_69019.splice);
       postprocess = (uu___860_69019.postprocess);
       is_native_tactic = (uu___860_69019.is_native_tactic);
       identifier_info = uu____69139;
       tc_hooks = (uu___860_69019.tc_hooks);
       dsenv = (uu___860_69019.dsenv);
       nbe = (uu___860_69019.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____69189  ->
    let uu____69190 = FStar_ST.op_Bang stack  in
    match uu____69190 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____69244 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____69334  ->
           let uu____69335 = snapshot_stack env  in
           match uu____69335 with
           | (stack_depth,env1) ->
               let uu____69369 = snapshot_query_indices ()  in
               (match uu____69369 with
                | (query_indices_depth,()) ->
                    let uu____69402 = (env1.solver).snapshot msg  in
                    (match uu____69402 with
                     | (solver_depth,()) ->
                         let uu____69459 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____69459 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_69526 = env1  in
                                 {
                                   solver = (uu___885_69526.solver);
                                   range = (uu___885_69526.range);
                                   curmodule = (uu___885_69526.curmodule);
                                   gamma = (uu___885_69526.gamma);
                                   gamma_sig = (uu___885_69526.gamma_sig);
                                   gamma_cache = (uu___885_69526.gamma_cache);
                                   modules = (uu___885_69526.modules);
                                   expected_typ =
                                     (uu___885_69526.expected_typ);
                                   sigtab = (uu___885_69526.sigtab);
                                   attrtab = (uu___885_69526.attrtab);
                                   is_pattern = (uu___885_69526.is_pattern);
                                   instantiate_imp =
                                     (uu___885_69526.instantiate_imp);
                                   effects = (uu___885_69526.effects);
                                   generalize = (uu___885_69526.generalize);
                                   letrecs = (uu___885_69526.letrecs);
                                   top_level = (uu___885_69526.top_level);
                                   check_uvars = (uu___885_69526.check_uvars);
                                   use_eq = (uu___885_69526.use_eq);
                                   is_iface = (uu___885_69526.is_iface);
                                   admit = (uu___885_69526.admit);
                                   lax = (uu___885_69526.lax);
                                   lax_universes =
                                     (uu___885_69526.lax_universes);
                                   phase1 = (uu___885_69526.phase1);
                                   failhard = (uu___885_69526.failhard);
                                   nosynth = (uu___885_69526.nosynth);
                                   uvar_subtyping =
                                     (uu___885_69526.uvar_subtyping);
                                   tc_term = (uu___885_69526.tc_term);
                                   type_of = (uu___885_69526.type_of);
                                   universe_of = (uu___885_69526.universe_of);
                                   check_type_of =
                                     (uu___885_69526.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_69526.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_69526.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_69526.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_69526.fv_delta_depths);
                                   proof_ns = (uu___885_69526.proof_ns);
                                   synth_hook = (uu___885_69526.synth_hook);
                                   splice = (uu___885_69526.splice);
                                   postprocess = (uu___885_69526.postprocess);
                                   is_native_tactic =
                                     (uu___885_69526.is_native_tactic);
                                   identifier_info =
                                     (uu___885_69526.identifier_info);
                                   tc_hooks = (uu___885_69526.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_69526.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____69560  ->
             let uu____69561 =
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
             match uu____69561 with
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
                             ((let uu____69741 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____69741
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____69757 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____69757
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____69789,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____69831 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____69861  ->
                  match uu____69861 with
                  | (m,uu____69869) -> FStar_Ident.lid_equals l m))
           in
        (match uu____69831 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_69884 = env  in
               {
                 solver = (uu___930_69884.solver);
                 range = (uu___930_69884.range);
                 curmodule = (uu___930_69884.curmodule);
                 gamma = (uu___930_69884.gamma);
                 gamma_sig = (uu___930_69884.gamma_sig);
                 gamma_cache = (uu___930_69884.gamma_cache);
                 modules = (uu___930_69884.modules);
                 expected_typ = (uu___930_69884.expected_typ);
                 sigtab = (uu___930_69884.sigtab);
                 attrtab = (uu___930_69884.attrtab);
                 is_pattern = (uu___930_69884.is_pattern);
                 instantiate_imp = (uu___930_69884.instantiate_imp);
                 effects = (uu___930_69884.effects);
                 generalize = (uu___930_69884.generalize);
                 letrecs = (uu___930_69884.letrecs);
                 top_level = (uu___930_69884.top_level);
                 check_uvars = (uu___930_69884.check_uvars);
                 use_eq = (uu___930_69884.use_eq);
                 is_iface = (uu___930_69884.is_iface);
                 admit = (uu___930_69884.admit);
                 lax = (uu___930_69884.lax);
                 lax_universes = (uu___930_69884.lax_universes);
                 phase1 = (uu___930_69884.phase1);
                 failhard = (uu___930_69884.failhard);
                 nosynth = (uu___930_69884.nosynth);
                 uvar_subtyping = (uu___930_69884.uvar_subtyping);
                 tc_term = (uu___930_69884.tc_term);
                 type_of = (uu___930_69884.type_of);
                 universe_of = (uu___930_69884.universe_of);
                 check_type_of = (uu___930_69884.check_type_of);
                 use_bv_sorts = (uu___930_69884.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_69884.normalized_eff_names);
                 fv_delta_depths = (uu___930_69884.fv_delta_depths);
                 proof_ns = (uu___930_69884.proof_ns);
                 synth_hook = (uu___930_69884.synth_hook);
                 splice = (uu___930_69884.splice);
                 postprocess = (uu___930_69884.postprocess);
                 is_native_tactic = (uu___930_69884.is_native_tactic);
                 identifier_info = (uu___930_69884.identifier_info);
                 tc_hooks = (uu___930_69884.tc_hooks);
                 dsenv = (uu___930_69884.dsenv);
                 nbe = (uu___930_69884.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____69901,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_69917 = env  in
               {
                 solver = (uu___939_69917.solver);
                 range = (uu___939_69917.range);
                 curmodule = (uu___939_69917.curmodule);
                 gamma = (uu___939_69917.gamma);
                 gamma_sig = (uu___939_69917.gamma_sig);
                 gamma_cache = (uu___939_69917.gamma_cache);
                 modules = (uu___939_69917.modules);
                 expected_typ = (uu___939_69917.expected_typ);
                 sigtab = (uu___939_69917.sigtab);
                 attrtab = (uu___939_69917.attrtab);
                 is_pattern = (uu___939_69917.is_pattern);
                 instantiate_imp = (uu___939_69917.instantiate_imp);
                 effects = (uu___939_69917.effects);
                 generalize = (uu___939_69917.generalize);
                 letrecs = (uu___939_69917.letrecs);
                 top_level = (uu___939_69917.top_level);
                 check_uvars = (uu___939_69917.check_uvars);
                 use_eq = (uu___939_69917.use_eq);
                 is_iface = (uu___939_69917.is_iface);
                 admit = (uu___939_69917.admit);
                 lax = (uu___939_69917.lax);
                 lax_universes = (uu___939_69917.lax_universes);
                 phase1 = (uu___939_69917.phase1);
                 failhard = (uu___939_69917.failhard);
                 nosynth = (uu___939_69917.nosynth);
                 uvar_subtyping = (uu___939_69917.uvar_subtyping);
                 tc_term = (uu___939_69917.tc_term);
                 type_of = (uu___939_69917.type_of);
                 universe_of = (uu___939_69917.universe_of);
                 check_type_of = (uu___939_69917.check_type_of);
                 use_bv_sorts = (uu___939_69917.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_69917.normalized_eff_names);
                 fv_delta_depths = (uu___939_69917.fv_delta_depths);
                 proof_ns = (uu___939_69917.proof_ns);
                 synth_hook = (uu___939_69917.synth_hook);
                 splice = (uu___939_69917.splice);
                 postprocess = (uu___939_69917.postprocess);
                 is_native_tactic = (uu___939_69917.is_native_tactic);
                 identifier_info = (uu___939_69917.identifier_info);
                 tc_hooks = (uu___939_69917.tc_hooks);
                 dsenv = (uu___939_69917.dsenv);
                 nbe = (uu___939_69917.nbe)
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
        (let uu___946_69960 = e  in
         {
           solver = (uu___946_69960.solver);
           range = r;
           curmodule = (uu___946_69960.curmodule);
           gamma = (uu___946_69960.gamma);
           gamma_sig = (uu___946_69960.gamma_sig);
           gamma_cache = (uu___946_69960.gamma_cache);
           modules = (uu___946_69960.modules);
           expected_typ = (uu___946_69960.expected_typ);
           sigtab = (uu___946_69960.sigtab);
           attrtab = (uu___946_69960.attrtab);
           is_pattern = (uu___946_69960.is_pattern);
           instantiate_imp = (uu___946_69960.instantiate_imp);
           effects = (uu___946_69960.effects);
           generalize = (uu___946_69960.generalize);
           letrecs = (uu___946_69960.letrecs);
           top_level = (uu___946_69960.top_level);
           check_uvars = (uu___946_69960.check_uvars);
           use_eq = (uu___946_69960.use_eq);
           is_iface = (uu___946_69960.is_iface);
           admit = (uu___946_69960.admit);
           lax = (uu___946_69960.lax);
           lax_universes = (uu___946_69960.lax_universes);
           phase1 = (uu___946_69960.phase1);
           failhard = (uu___946_69960.failhard);
           nosynth = (uu___946_69960.nosynth);
           uvar_subtyping = (uu___946_69960.uvar_subtyping);
           tc_term = (uu___946_69960.tc_term);
           type_of = (uu___946_69960.type_of);
           universe_of = (uu___946_69960.universe_of);
           check_type_of = (uu___946_69960.check_type_of);
           use_bv_sorts = (uu___946_69960.use_bv_sorts);
           qtbl_name_and_index = (uu___946_69960.qtbl_name_and_index);
           normalized_eff_names = (uu___946_69960.normalized_eff_names);
           fv_delta_depths = (uu___946_69960.fv_delta_depths);
           proof_ns = (uu___946_69960.proof_ns);
           synth_hook = (uu___946_69960.synth_hook);
           splice = (uu___946_69960.splice);
           postprocess = (uu___946_69960.postprocess);
           is_native_tactic = (uu___946_69960.is_native_tactic);
           identifier_info = (uu___946_69960.identifier_info);
           tc_hooks = (uu___946_69960.tc_hooks);
           dsenv = (uu___946_69960.dsenv);
           nbe = (uu___946_69960.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____69980 =
        let uu____69981 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____69981 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____69980
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____70036 =
          let uu____70037 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____70037 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70036
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____70092 =
          let uu____70093 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____70093 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70092
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____70148 =
        let uu____70149 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____70149 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____70148
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_70213 = env  in
      {
        solver = (uu___963_70213.solver);
        range = (uu___963_70213.range);
        curmodule = lid;
        gamma = (uu___963_70213.gamma);
        gamma_sig = (uu___963_70213.gamma_sig);
        gamma_cache = (uu___963_70213.gamma_cache);
        modules = (uu___963_70213.modules);
        expected_typ = (uu___963_70213.expected_typ);
        sigtab = (uu___963_70213.sigtab);
        attrtab = (uu___963_70213.attrtab);
        is_pattern = (uu___963_70213.is_pattern);
        instantiate_imp = (uu___963_70213.instantiate_imp);
        effects = (uu___963_70213.effects);
        generalize = (uu___963_70213.generalize);
        letrecs = (uu___963_70213.letrecs);
        top_level = (uu___963_70213.top_level);
        check_uvars = (uu___963_70213.check_uvars);
        use_eq = (uu___963_70213.use_eq);
        is_iface = (uu___963_70213.is_iface);
        admit = (uu___963_70213.admit);
        lax = (uu___963_70213.lax);
        lax_universes = (uu___963_70213.lax_universes);
        phase1 = (uu___963_70213.phase1);
        failhard = (uu___963_70213.failhard);
        nosynth = (uu___963_70213.nosynth);
        uvar_subtyping = (uu___963_70213.uvar_subtyping);
        tc_term = (uu___963_70213.tc_term);
        type_of = (uu___963_70213.type_of);
        universe_of = (uu___963_70213.universe_of);
        check_type_of = (uu___963_70213.check_type_of);
        use_bv_sorts = (uu___963_70213.use_bv_sorts);
        qtbl_name_and_index = (uu___963_70213.qtbl_name_and_index);
        normalized_eff_names = (uu___963_70213.normalized_eff_names);
        fv_delta_depths = (uu___963_70213.fv_delta_depths);
        proof_ns = (uu___963_70213.proof_ns);
        synth_hook = (uu___963_70213.synth_hook);
        splice = (uu___963_70213.splice);
        postprocess = (uu___963_70213.postprocess);
        is_native_tactic = (uu___963_70213.is_native_tactic);
        identifier_info = (uu___963_70213.identifier_info);
        tc_hooks = (uu___963_70213.tc_hooks);
        dsenv = (uu___963_70213.dsenv);
        nbe = (uu___963_70213.nbe)
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
      let uu____70244 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____70244
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____70257 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____70257)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____70272 =
      let uu____70274 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____70274  in
    (FStar_Errors.Fatal_VariableNotFound, uu____70272)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____70283  ->
    let uu____70284 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____70284
  
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
      | ((formals,t),uu____70384) ->
          let vs = mk_univ_subst formals us  in
          let uu____70408 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____70408)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_70425  ->
    match uu___447_70425 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____70451  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____70471 = inst_tscheme t  in
      match uu____70471 with
      | (us,t1) ->
          let uu____70482 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____70482)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____70503  ->
          match uu____70503 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____70525 =
                         let uu____70527 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____70531 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____70535 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____70537 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____70527 uu____70531 uu____70535 uu____70537
                          in
                       failwith uu____70525)
                    else ();
                    (let uu____70542 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____70542))
               | uu____70551 ->
                   let uu____70552 =
                     let uu____70554 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____70554
                      in
                   failwith uu____70552)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____70566 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____70577 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____70588 -> false
  
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
             | ([],uu____70636) -> Maybe
             | (uu____70643,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____70663 -> No  in
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
          let uu____70757 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____70757 with
          | FStar_Pervasives_Native.None  ->
              let uu____70780 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_70824  ->
                     match uu___448_70824 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____70863 = FStar_Ident.lid_equals lid l  in
                         if uu____70863
                         then
                           let uu____70886 =
                             let uu____70905 =
                               let uu____70920 = inst_tscheme t  in
                               FStar_Util.Inl uu____70920  in
                             let uu____70935 = FStar_Ident.range_of_lid l  in
                             (uu____70905, uu____70935)  in
                           FStar_Pervasives_Native.Some uu____70886
                         else FStar_Pervasives_Native.None
                     | uu____70988 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____70780
                (fun uu____71026  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_71035  ->
                        match uu___449_71035 with
                        | (uu____71038,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____71040);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____71041;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____71042;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____71043;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____71044;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____71064 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____71064
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
                                  uu____71116 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____71123 -> cache t  in
                            let uu____71124 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____71124 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____71130 =
                                   let uu____71131 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____71131)
                                    in
                                 maybe_cache uu____71130)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____71202 = find_in_sigtab env lid  in
         match uu____71202 with
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
      let uu____71283 = lookup_qname env lid  in
      match uu____71283 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____71304,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____71418 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____71418 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____71463 =
          let uu____71466 = lookup_attr env1 attr  in se1 :: uu____71466  in
        FStar_Util.smap_add (attrtab env1) attr uu____71463  in
      FStar_List.iter
        (fun attr  ->
           let uu____71476 =
             let uu____71477 = FStar_Syntax_Subst.compress attr  in
             uu____71477.FStar_Syntax_Syntax.n  in
           match uu____71476 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____71481 =
                 let uu____71483 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____71483.FStar_Ident.str  in
               add_one1 env se uu____71481
           | uu____71484 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____71507) ->
          add_sigelts env ses
      | uu____71516 ->
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
            | uu____71531 -> ()))

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
        (fun uu___450_71563  ->
           match uu___450_71563 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____71581 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____71643,lb::[]),uu____71645) ->
            let uu____71654 =
              let uu____71663 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____71672 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____71663, uu____71672)  in
            FStar_Pervasives_Native.Some uu____71654
        | FStar_Syntax_Syntax.Sig_let ((uu____71685,lbs),uu____71687) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____71719 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____71732 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____71732
                     then
                       let uu____71745 =
                         let uu____71754 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____71763 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____71754, uu____71763)  in
                       FStar_Pervasives_Native.Some uu____71745
                     else FStar_Pervasives_Native.None)
        | uu____71786 -> FStar_Pervasives_Native.None
  
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
          let uu____71846 =
            let uu____71855 =
              let uu____71860 =
                let uu____71861 =
                  let uu____71864 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____71864
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____71861)  in
              inst_tscheme1 uu____71860  in
            (uu____71855, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71846
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____71886,uu____71887) ->
          let uu____71892 =
            let uu____71901 =
              let uu____71906 =
                let uu____71907 =
                  let uu____71910 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____71910  in
                (us, uu____71907)  in
              inst_tscheme1 uu____71906  in
            (uu____71901, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71892
      | uu____71929 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____72018 =
          match uu____72018 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____72114,uvs,t,uu____72117,uu____72118,uu____72119);
                      FStar_Syntax_Syntax.sigrng = uu____72120;
                      FStar_Syntax_Syntax.sigquals = uu____72121;
                      FStar_Syntax_Syntax.sigmeta = uu____72122;
                      FStar_Syntax_Syntax.sigattrs = uu____72123;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72146 =
                     let uu____72155 = inst_tscheme1 (uvs, t)  in
                     (uu____72155, rng)  in
                   FStar_Pervasives_Native.Some uu____72146
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____72179;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____72181;
                      FStar_Syntax_Syntax.sigattrs = uu____72182;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72199 =
                     let uu____72201 = in_cur_mod env l  in uu____72201 = Yes
                      in
                   if uu____72199
                   then
                     let uu____72213 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____72213
                      then
                        let uu____72229 =
                          let uu____72238 = inst_tscheme1 (uvs, t)  in
                          (uu____72238, rng)  in
                        FStar_Pervasives_Native.Some uu____72229
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____72271 =
                        let uu____72280 = inst_tscheme1 (uvs, t)  in
                        (uu____72280, rng)  in
                      FStar_Pervasives_Native.Some uu____72271)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72305,uu____72306);
                      FStar_Syntax_Syntax.sigrng = uu____72307;
                      FStar_Syntax_Syntax.sigquals = uu____72308;
                      FStar_Syntax_Syntax.sigmeta = uu____72309;
                      FStar_Syntax_Syntax.sigattrs = uu____72310;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____72351 =
                          let uu____72360 = inst_tscheme1 (uvs, k)  in
                          (uu____72360, rng)  in
                        FStar_Pervasives_Native.Some uu____72351
                    | uu____72381 ->
                        let uu____72382 =
                          let uu____72391 =
                            let uu____72396 =
                              let uu____72397 =
                                let uu____72400 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72400
                                 in
                              (uvs, uu____72397)  in
                            inst_tscheme1 uu____72396  in
                          (uu____72391, rng)  in
                        FStar_Pervasives_Native.Some uu____72382)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72423,uu____72424);
                      FStar_Syntax_Syntax.sigrng = uu____72425;
                      FStar_Syntax_Syntax.sigquals = uu____72426;
                      FStar_Syntax_Syntax.sigmeta = uu____72427;
                      FStar_Syntax_Syntax.sigattrs = uu____72428;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____72470 =
                          let uu____72479 = inst_tscheme_with (uvs, k) us  in
                          (uu____72479, rng)  in
                        FStar_Pervasives_Native.Some uu____72470
                    | uu____72500 ->
                        let uu____72501 =
                          let uu____72510 =
                            let uu____72515 =
                              let uu____72516 =
                                let uu____72519 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72519
                                 in
                              (uvs, uu____72516)  in
                            inst_tscheme_with uu____72515 us  in
                          (uu____72510, rng)  in
                        FStar_Pervasives_Native.Some uu____72501)
               | FStar_Util.Inr se ->
                   let uu____72555 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____72576;
                          FStar_Syntax_Syntax.sigrng = uu____72577;
                          FStar_Syntax_Syntax.sigquals = uu____72578;
                          FStar_Syntax_Syntax.sigmeta = uu____72579;
                          FStar_Syntax_Syntax.sigattrs = uu____72580;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____72595 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____72555
                     (FStar_Util.map_option
                        (fun uu____72643  ->
                           match uu____72643 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____72674 =
          let uu____72685 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____72685 mapper  in
        match uu____72674 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____72759 =
              let uu____72770 =
                let uu____72777 =
                  let uu___1290_72780 = t  in
                  let uu____72781 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_72780.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____72781;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_72780.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____72777)  in
              (uu____72770, r)  in
            FStar_Pervasives_Native.Some uu____72759
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____72830 = lookup_qname env l  in
      match uu____72830 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____72851 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____72905 = try_lookup_bv env bv  in
      match uu____72905 with
      | FStar_Pervasives_Native.None  ->
          let uu____72920 = variable_not_found bv  in
          FStar_Errors.raise_error uu____72920 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____72936 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____72937 =
            let uu____72938 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____72938  in
          (uu____72936, uu____72937)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____72960 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____72960 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____73026 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____73026  in
          let uu____73027 =
            let uu____73036 =
              let uu____73041 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____73041)  in
            (uu____73036, r1)  in
          FStar_Pervasives_Native.Some uu____73027
  
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
        let uu____73076 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____73076 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____73109,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____73134 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____73134  in
            let uu____73135 =
              let uu____73140 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____73140, r1)  in
            FStar_Pervasives_Native.Some uu____73135
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____73164 = try_lookup_lid env l  in
      match uu____73164 with
      | FStar_Pervasives_Native.None  ->
          let uu____73191 = name_not_found l  in
          let uu____73197 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____73191 uu____73197
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_73240  ->
              match uu___451_73240 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____73244 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____73265 = lookup_qname env lid  in
      match uu____73265 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73274,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73277;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73279;
              FStar_Syntax_Syntax.sigattrs = uu____73280;_},FStar_Pervasives_Native.None
            ),uu____73281)
          ->
          let uu____73330 =
            let uu____73337 =
              let uu____73338 =
                let uu____73341 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____73341 t  in
              (uvs, uu____73338)  in
            (uu____73337, q)  in
          FStar_Pervasives_Native.Some uu____73330
      | uu____73354 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73376 = lookup_qname env lid  in
      match uu____73376 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73381,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73384;
              FStar_Syntax_Syntax.sigquals = uu____73385;
              FStar_Syntax_Syntax.sigmeta = uu____73386;
              FStar_Syntax_Syntax.sigattrs = uu____73387;_},FStar_Pervasives_Native.None
            ),uu____73388)
          ->
          let uu____73437 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73437 (uvs, t)
      | uu____73442 ->
          let uu____73443 = name_not_found lid  in
          let uu____73449 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73443 uu____73449
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73469 = lookup_qname env lid  in
      match uu____73469 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73474,uvs,t,uu____73477,uu____73478,uu____73479);
              FStar_Syntax_Syntax.sigrng = uu____73480;
              FStar_Syntax_Syntax.sigquals = uu____73481;
              FStar_Syntax_Syntax.sigmeta = uu____73482;
              FStar_Syntax_Syntax.sigattrs = uu____73483;_},FStar_Pervasives_Native.None
            ),uu____73484)
          ->
          let uu____73539 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73539 (uvs, t)
      | uu____73544 ->
          let uu____73545 = name_not_found lid  in
          let uu____73551 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73545 uu____73551
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____73574 = lookup_qname env lid  in
      match uu____73574 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____73582,uu____73583,uu____73584,uu____73585,uu____73586,dcs);
              FStar_Syntax_Syntax.sigrng = uu____73588;
              FStar_Syntax_Syntax.sigquals = uu____73589;
              FStar_Syntax_Syntax.sigmeta = uu____73590;
              FStar_Syntax_Syntax.sigattrs = uu____73591;_},uu____73592),uu____73593)
          -> (true, dcs)
      | uu____73656 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____73672 = lookup_qname env lid  in
      match uu____73672 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73673,uu____73674,uu____73675,l,uu____73677,uu____73678);
              FStar_Syntax_Syntax.sigrng = uu____73679;
              FStar_Syntax_Syntax.sigquals = uu____73680;
              FStar_Syntax_Syntax.sigmeta = uu____73681;
              FStar_Syntax_Syntax.sigattrs = uu____73682;_},uu____73683),uu____73684)
          -> l
      | uu____73741 ->
          let uu____73742 =
            let uu____73744 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____73744  in
          failwith uu____73742
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____73814)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____73871) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____73895 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____73895
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____73930 -> FStar_Pervasives_Native.None)
          | uu____73939 -> FStar_Pervasives_Native.None
  
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
        let uu____74001 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____74001
  
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
        let uu____74034 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____74034
  
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
             (FStar_Util.Inl uu____74086,uu____74087) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____74136),uu____74137) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____74186 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____74204 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____74214 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____74231 ->
                  let uu____74238 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____74238
              | FStar_Syntax_Syntax.Sig_let ((uu____74239,lbs),uu____74241)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____74257 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____74257
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____74264 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____74272 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____74273 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____74280 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74281 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____74282 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74283 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____74296 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____74314 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____74314
           (fun d_opt  ->
              let uu____74327 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____74327
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____74337 =
                   let uu____74340 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____74340  in
                 match uu____74337 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____74341 =
                       let uu____74343 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____74343
                        in
                     failwith uu____74341
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____74348 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____74348
                       then
                         let uu____74351 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____74353 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____74355 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____74351 uu____74353 uu____74355
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
        (FStar_Util.Inr (se,uu____74380),uu____74381) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____74430 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____74452),uu____74453) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____74502 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____74524 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____74524
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____74547 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____74547 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____74571 =
                      let uu____74572 = FStar_Syntax_Util.un_uinst tm  in
                      uu____74572.FStar_Syntax_Syntax.n  in
                    match uu____74571 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____74577 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____74594 = lookup_qname env ftv  in
      match uu____74594 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____74598) ->
          let uu____74643 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____74643 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____74664,t),r) ->
               let uu____74679 =
                 let uu____74680 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____74680 t  in
               FStar_Pervasives_Native.Some uu____74679)
      | uu____74681 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____74693 = try_lookup_effect_lid env ftv  in
      match uu____74693 with
      | FStar_Pervasives_Native.None  ->
          let uu____74696 = name_not_found ftv  in
          let uu____74702 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____74696 uu____74702
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
        let uu____74726 = lookup_qname env lid0  in
        match uu____74726 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____74737);
                FStar_Syntax_Syntax.sigrng = uu____74738;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____74740;
                FStar_Syntax_Syntax.sigattrs = uu____74741;_},FStar_Pervasives_Native.None
              ),uu____74742)
            ->
            let lid1 =
              let uu____74796 =
                let uu____74797 = FStar_Ident.range_of_lid lid  in
                let uu____74798 =
                  let uu____74799 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____74799  in
                FStar_Range.set_use_range uu____74797 uu____74798  in
              FStar_Ident.set_lid_range lid uu____74796  in
            let uu____74800 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_74806  ->
                      match uu___452_74806 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____74809 -> false))
               in
            if uu____74800
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____74828 =
                      let uu____74830 =
                        let uu____74832 = get_range env  in
                        FStar_Range.string_of_range uu____74832  in
                      let uu____74833 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____74835 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____74830 uu____74833 uu____74835
                       in
                    failwith uu____74828)
                  in
               match (binders, univs1) with
               | ([],uu____74856) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____74882,uu____74883::uu____74884::uu____74885) ->
                   let uu____74906 =
                     let uu____74908 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____74910 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____74908 uu____74910
                      in
                   failwith uu____74906
               | uu____74921 ->
                   let uu____74936 =
                     let uu____74941 =
                       let uu____74942 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____74942)  in
                     inst_tscheme_with uu____74941 insts  in
                   (match uu____74936 with
                    | (uu____74955,t) ->
                        let t1 =
                          let uu____74958 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____74958 t  in
                        let uu____74959 =
                          let uu____74960 = FStar_Syntax_Subst.compress t1
                             in
                          uu____74960.FStar_Syntax_Syntax.n  in
                        (match uu____74959 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____74995 -> failwith "Impossible")))
        | uu____75003 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____75027 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____75027 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____75040,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____75047 = find1 l2  in
            (match uu____75047 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____75054 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____75054 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____75058 = find1 l  in
            (match uu____75058 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____75063 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____75063
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____75078 = lookup_qname env l1  in
      match uu____75078 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____75081;
              FStar_Syntax_Syntax.sigrng = uu____75082;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____75084;
              FStar_Syntax_Syntax.sigattrs = uu____75085;_},uu____75086),uu____75087)
          -> q
      | uu____75138 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____75162 =
          let uu____75163 =
            let uu____75165 = FStar_Util.string_of_int i  in
            let uu____75167 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____75165 uu____75167
             in
          failwith uu____75163  in
        let uu____75170 = lookup_datacon env lid  in
        match uu____75170 with
        | (uu____75175,t) ->
            let uu____75177 =
              let uu____75178 = FStar_Syntax_Subst.compress t  in
              uu____75178.FStar_Syntax_Syntax.n  in
            (match uu____75177 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75182) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____75226 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____75226
                      FStar_Pervasives_Native.fst)
             | uu____75237 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75251 = lookup_qname env l  in
      match uu____75251 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____75253,uu____75254,uu____75255);
              FStar_Syntax_Syntax.sigrng = uu____75256;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75258;
              FStar_Syntax_Syntax.sigattrs = uu____75259;_},uu____75260),uu____75261)
          ->
          FStar_Util.for_some
            (fun uu___453_75314  ->
               match uu___453_75314 with
               | FStar_Syntax_Syntax.Projector uu____75316 -> true
               | uu____75322 -> false) quals
      | uu____75324 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75338 = lookup_qname env lid  in
      match uu____75338 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____75340,uu____75341,uu____75342,uu____75343,uu____75344,uu____75345);
              FStar_Syntax_Syntax.sigrng = uu____75346;
              FStar_Syntax_Syntax.sigquals = uu____75347;
              FStar_Syntax_Syntax.sigmeta = uu____75348;
              FStar_Syntax_Syntax.sigattrs = uu____75349;_},uu____75350),uu____75351)
          -> true
      | uu____75409 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75423 = lookup_qname env lid  in
      match uu____75423 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75425,uu____75426,uu____75427,uu____75428,uu____75429,uu____75430);
              FStar_Syntax_Syntax.sigrng = uu____75431;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75433;
              FStar_Syntax_Syntax.sigattrs = uu____75434;_},uu____75435),uu____75436)
          ->
          FStar_Util.for_some
            (fun uu___454_75497  ->
               match uu___454_75497 with
               | FStar_Syntax_Syntax.RecordType uu____75499 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____75509 -> true
               | uu____75519 -> false) quals
      | uu____75521 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____75531,uu____75532);
            FStar_Syntax_Syntax.sigrng = uu____75533;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____75535;
            FStar_Syntax_Syntax.sigattrs = uu____75536;_},uu____75537),uu____75538)
        ->
        FStar_Util.for_some
          (fun uu___455_75595  ->
             match uu___455_75595 with
             | FStar_Syntax_Syntax.Action uu____75597 -> true
             | uu____75599 -> false) quals
    | uu____75601 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75615 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____75615
  
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
      let uu____75632 =
        let uu____75633 = FStar_Syntax_Util.un_uinst head1  in
        uu____75633.FStar_Syntax_Syntax.n  in
      match uu____75632 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75639 ->
               true
           | uu____75642 -> false)
      | uu____75644 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75658 = lookup_qname env l  in
      match uu____75658 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75661),uu____75662) ->
          FStar_Util.for_some
            (fun uu___456_75710  ->
               match uu___456_75710 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75713 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75715 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75791 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75809) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75827 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75835 ->
                 FStar_Pervasives_Native.Some true
             | uu____75854 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75857 =
        let uu____75861 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75861 mapper  in
      match uu____75857 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75921 = lookup_qname env lid  in
      match uu____75921 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75925,uu____75926,tps,uu____75928,uu____75929,uu____75930);
              FStar_Syntax_Syntax.sigrng = uu____75931;
              FStar_Syntax_Syntax.sigquals = uu____75932;
              FStar_Syntax_Syntax.sigmeta = uu____75933;
              FStar_Syntax_Syntax.sigattrs = uu____75934;_},uu____75935),uu____75936)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____76002 -> FStar_Pervasives_Native.None
  
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
           (fun uu____76048  ->
              match uu____76048 with
              | (d,uu____76057) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____76073 = effect_decl_opt env l  in
      match uu____76073 with
      | FStar_Pervasives_Native.None  ->
          let uu____76088 = name_not_found l  in
          let uu____76094 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76088 uu____76094
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76117  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76136  ->
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
        let uu____76168 = FStar_Ident.lid_equals l1 l2  in
        if uu____76168
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76179 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76179
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76190 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____76243  ->
                        match uu____76243 with
                        | (m1,m2,uu____76257,uu____76258,uu____76259) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76190 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76276 =
                    let uu____76282 =
                      let uu____76284 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____76286 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____76284
                        uu____76286
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____76282)
                     in
                  FStar_Errors.raise_error uu____76276 env.range
              | FStar_Pervasives_Native.Some
                  (uu____76296,uu____76297,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____76331 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____76331
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
  'Auu____76351 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____76351) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____76380 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____76406  ->
                match uu____76406 with
                | (d,uu____76413) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____76380 with
      | FStar_Pervasives_Native.None  ->
          let uu____76424 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____76424
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____76439 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____76439 with
           | (uu____76454,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____76472)::(wp,uu____76474)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____76530 -> failwith "Impossible"))
  
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
          let uu____76588 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____76588
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____76593 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____76593
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
                  let uu____76604 = get_range env  in
                  let uu____76605 =
                    let uu____76612 =
                      let uu____76613 =
                        let uu____76630 =
                          let uu____76641 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____76641]  in
                        (null_wp, uu____76630)  in
                      FStar_Syntax_Syntax.Tm_app uu____76613  in
                    FStar_Syntax_Syntax.mk uu____76612  in
                  uu____76605 FStar_Pervasives_Native.None uu____76604  in
                let uu____76681 =
                  let uu____76682 =
                    let uu____76693 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____76693]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____76682;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____76681))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1939_76731 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1939_76731.order);
              joins = (uu___1939_76731.joins)
            }  in
          let uu___1942_76740 = env  in
          {
            solver = (uu___1942_76740.solver);
            range = (uu___1942_76740.range);
            curmodule = (uu___1942_76740.curmodule);
            gamma = (uu___1942_76740.gamma);
            gamma_sig = (uu___1942_76740.gamma_sig);
            gamma_cache = (uu___1942_76740.gamma_cache);
            modules = (uu___1942_76740.modules);
            expected_typ = (uu___1942_76740.expected_typ);
            sigtab = (uu___1942_76740.sigtab);
            attrtab = (uu___1942_76740.attrtab);
            is_pattern = (uu___1942_76740.is_pattern);
            instantiate_imp = (uu___1942_76740.instantiate_imp);
            effects;
            generalize = (uu___1942_76740.generalize);
            letrecs = (uu___1942_76740.letrecs);
            top_level = (uu___1942_76740.top_level);
            check_uvars = (uu___1942_76740.check_uvars);
            use_eq = (uu___1942_76740.use_eq);
            is_iface = (uu___1942_76740.is_iface);
            admit = (uu___1942_76740.admit);
            lax = (uu___1942_76740.lax);
            lax_universes = (uu___1942_76740.lax_universes);
            phase1 = (uu___1942_76740.phase1);
            failhard = (uu___1942_76740.failhard);
            nosynth = (uu___1942_76740.nosynth);
            uvar_subtyping = (uu___1942_76740.uvar_subtyping);
            tc_term = (uu___1942_76740.tc_term);
            type_of = (uu___1942_76740.type_of);
            universe_of = (uu___1942_76740.universe_of);
            check_type_of = (uu___1942_76740.check_type_of);
            use_bv_sorts = (uu___1942_76740.use_bv_sorts);
            qtbl_name_and_index = (uu___1942_76740.qtbl_name_and_index);
            normalized_eff_names = (uu___1942_76740.normalized_eff_names);
            fv_delta_depths = (uu___1942_76740.fv_delta_depths);
            proof_ns = (uu___1942_76740.proof_ns);
            synth_hook = (uu___1942_76740.synth_hook);
            splice = (uu___1942_76740.splice);
            postprocess = (uu___1942_76740.postprocess);
            is_native_tactic = (uu___1942_76740.is_native_tactic);
            identifier_info = (uu___1942_76740.identifier_info);
            tc_hooks = (uu___1942_76740.tc_hooks);
            dsenv = (uu___1942_76740.dsenv);
            nbe = (uu___1942_76740.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____76770 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____76770  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____76928 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____76929 = l1 u t wp e  in
                                l2 u t uu____76928 uu____76929))
                | uu____76930 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____77002 = inst_tscheme_with lift_t [u]  in
            match uu____77002 with
            | (uu____77009,lift_t1) ->
                let uu____77011 =
                  let uu____77018 =
                    let uu____77019 =
                      let uu____77036 =
                        let uu____77047 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77056 =
                          let uu____77067 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____77067]  in
                        uu____77047 :: uu____77056  in
                      (lift_t1, uu____77036)  in
                    FStar_Syntax_Syntax.Tm_app uu____77019  in
                  FStar_Syntax_Syntax.mk uu____77018  in
                uu____77011 FStar_Pervasives_Native.None
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
            let uu____77180 = inst_tscheme_with lift_t [u]  in
            match uu____77180 with
            | (uu____77187,lift_t1) ->
                let uu____77189 =
                  let uu____77196 =
                    let uu____77197 =
                      let uu____77214 =
                        let uu____77225 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77234 =
                          let uu____77245 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____77254 =
                            let uu____77265 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____77265]  in
                          uu____77245 :: uu____77254  in
                        uu____77225 :: uu____77234  in
                      (lift_t1, uu____77214)  in
                    FStar_Syntax_Syntax.Tm_app uu____77197  in
                  FStar_Syntax_Syntax.mk uu____77196  in
                uu____77189 FStar_Pervasives_Native.None
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
              let uu____77370 =
                let uu____77371 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____77371
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____77370  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____77380 =
              let uu____77382 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____77382  in
            let uu____77383 =
              let uu____77385 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____77413 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____77413)
                 in
              FStar_Util.dflt "none" uu____77385  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____77380
              uu____77383
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____77442  ->
                    match uu____77442 with
                    | (e,uu____77450) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____77473 =
            match uu____77473 with
            | (i,j) ->
                let uu____77484 = FStar_Ident.lid_equals i j  in
                if uu____77484
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _77491  -> FStar_Pervasives_Native.Some _77491)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____77520 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____77530 = FStar_Ident.lid_equals i k  in
                        if uu____77530
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____77544 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____77544
                                  then []
                                  else
                                    (let uu____77551 =
                                       let uu____77560 =
                                         find_edge order1 (i, k)  in
                                       let uu____77563 =
                                         find_edge order1 (k, j)  in
                                       (uu____77560, uu____77563)  in
                                     match uu____77551 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____77578 =
                                           compose_edges e1 e2  in
                                         [uu____77578]
                                     | uu____77579 -> [])))))
                 in
              FStar_List.append order1 uu____77520  in
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
                   let uu____77609 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____77612 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____77612
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____77609
                   then
                     let uu____77619 =
                       let uu____77625 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____77625)
                        in
                     let uu____77629 = get_range env  in
                     FStar_Errors.raise_error uu____77619 uu____77629
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____77707 = FStar_Ident.lid_equals i j
                                   in
                                if uu____77707
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____77759 =
                                              let uu____77768 =
                                                find_edge order2 (i, k)  in
                                              let uu____77771 =
                                                find_edge order2 (j, k)  in
                                              (uu____77768, uu____77771)  in
                                            match uu____77759 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____77813,uu____77814)
                                                     ->
                                                     let uu____77821 =
                                                       let uu____77828 =
                                                         let uu____77830 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77830
                                                          in
                                                       let uu____77833 =
                                                         let uu____77835 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77835
                                                          in
                                                       (uu____77828,
                                                         uu____77833)
                                                        in
                                                     (match uu____77821 with
                                                      | (true ,true ) ->
                                                          let uu____77852 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____77852
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
                                            | uu____77895 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2069_77968 = env.effects  in
              { decls = (uu___2069_77968.decls); order = order2; joins }  in
            let uu___2072_77969 = env  in
            {
              solver = (uu___2072_77969.solver);
              range = (uu___2072_77969.range);
              curmodule = (uu___2072_77969.curmodule);
              gamma = (uu___2072_77969.gamma);
              gamma_sig = (uu___2072_77969.gamma_sig);
              gamma_cache = (uu___2072_77969.gamma_cache);
              modules = (uu___2072_77969.modules);
              expected_typ = (uu___2072_77969.expected_typ);
              sigtab = (uu___2072_77969.sigtab);
              attrtab = (uu___2072_77969.attrtab);
              is_pattern = (uu___2072_77969.is_pattern);
              instantiate_imp = (uu___2072_77969.instantiate_imp);
              effects;
              generalize = (uu___2072_77969.generalize);
              letrecs = (uu___2072_77969.letrecs);
              top_level = (uu___2072_77969.top_level);
              check_uvars = (uu___2072_77969.check_uvars);
              use_eq = (uu___2072_77969.use_eq);
              is_iface = (uu___2072_77969.is_iface);
              admit = (uu___2072_77969.admit);
              lax = (uu___2072_77969.lax);
              lax_universes = (uu___2072_77969.lax_universes);
              phase1 = (uu___2072_77969.phase1);
              failhard = (uu___2072_77969.failhard);
              nosynth = (uu___2072_77969.nosynth);
              uvar_subtyping = (uu___2072_77969.uvar_subtyping);
              tc_term = (uu___2072_77969.tc_term);
              type_of = (uu___2072_77969.type_of);
              universe_of = (uu___2072_77969.universe_of);
              check_type_of = (uu___2072_77969.check_type_of);
              use_bv_sorts = (uu___2072_77969.use_bv_sorts);
              qtbl_name_and_index = (uu___2072_77969.qtbl_name_and_index);
              normalized_eff_names = (uu___2072_77969.normalized_eff_names);
              fv_delta_depths = (uu___2072_77969.fv_delta_depths);
              proof_ns = (uu___2072_77969.proof_ns);
              synth_hook = (uu___2072_77969.synth_hook);
              splice = (uu___2072_77969.splice);
              postprocess = (uu___2072_77969.postprocess);
              is_native_tactic = (uu___2072_77969.is_native_tactic);
              identifier_info = (uu___2072_77969.identifier_info);
              tc_hooks = (uu___2072_77969.tc_hooks);
              dsenv = (uu___2072_77969.dsenv);
              nbe = (uu___2072_77969.nbe)
            }))
      | uu____77970 -> env
  
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
        | uu____77999 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____78012 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____78012 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____78029 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____78029 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____78054 =
                     let uu____78060 =
                       let uu____78062 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____78070 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____78081 =
                         let uu____78083 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____78083  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____78062 uu____78070 uu____78081
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____78060)
                      in
                   FStar_Errors.raise_error uu____78054
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____78091 =
                     let uu____78102 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____78102 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____78139  ->
                        fun uu____78140  ->
                          match (uu____78139, uu____78140) with
                          | ((x,uu____78170),(t,uu____78172)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____78091
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____78203 =
                     let uu___2110_78204 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2110_78204.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2110_78204.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2110_78204.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2110_78204.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____78203
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____78216 .
    'Auu____78216 ->
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
          let uu____78246 = effect_decl_opt env effect_name  in
          match uu____78246 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____78285 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____78308 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____78347 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____78347
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____78352 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____78352
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____78367 =
                     let uu____78370 = get_range env  in
                     let uu____78371 =
                       let uu____78378 =
                         let uu____78379 =
                           let uu____78396 =
                             let uu____78407 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____78407; wp]  in
                           (repr, uu____78396)  in
                         FStar_Syntax_Syntax.Tm_app uu____78379  in
                       FStar_Syntax_Syntax.mk uu____78378  in
                     uu____78371 FStar_Pervasives_Native.None uu____78370  in
                   FStar_Pervasives_Native.Some uu____78367)
  
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
      | uu____78554 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____78569 =
        let uu____78570 = FStar_Syntax_Subst.compress t  in
        uu____78570.FStar_Syntax_Syntax.n  in
      match uu____78569 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____78574,c) ->
          is_reifiable_comp env c
      | uu____78596 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____78616 =
           let uu____78618 = is_reifiable_effect env l  in
           Prims.op_Negation uu____78618  in
         if uu____78616
         then
           let uu____78621 =
             let uu____78627 =
               let uu____78629 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____78629
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____78627)  in
           let uu____78633 = get_range env  in
           FStar_Errors.raise_error uu____78621 uu____78633
         else ());
        (let uu____78636 = effect_repr_aux true env c u_c  in
         match uu____78636 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2175_78672 = env  in
        {
          solver = (uu___2175_78672.solver);
          range = (uu___2175_78672.range);
          curmodule = (uu___2175_78672.curmodule);
          gamma = (uu___2175_78672.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2175_78672.gamma_cache);
          modules = (uu___2175_78672.modules);
          expected_typ = (uu___2175_78672.expected_typ);
          sigtab = (uu___2175_78672.sigtab);
          attrtab = (uu___2175_78672.attrtab);
          is_pattern = (uu___2175_78672.is_pattern);
          instantiate_imp = (uu___2175_78672.instantiate_imp);
          effects = (uu___2175_78672.effects);
          generalize = (uu___2175_78672.generalize);
          letrecs = (uu___2175_78672.letrecs);
          top_level = (uu___2175_78672.top_level);
          check_uvars = (uu___2175_78672.check_uvars);
          use_eq = (uu___2175_78672.use_eq);
          is_iface = (uu___2175_78672.is_iface);
          admit = (uu___2175_78672.admit);
          lax = (uu___2175_78672.lax);
          lax_universes = (uu___2175_78672.lax_universes);
          phase1 = (uu___2175_78672.phase1);
          failhard = (uu___2175_78672.failhard);
          nosynth = (uu___2175_78672.nosynth);
          uvar_subtyping = (uu___2175_78672.uvar_subtyping);
          tc_term = (uu___2175_78672.tc_term);
          type_of = (uu___2175_78672.type_of);
          universe_of = (uu___2175_78672.universe_of);
          check_type_of = (uu___2175_78672.check_type_of);
          use_bv_sorts = (uu___2175_78672.use_bv_sorts);
          qtbl_name_and_index = (uu___2175_78672.qtbl_name_and_index);
          normalized_eff_names = (uu___2175_78672.normalized_eff_names);
          fv_delta_depths = (uu___2175_78672.fv_delta_depths);
          proof_ns = (uu___2175_78672.proof_ns);
          synth_hook = (uu___2175_78672.synth_hook);
          splice = (uu___2175_78672.splice);
          postprocess = (uu___2175_78672.postprocess);
          is_native_tactic = (uu___2175_78672.is_native_tactic);
          identifier_info = (uu___2175_78672.identifier_info);
          tc_hooks = (uu___2175_78672.tc_hooks);
          dsenv = (uu___2175_78672.dsenv);
          nbe = (uu___2175_78672.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2182_78686 = env  in
      {
        solver = (uu___2182_78686.solver);
        range = (uu___2182_78686.range);
        curmodule = (uu___2182_78686.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2182_78686.gamma_sig);
        gamma_cache = (uu___2182_78686.gamma_cache);
        modules = (uu___2182_78686.modules);
        expected_typ = (uu___2182_78686.expected_typ);
        sigtab = (uu___2182_78686.sigtab);
        attrtab = (uu___2182_78686.attrtab);
        is_pattern = (uu___2182_78686.is_pattern);
        instantiate_imp = (uu___2182_78686.instantiate_imp);
        effects = (uu___2182_78686.effects);
        generalize = (uu___2182_78686.generalize);
        letrecs = (uu___2182_78686.letrecs);
        top_level = (uu___2182_78686.top_level);
        check_uvars = (uu___2182_78686.check_uvars);
        use_eq = (uu___2182_78686.use_eq);
        is_iface = (uu___2182_78686.is_iface);
        admit = (uu___2182_78686.admit);
        lax = (uu___2182_78686.lax);
        lax_universes = (uu___2182_78686.lax_universes);
        phase1 = (uu___2182_78686.phase1);
        failhard = (uu___2182_78686.failhard);
        nosynth = (uu___2182_78686.nosynth);
        uvar_subtyping = (uu___2182_78686.uvar_subtyping);
        tc_term = (uu___2182_78686.tc_term);
        type_of = (uu___2182_78686.type_of);
        universe_of = (uu___2182_78686.universe_of);
        check_type_of = (uu___2182_78686.check_type_of);
        use_bv_sorts = (uu___2182_78686.use_bv_sorts);
        qtbl_name_and_index = (uu___2182_78686.qtbl_name_and_index);
        normalized_eff_names = (uu___2182_78686.normalized_eff_names);
        fv_delta_depths = (uu___2182_78686.fv_delta_depths);
        proof_ns = (uu___2182_78686.proof_ns);
        synth_hook = (uu___2182_78686.synth_hook);
        splice = (uu___2182_78686.splice);
        postprocess = (uu___2182_78686.postprocess);
        is_native_tactic = (uu___2182_78686.is_native_tactic);
        identifier_info = (uu___2182_78686.identifier_info);
        tc_hooks = (uu___2182_78686.tc_hooks);
        dsenv = (uu___2182_78686.dsenv);
        nbe = (uu___2182_78686.nbe)
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
            (let uu___2195_78744 = env  in
             {
               solver = (uu___2195_78744.solver);
               range = (uu___2195_78744.range);
               curmodule = (uu___2195_78744.curmodule);
               gamma = rest;
               gamma_sig = (uu___2195_78744.gamma_sig);
               gamma_cache = (uu___2195_78744.gamma_cache);
               modules = (uu___2195_78744.modules);
               expected_typ = (uu___2195_78744.expected_typ);
               sigtab = (uu___2195_78744.sigtab);
               attrtab = (uu___2195_78744.attrtab);
               is_pattern = (uu___2195_78744.is_pattern);
               instantiate_imp = (uu___2195_78744.instantiate_imp);
               effects = (uu___2195_78744.effects);
               generalize = (uu___2195_78744.generalize);
               letrecs = (uu___2195_78744.letrecs);
               top_level = (uu___2195_78744.top_level);
               check_uvars = (uu___2195_78744.check_uvars);
               use_eq = (uu___2195_78744.use_eq);
               is_iface = (uu___2195_78744.is_iface);
               admit = (uu___2195_78744.admit);
               lax = (uu___2195_78744.lax);
               lax_universes = (uu___2195_78744.lax_universes);
               phase1 = (uu___2195_78744.phase1);
               failhard = (uu___2195_78744.failhard);
               nosynth = (uu___2195_78744.nosynth);
               uvar_subtyping = (uu___2195_78744.uvar_subtyping);
               tc_term = (uu___2195_78744.tc_term);
               type_of = (uu___2195_78744.type_of);
               universe_of = (uu___2195_78744.universe_of);
               check_type_of = (uu___2195_78744.check_type_of);
               use_bv_sorts = (uu___2195_78744.use_bv_sorts);
               qtbl_name_and_index = (uu___2195_78744.qtbl_name_and_index);
               normalized_eff_names = (uu___2195_78744.normalized_eff_names);
               fv_delta_depths = (uu___2195_78744.fv_delta_depths);
               proof_ns = (uu___2195_78744.proof_ns);
               synth_hook = (uu___2195_78744.synth_hook);
               splice = (uu___2195_78744.splice);
               postprocess = (uu___2195_78744.postprocess);
               is_native_tactic = (uu___2195_78744.is_native_tactic);
               identifier_info = (uu___2195_78744.identifier_info);
               tc_hooks = (uu___2195_78744.tc_hooks);
               dsenv = (uu___2195_78744.dsenv);
               nbe = (uu___2195_78744.nbe)
             }))
    | uu____78745 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____78774  ->
             match uu____78774 with | (x,uu____78782) -> push_bv env1 x) env
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
            let uu___2209_78817 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2209_78817.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2209_78817.FStar_Syntax_Syntax.index);
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
      (let uu___2220_78859 = env  in
       {
         solver = (uu___2220_78859.solver);
         range = (uu___2220_78859.range);
         curmodule = (uu___2220_78859.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2220_78859.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2220_78859.sigtab);
         attrtab = (uu___2220_78859.attrtab);
         is_pattern = (uu___2220_78859.is_pattern);
         instantiate_imp = (uu___2220_78859.instantiate_imp);
         effects = (uu___2220_78859.effects);
         generalize = (uu___2220_78859.generalize);
         letrecs = (uu___2220_78859.letrecs);
         top_level = (uu___2220_78859.top_level);
         check_uvars = (uu___2220_78859.check_uvars);
         use_eq = (uu___2220_78859.use_eq);
         is_iface = (uu___2220_78859.is_iface);
         admit = (uu___2220_78859.admit);
         lax = (uu___2220_78859.lax);
         lax_universes = (uu___2220_78859.lax_universes);
         phase1 = (uu___2220_78859.phase1);
         failhard = (uu___2220_78859.failhard);
         nosynth = (uu___2220_78859.nosynth);
         uvar_subtyping = (uu___2220_78859.uvar_subtyping);
         tc_term = (uu___2220_78859.tc_term);
         type_of = (uu___2220_78859.type_of);
         universe_of = (uu___2220_78859.universe_of);
         check_type_of = (uu___2220_78859.check_type_of);
         use_bv_sorts = (uu___2220_78859.use_bv_sorts);
         qtbl_name_and_index = (uu___2220_78859.qtbl_name_and_index);
         normalized_eff_names = (uu___2220_78859.normalized_eff_names);
         fv_delta_depths = (uu___2220_78859.fv_delta_depths);
         proof_ns = (uu___2220_78859.proof_ns);
         synth_hook = (uu___2220_78859.synth_hook);
         splice = (uu___2220_78859.splice);
         postprocess = (uu___2220_78859.postprocess);
         is_native_tactic = (uu___2220_78859.is_native_tactic);
         identifier_info = (uu___2220_78859.identifier_info);
         tc_hooks = (uu___2220_78859.tc_hooks);
         dsenv = (uu___2220_78859.dsenv);
         nbe = (uu___2220_78859.nbe)
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
        let uu____78903 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____78903 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____78931 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____78931)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2235_78947 = env  in
      {
        solver = (uu___2235_78947.solver);
        range = (uu___2235_78947.range);
        curmodule = (uu___2235_78947.curmodule);
        gamma = (uu___2235_78947.gamma);
        gamma_sig = (uu___2235_78947.gamma_sig);
        gamma_cache = (uu___2235_78947.gamma_cache);
        modules = (uu___2235_78947.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2235_78947.sigtab);
        attrtab = (uu___2235_78947.attrtab);
        is_pattern = (uu___2235_78947.is_pattern);
        instantiate_imp = (uu___2235_78947.instantiate_imp);
        effects = (uu___2235_78947.effects);
        generalize = (uu___2235_78947.generalize);
        letrecs = (uu___2235_78947.letrecs);
        top_level = (uu___2235_78947.top_level);
        check_uvars = (uu___2235_78947.check_uvars);
        use_eq = false;
        is_iface = (uu___2235_78947.is_iface);
        admit = (uu___2235_78947.admit);
        lax = (uu___2235_78947.lax);
        lax_universes = (uu___2235_78947.lax_universes);
        phase1 = (uu___2235_78947.phase1);
        failhard = (uu___2235_78947.failhard);
        nosynth = (uu___2235_78947.nosynth);
        uvar_subtyping = (uu___2235_78947.uvar_subtyping);
        tc_term = (uu___2235_78947.tc_term);
        type_of = (uu___2235_78947.type_of);
        universe_of = (uu___2235_78947.universe_of);
        check_type_of = (uu___2235_78947.check_type_of);
        use_bv_sorts = (uu___2235_78947.use_bv_sorts);
        qtbl_name_and_index = (uu___2235_78947.qtbl_name_and_index);
        normalized_eff_names = (uu___2235_78947.normalized_eff_names);
        fv_delta_depths = (uu___2235_78947.fv_delta_depths);
        proof_ns = (uu___2235_78947.proof_ns);
        synth_hook = (uu___2235_78947.synth_hook);
        splice = (uu___2235_78947.splice);
        postprocess = (uu___2235_78947.postprocess);
        is_native_tactic = (uu___2235_78947.is_native_tactic);
        identifier_info = (uu___2235_78947.identifier_info);
        tc_hooks = (uu___2235_78947.tc_hooks);
        dsenv = (uu___2235_78947.dsenv);
        nbe = (uu___2235_78947.nbe)
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
    let uu____78978 = expected_typ env_  in
    ((let uu___2242_78984 = env_  in
      {
        solver = (uu___2242_78984.solver);
        range = (uu___2242_78984.range);
        curmodule = (uu___2242_78984.curmodule);
        gamma = (uu___2242_78984.gamma);
        gamma_sig = (uu___2242_78984.gamma_sig);
        gamma_cache = (uu___2242_78984.gamma_cache);
        modules = (uu___2242_78984.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2242_78984.sigtab);
        attrtab = (uu___2242_78984.attrtab);
        is_pattern = (uu___2242_78984.is_pattern);
        instantiate_imp = (uu___2242_78984.instantiate_imp);
        effects = (uu___2242_78984.effects);
        generalize = (uu___2242_78984.generalize);
        letrecs = (uu___2242_78984.letrecs);
        top_level = (uu___2242_78984.top_level);
        check_uvars = (uu___2242_78984.check_uvars);
        use_eq = false;
        is_iface = (uu___2242_78984.is_iface);
        admit = (uu___2242_78984.admit);
        lax = (uu___2242_78984.lax);
        lax_universes = (uu___2242_78984.lax_universes);
        phase1 = (uu___2242_78984.phase1);
        failhard = (uu___2242_78984.failhard);
        nosynth = (uu___2242_78984.nosynth);
        uvar_subtyping = (uu___2242_78984.uvar_subtyping);
        tc_term = (uu___2242_78984.tc_term);
        type_of = (uu___2242_78984.type_of);
        universe_of = (uu___2242_78984.universe_of);
        check_type_of = (uu___2242_78984.check_type_of);
        use_bv_sorts = (uu___2242_78984.use_bv_sorts);
        qtbl_name_and_index = (uu___2242_78984.qtbl_name_and_index);
        normalized_eff_names = (uu___2242_78984.normalized_eff_names);
        fv_delta_depths = (uu___2242_78984.fv_delta_depths);
        proof_ns = (uu___2242_78984.proof_ns);
        synth_hook = (uu___2242_78984.synth_hook);
        splice = (uu___2242_78984.splice);
        postprocess = (uu___2242_78984.postprocess);
        is_native_tactic = (uu___2242_78984.is_native_tactic);
        identifier_info = (uu___2242_78984.identifier_info);
        tc_hooks = (uu___2242_78984.tc_hooks);
        dsenv = (uu___2242_78984.dsenv);
        nbe = (uu___2242_78984.nbe)
      }), uu____78978)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____78996 =
      let uu____78999 = FStar_Ident.id_of_text ""  in [uu____78999]  in
    FStar_Ident.lid_of_ids uu____78996  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____79006 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____79006
        then
          let uu____79011 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____79011 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2250_79039 = env  in
       {
         solver = (uu___2250_79039.solver);
         range = (uu___2250_79039.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2250_79039.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2250_79039.expected_typ);
         sigtab = (uu___2250_79039.sigtab);
         attrtab = (uu___2250_79039.attrtab);
         is_pattern = (uu___2250_79039.is_pattern);
         instantiate_imp = (uu___2250_79039.instantiate_imp);
         effects = (uu___2250_79039.effects);
         generalize = (uu___2250_79039.generalize);
         letrecs = (uu___2250_79039.letrecs);
         top_level = (uu___2250_79039.top_level);
         check_uvars = (uu___2250_79039.check_uvars);
         use_eq = (uu___2250_79039.use_eq);
         is_iface = (uu___2250_79039.is_iface);
         admit = (uu___2250_79039.admit);
         lax = (uu___2250_79039.lax);
         lax_universes = (uu___2250_79039.lax_universes);
         phase1 = (uu___2250_79039.phase1);
         failhard = (uu___2250_79039.failhard);
         nosynth = (uu___2250_79039.nosynth);
         uvar_subtyping = (uu___2250_79039.uvar_subtyping);
         tc_term = (uu___2250_79039.tc_term);
         type_of = (uu___2250_79039.type_of);
         universe_of = (uu___2250_79039.universe_of);
         check_type_of = (uu___2250_79039.check_type_of);
         use_bv_sorts = (uu___2250_79039.use_bv_sorts);
         qtbl_name_and_index = (uu___2250_79039.qtbl_name_and_index);
         normalized_eff_names = (uu___2250_79039.normalized_eff_names);
         fv_delta_depths = (uu___2250_79039.fv_delta_depths);
         proof_ns = (uu___2250_79039.proof_ns);
         synth_hook = (uu___2250_79039.synth_hook);
         splice = (uu___2250_79039.splice);
         postprocess = (uu___2250_79039.postprocess);
         is_native_tactic = (uu___2250_79039.is_native_tactic);
         identifier_info = (uu___2250_79039.identifier_info);
         tc_hooks = (uu___2250_79039.tc_hooks);
         dsenv = (uu___2250_79039.dsenv);
         nbe = (uu___2250_79039.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79091)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79095,(uu____79096,t)))::tl1
          ->
          let uu____79117 =
            let uu____79120 = FStar_Syntax_Free.uvars t  in
            ext out uu____79120  in
          aux uu____79117 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79123;
            FStar_Syntax_Syntax.index = uu____79124;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79132 =
            let uu____79135 = FStar_Syntax_Free.uvars t  in
            ext out uu____79135  in
          aux uu____79132 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79193)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79197,(uu____79198,t)))::tl1
          ->
          let uu____79219 =
            let uu____79222 = FStar_Syntax_Free.univs t  in
            ext out uu____79222  in
          aux uu____79219 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79225;
            FStar_Syntax_Syntax.index = uu____79226;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79234 =
            let uu____79237 = FStar_Syntax_Free.univs t  in
            ext out uu____79237  in
          aux uu____79234 tl1
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
          let uu____79299 = FStar_Util.set_add uname out  in
          aux uu____79299 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79302,(uu____79303,t)))::tl1
          ->
          let uu____79324 =
            let uu____79327 = FStar_Syntax_Free.univnames t  in
            ext out uu____79327  in
          aux uu____79324 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79330;
            FStar_Syntax_Syntax.index = uu____79331;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79339 =
            let uu____79342 = FStar_Syntax_Free.univnames t  in
            ext out uu____79342  in
          aux uu____79339 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_79363  ->
            match uu___457_79363 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____79367 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____79380 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____79391 =
      let uu____79400 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____79400
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____79391 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____79448 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_79461  ->
              match uu___458_79461 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____79464 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____79464
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____79470) ->
                  let uu____79487 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____79487))
       in
    FStar_All.pipe_right uu____79448 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_79501  ->
    match uu___459_79501 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____79507 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____79507
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____79530  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____79585) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____79618,uu____79619) -> false  in
      let uu____79633 =
        FStar_List.tryFind
          (fun uu____79655  ->
             match uu____79655 with | (p,uu____79666) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____79633 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____79685,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____79715 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____79715
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2393_79737 = e  in
        {
          solver = (uu___2393_79737.solver);
          range = (uu___2393_79737.range);
          curmodule = (uu___2393_79737.curmodule);
          gamma = (uu___2393_79737.gamma);
          gamma_sig = (uu___2393_79737.gamma_sig);
          gamma_cache = (uu___2393_79737.gamma_cache);
          modules = (uu___2393_79737.modules);
          expected_typ = (uu___2393_79737.expected_typ);
          sigtab = (uu___2393_79737.sigtab);
          attrtab = (uu___2393_79737.attrtab);
          is_pattern = (uu___2393_79737.is_pattern);
          instantiate_imp = (uu___2393_79737.instantiate_imp);
          effects = (uu___2393_79737.effects);
          generalize = (uu___2393_79737.generalize);
          letrecs = (uu___2393_79737.letrecs);
          top_level = (uu___2393_79737.top_level);
          check_uvars = (uu___2393_79737.check_uvars);
          use_eq = (uu___2393_79737.use_eq);
          is_iface = (uu___2393_79737.is_iface);
          admit = (uu___2393_79737.admit);
          lax = (uu___2393_79737.lax);
          lax_universes = (uu___2393_79737.lax_universes);
          phase1 = (uu___2393_79737.phase1);
          failhard = (uu___2393_79737.failhard);
          nosynth = (uu___2393_79737.nosynth);
          uvar_subtyping = (uu___2393_79737.uvar_subtyping);
          tc_term = (uu___2393_79737.tc_term);
          type_of = (uu___2393_79737.type_of);
          universe_of = (uu___2393_79737.universe_of);
          check_type_of = (uu___2393_79737.check_type_of);
          use_bv_sorts = (uu___2393_79737.use_bv_sorts);
          qtbl_name_and_index = (uu___2393_79737.qtbl_name_and_index);
          normalized_eff_names = (uu___2393_79737.normalized_eff_names);
          fv_delta_depths = (uu___2393_79737.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2393_79737.synth_hook);
          splice = (uu___2393_79737.splice);
          postprocess = (uu___2393_79737.postprocess);
          is_native_tactic = (uu___2393_79737.is_native_tactic);
          identifier_info = (uu___2393_79737.identifier_info);
          tc_hooks = (uu___2393_79737.tc_hooks);
          dsenv = (uu___2393_79737.dsenv);
          nbe = (uu___2393_79737.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2402_79785 = e  in
      {
        solver = (uu___2402_79785.solver);
        range = (uu___2402_79785.range);
        curmodule = (uu___2402_79785.curmodule);
        gamma = (uu___2402_79785.gamma);
        gamma_sig = (uu___2402_79785.gamma_sig);
        gamma_cache = (uu___2402_79785.gamma_cache);
        modules = (uu___2402_79785.modules);
        expected_typ = (uu___2402_79785.expected_typ);
        sigtab = (uu___2402_79785.sigtab);
        attrtab = (uu___2402_79785.attrtab);
        is_pattern = (uu___2402_79785.is_pattern);
        instantiate_imp = (uu___2402_79785.instantiate_imp);
        effects = (uu___2402_79785.effects);
        generalize = (uu___2402_79785.generalize);
        letrecs = (uu___2402_79785.letrecs);
        top_level = (uu___2402_79785.top_level);
        check_uvars = (uu___2402_79785.check_uvars);
        use_eq = (uu___2402_79785.use_eq);
        is_iface = (uu___2402_79785.is_iface);
        admit = (uu___2402_79785.admit);
        lax = (uu___2402_79785.lax);
        lax_universes = (uu___2402_79785.lax_universes);
        phase1 = (uu___2402_79785.phase1);
        failhard = (uu___2402_79785.failhard);
        nosynth = (uu___2402_79785.nosynth);
        uvar_subtyping = (uu___2402_79785.uvar_subtyping);
        tc_term = (uu___2402_79785.tc_term);
        type_of = (uu___2402_79785.type_of);
        universe_of = (uu___2402_79785.universe_of);
        check_type_of = (uu___2402_79785.check_type_of);
        use_bv_sorts = (uu___2402_79785.use_bv_sorts);
        qtbl_name_and_index = (uu___2402_79785.qtbl_name_and_index);
        normalized_eff_names = (uu___2402_79785.normalized_eff_names);
        fv_delta_depths = (uu___2402_79785.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2402_79785.synth_hook);
        splice = (uu___2402_79785.splice);
        postprocess = (uu___2402_79785.postprocess);
        is_native_tactic = (uu___2402_79785.is_native_tactic);
        identifier_info = (uu___2402_79785.identifier_info);
        tc_hooks = (uu___2402_79785.tc_hooks);
        dsenv = (uu___2402_79785.dsenv);
        nbe = (uu___2402_79785.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____79801 = FStar_Syntax_Free.names t  in
      let uu____79804 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____79801 uu____79804
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____79827 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____79827
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____79837 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____79837
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____79858 =
      match uu____79858 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____79878 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____79878)
       in
    let uu____79886 =
      let uu____79890 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____79890 FStar_List.rev  in
    FStar_All.pipe_right uu____79886 (FStar_String.concat " ")
  
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
                  (let uu____79960 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____79960 with
                   | FStar_Pervasives_Native.Some uu____79964 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____79967 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____79977;
        univ_ineqs = uu____79978; implicits = uu____79979;_} -> true
    | uu____79991 -> false
  
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
          let uu___2446_80022 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2446_80022.deferred);
            univ_ineqs = (uu___2446_80022.univ_ineqs);
            implicits = (uu___2446_80022.implicits)
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
          let uu____80061 = FStar_Options.defensive ()  in
          if uu____80061
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____80067 =
              let uu____80069 =
                let uu____80071 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____80071  in
              Prims.op_Negation uu____80069  in
            (if uu____80067
             then
               let uu____80078 =
                 let uu____80084 =
                   let uu____80086 = FStar_Syntax_Print.term_to_string t  in
                   let uu____80088 =
                     let uu____80090 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____80090
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____80086 uu____80088
                    in
                 (FStar_Errors.Warning_Defensive, uu____80084)  in
               FStar_Errors.log_issue rng uu____80078
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
          let uu____80130 =
            let uu____80132 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80132  in
          if uu____80130
          then ()
          else
            (let uu____80137 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____80137 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____80163 =
            let uu____80165 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80165  in
          if uu____80163
          then ()
          else
            (let uu____80170 = bound_vars e  in
             def_check_closed_in rng msg uu____80170 t)
  
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
          let uu___2483_80209 = g  in
          let uu____80210 =
            let uu____80211 =
              let uu____80212 =
                let uu____80219 =
                  let uu____80220 =
                    let uu____80237 =
                      let uu____80248 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____80248]  in
                    (f, uu____80237)  in
                  FStar_Syntax_Syntax.Tm_app uu____80220  in
                FStar_Syntax_Syntax.mk uu____80219  in
              uu____80212 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _80288  -> FStar_TypeChecker_Common.NonTrivial _80288)
              uu____80211
             in
          {
            guard_f = uu____80210;
            deferred = (uu___2483_80209.deferred);
            univ_ineqs = (uu___2483_80209.univ_ineqs);
            implicits = (uu___2483_80209.implicits)
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
          let uu___2490_80306 = g  in
          let uu____80307 =
            let uu____80308 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80308  in
          {
            guard_f = uu____80307;
            deferred = (uu___2490_80306.deferred);
            univ_ineqs = (uu___2490_80306.univ_ineqs);
            implicits = (uu___2490_80306.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2495_80325 = g  in
          let uu____80326 =
            let uu____80327 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____80327  in
          {
            guard_f = uu____80326;
            deferred = (uu___2495_80325.deferred);
            univ_ineqs = (uu___2495_80325.univ_ineqs);
            implicits = (uu___2495_80325.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2499_80329 = g  in
          let uu____80330 =
            let uu____80331 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80331  in
          {
            guard_f = uu____80330;
            deferred = (uu___2499_80329.deferred);
            univ_ineqs = (uu___2499_80329.univ_ineqs);
            implicits = (uu___2499_80329.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____80338 ->
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
          let uu____80355 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____80355
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____80362 =
      let uu____80363 = FStar_Syntax_Util.unmeta t  in
      uu____80363.FStar_Syntax_Syntax.n  in
    match uu____80362 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____80367 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____80410 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____80410;
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
                       let uu____80505 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____80505
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2554_80512 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2554_80512.deferred);
              univ_ineqs = (uu___2554_80512.univ_ineqs);
              implicits = (uu___2554_80512.implicits)
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
               let uu____80546 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____80546
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
            let uu___2569_80573 = g  in
            let uu____80574 =
              let uu____80575 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____80575  in
            {
              guard_f = uu____80574;
              deferred = (uu___2569_80573.deferred);
              univ_ineqs = (uu___2569_80573.univ_ineqs);
              implicits = (uu___2569_80573.implicits)
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
              let uu____80633 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____80633 with
              | FStar_Pervasives_Native.Some
                  (uu____80658::(tm,uu____80660)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____80724 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____80742 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____80742;
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
                      let uu___2591_80774 = trivial_guard  in
                      {
                        guard_f = (uu___2591_80774.guard_f);
                        deferred = (uu___2591_80774.deferred);
                        univ_ineqs = (uu___2591_80774.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____80792  -> ());
    push = (fun uu____80794  -> ());
    pop = (fun uu____80797  -> ());
    snapshot =
      (fun uu____80800  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____80819  -> fun uu____80820  -> ());
    encode_sig = (fun uu____80835  -> fun uu____80836  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____80842 =
             let uu____80849 = FStar_Options.peek ()  in (e, g, uu____80849)
              in
           [uu____80842]);
    solve = (fun uu____80865  -> fun uu____80866  -> fun uu____80867  -> ());
    finish = (fun uu____80874  -> ());
    refresh = (fun uu____80876  -> ())
  } 