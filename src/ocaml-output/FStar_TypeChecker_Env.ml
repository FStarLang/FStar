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
    match projectee with | Beta  -> true | uu____56074 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56085 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56096 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56108 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56127 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56138 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56149 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____56160 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____56171 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____56182 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____56194 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56216 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56244 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56272 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____56297 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____56308 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____56319 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____56330 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____56341 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56352 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____56363 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____56374 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____56385 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____56396 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____56407 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56418 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____56429 -> false
  
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
      | uu____56489 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____56515 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____56526 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____56537 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____56549 -> false
  
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
           (fun uu___446_67811  ->
              match uu___446_67811 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____67814 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____67814  in
                  let uu____67815 =
                    let uu____67816 = FStar_Syntax_Subst.compress y  in
                    uu____67816.FStar_Syntax_Syntax.n  in
                  (match uu____67815 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____67820 =
                         let uu___775_67821 = y1  in
                         let uu____67822 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_67821.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_67821.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____67822
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____67820
                   | uu____67825 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_67839 = env  in
      let uu____67840 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_67839.solver);
        range = (uu___781_67839.range);
        curmodule = (uu___781_67839.curmodule);
        gamma = uu____67840;
        gamma_sig = (uu___781_67839.gamma_sig);
        gamma_cache = (uu___781_67839.gamma_cache);
        modules = (uu___781_67839.modules);
        expected_typ = (uu___781_67839.expected_typ);
        sigtab = (uu___781_67839.sigtab);
        attrtab = (uu___781_67839.attrtab);
        is_pattern = (uu___781_67839.is_pattern);
        instantiate_imp = (uu___781_67839.instantiate_imp);
        effects = (uu___781_67839.effects);
        generalize = (uu___781_67839.generalize);
        letrecs = (uu___781_67839.letrecs);
        top_level = (uu___781_67839.top_level);
        check_uvars = (uu___781_67839.check_uvars);
        use_eq = (uu___781_67839.use_eq);
        is_iface = (uu___781_67839.is_iface);
        admit = (uu___781_67839.admit);
        lax = (uu___781_67839.lax);
        lax_universes = (uu___781_67839.lax_universes);
        phase1 = (uu___781_67839.phase1);
        failhard = (uu___781_67839.failhard);
        nosynth = (uu___781_67839.nosynth);
        uvar_subtyping = (uu___781_67839.uvar_subtyping);
        tc_term = (uu___781_67839.tc_term);
        type_of = (uu___781_67839.type_of);
        universe_of = (uu___781_67839.universe_of);
        check_type_of = (uu___781_67839.check_type_of);
        use_bv_sorts = (uu___781_67839.use_bv_sorts);
        qtbl_name_and_index = (uu___781_67839.qtbl_name_and_index);
        normalized_eff_names = (uu___781_67839.normalized_eff_names);
        fv_delta_depths = (uu___781_67839.fv_delta_depths);
        proof_ns = (uu___781_67839.proof_ns);
        synth_hook = (uu___781_67839.synth_hook);
        splice = (uu___781_67839.splice);
        postprocess = (uu___781_67839.postprocess);
        is_native_tactic = (uu___781_67839.is_native_tactic);
        identifier_info = (uu___781_67839.identifier_info);
        tc_hooks = (uu___781_67839.tc_hooks);
        dsenv = (uu___781_67839.dsenv);
        nbe = (uu___781_67839.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____67848  -> fun uu____67849  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_67871 = env  in
      {
        solver = (uu___788_67871.solver);
        range = (uu___788_67871.range);
        curmodule = (uu___788_67871.curmodule);
        gamma = (uu___788_67871.gamma);
        gamma_sig = (uu___788_67871.gamma_sig);
        gamma_cache = (uu___788_67871.gamma_cache);
        modules = (uu___788_67871.modules);
        expected_typ = (uu___788_67871.expected_typ);
        sigtab = (uu___788_67871.sigtab);
        attrtab = (uu___788_67871.attrtab);
        is_pattern = (uu___788_67871.is_pattern);
        instantiate_imp = (uu___788_67871.instantiate_imp);
        effects = (uu___788_67871.effects);
        generalize = (uu___788_67871.generalize);
        letrecs = (uu___788_67871.letrecs);
        top_level = (uu___788_67871.top_level);
        check_uvars = (uu___788_67871.check_uvars);
        use_eq = (uu___788_67871.use_eq);
        is_iface = (uu___788_67871.is_iface);
        admit = (uu___788_67871.admit);
        lax = (uu___788_67871.lax);
        lax_universes = (uu___788_67871.lax_universes);
        phase1 = (uu___788_67871.phase1);
        failhard = (uu___788_67871.failhard);
        nosynth = (uu___788_67871.nosynth);
        uvar_subtyping = (uu___788_67871.uvar_subtyping);
        tc_term = (uu___788_67871.tc_term);
        type_of = (uu___788_67871.type_of);
        universe_of = (uu___788_67871.universe_of);
        check_type_of = (uu___788_67871.check_type_of);
        use_bv_sorts = (uu___788_67871.use_bv_sorts);
        qtbl_name_and_index = (uu___788_67871.qtbl_name_and_index);
        normalized_eff_names = (uu___788_67871.normalized_eff_names);
        fv_delta_depths = (uu___788_67871.fv_delta_depths);
        proof_ns = (uu___788_67871.proof_ns);
        synth_hook = (uu___788_67871.synth_hook);
        splice = (uu___788_67871.splice);
        postprocess = (uu___788_67871.postprocess);
        is_native_tactic = (uu___788_67871.is_native_tactic);
        identifier_info = (uu___788_67871.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_67871.dsenv);
        nbe = (uu___788_67871.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_67883 = e  in
      let uu____67884 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_67883.solver);
        range = (uu___792_67883.range);
        curmodule = (uu___792_67883.curmodule);
        gamma = (uu___792_67883.gamma);
        gamma_sig = (uu___792_67883.gamma_sig);
        gamma_cache = (uu___792_67883.gamma_cache);
        modules = (uu___792_67883.modules);
        expected_typ = (uu___792_67883.expected_typ);
        sigtab = (uu___792_67883.sigtab);
        attrtab = (uu___792_67883.attrtab);
        is_pattern = (uu___792_67883.is_pattern);
        instantiate_imp = (uu___792_67883.instantiate_imp);
        effects = (uu___792_67883.effects);
        generalize = (uu___792_67883.generalize);
        letrecs = (uu___792_67883.letrecs);
        top_level = (uu___792_67883.top_level);
        check_uvars = (uu___792_67883.check_uvars);
        use_eq = (uu___792_67883.use_eq);
        is_iface = (uu___792_67883.is_iface);
        admit = (uu___792_67883.admit);
        lax = (uu___792_67883.lax);
        lax_universes = (uu___792_67883.lax_universes);
        phase1 = (uu___792_67883.phase1);
        failhard = (uu___792_67883.failhard);
        nosynth = (uu___792_67883.nosynth);
        uvar_subtyping = (uu___792_67883.uvar_subtyping);
        tc_term = (uu___792_67883.tc_term);
        type_of = (uu___792_67883.type_of);
        universe_of = (uu___792_67883.universe_of);
        check_type_of = (uu___792_67883.check_type_of);
        use_bv_sorts = (uu___792_67883.use_bv_sorts);
        qtbl_name_and_index = (uu___792_67883.qtbl_name_and_index);
        normalized_eff_names = (uu___792_67883.normalized_eff_names);
        fv_delta_depths = (uu___792_67883.fv_delta_depths);
        proof_ns = (uu___792_67883.proof_ns);
        synth_hook = (uu___792_67883.synth_hook);
        splice = (uu___792_67883.splice);
        postprocess = (uu___792_67883.postprocess);
        is_native_tactic = (uu___792_67883.is_native_tactic);
        identifier_info = (uu___792_67883.identifier_info);
        tc_hooks = (uu___792_67883.tc_hooks);
        dsenv = uu____67884;
        nbe = (uu___792_67883.nbe)
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
      | (NoDelta ,uu____67913) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____67916,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____67918,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____67921 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____67935 . unit -> 'Auu____67935 FStar_Util.smap =
  fun uu____67942  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____67948 . unit -> 'Auu____67948 FStar_Util.smap =
  fun uu____67955  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____68093 = new_gamma_cache ()  in
                  let uu____68096 = new_sigtab ()  in
                  let uu____68099 = new_sigtab ()  in
                  let uu____68106 =
                    let uu____68121 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____68121, FStar_Pervasives_Native.None)  in
                  let uu____68142 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____68146 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____68150 = FStar_Options.using_facts_from ()  in
                  let uu____68151 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____68154 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____68093;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____68096;
                    attrtab = uu____68099;
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
                    qtbl_name_and_index = uu____68106;
                    normalized_eff_names = uu____68142;
                    fv_delta_depths = uu____68146;
                    proof_ns = uu____68150;
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
                    is_native_tactic = (fun uu____68216  -> false);
                    identifier_info = uu____68151;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____68154;
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
  fun uu____68328  ->
    let uu____68329 = FStar_ST.op_Bang query_indices  in
    match uu____68329 with
    | [] -> failwith "Empty query indices!"
    | uu____68384 ->
        let uu____68394 =
          let uu____68404 =
            let uu____68412 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____68412  in
          let uu____68466 = FStar_ST.op_Bang query_indices  in uu____68404 ::
            uu____68466
           in
        FStar_ST.op_Colon_Equals query_indices uu____68394
  
let (pop_query_indices : unit -> unit) =
  fun uu____68562  ->
    let uu____68563 = FStar_ST.op_Bang query_indices  in
    match uu____68563 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____68690  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____68727  ->
    match uu____68727 with
    | (l,n1) ->
        let uu____68737 = FStar_ST.op_Bang query_indices  in
        (match uu____68737 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____68859 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____68882  ->
    let uu____68883 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____68883
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____68962 =
       let uu____68965 = FStar_ST.op_Bang stack  in env :: uu____68965  in
     FStar_ST.op_Colon_Equals stack uu____68962);
    (let uu___860_69014 = env  in
     let uu____69015 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____69018 = FStar_Util.smap_copy (sigtab env)  in
     let uu____69021 = FStar_Util.smap_copy (attrtab env)  in
     let uu____69028 =
       let uu____69043 =
         let uu____69047 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____69047  in
       let uu____69079 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____69043, uu____69079)  in
     let uu____69128 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____69131 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____69134 =
       let uu____69137 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____69137  in
     {
       solver = (uu___860_69014.solver);
       range = (uu___860_69014.range);
       curmodule = (uu___860_69014.curmodule);
       gamma = (uu___860_69014.gamma);
       gamma_sig = (uu___860_69014.gamma_sig);
       gamma_cache = uu____69015;
       modules = (uu___860_69014.modules);
       expected_typ = (uu___860_69014.expected_typ);
       sigtab = uu____69018;
       attrtab = uu____69021;
       is_pattern = (uu___860_69014.is_pattern);
       instantiate_imp = (uu___860_69014.instantiate_imp);
       effects = (uu___860_69014.effects);
       generalize = (uu___860_69014.generalize);
       letrecs = (uu___860_69014.letrecs);
       top_level = (uu___860_69014.top_level);
       check_uvars = (uu___860_69014.check_uvars);
       use_eq = (uu___860_69014.use_eq);
       is_iface = (uu___860_69014.is_iface);
       admit = (uu___860_69014.admit);
       lax = (uu___860_69014.lax);
       lax_universes = (uu___860_69014.lax_universes);
       phase1 = (uu___860_69014.phase1);
       failhard = (uu___860_69014.failhard);
       nosynth = (uu___860_69014.nosynth);
       uvar_subtyping = (uu___860_69014.uvar_subtyping);
       tc_term = (uu___860_69014.tc_term);
       type_of = (uu___860_69014.type_of);
       universe_of = (uu___860_69014.universe_of);
       check_type_of = (uu___860_69014.check_type_of);
       use_bv_sorts = (uu___860_69014.use_bv_sorts);
       qtbl_name_and_index = uu____69028;
       normalized_eff_names = uu____69128;
       fv_delta_depths = uu____69131;
       proof_ns = (uu___860_69014.proof_ns);
       synth_hook = (uu___860_69014.synth_hook);
       splice = (uu___860_69014.splice);
       postprocess = (uu___860_69014.postprocess);
       is_native_tactic = (uu___860_69014.is_native_tactic);
       identifier_info = uu____69134;
       tc_hooks = (uu___860_69014.tc_hooks);
       dsenv = (uu___860_69014.dsenv);
       nbe = (uu___860_69014.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____69184  ->
    let uu____69185 = FStar_ST.op_Bang stack  in
    match uu____69185 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____69239 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____69329  ->
           let uu____69330 = snapshot_stack env  in
           match uu____69330 with
           | (stack_depth,env1) ->
               let uu____69364 = snapshot_query_indices ()  in
               (match uu____69364 with
                | (query_indices_depth,()) ->
                    let uu____69397 = (env1.solver).snapshot msg  in
                    (match uu____69397 with
                     | (solver_depth,()) ->
                         let uu____69454 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____69454 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_69521 = env1  in
                                 {
                                   solver = (uu___885_69521.solver);
                                   range = (uu___885_69521.range);
                                   curmodule = (uu___885_69521.curmodule);
                                   gamma = (uu___885_69521.gamma);
                                   gamma_sig = (uu___885_69521.gamma_sig);
                                   gamma_cache = (uu___885_69521.gamma_cache);
                                   modules = (uu___885_69521.modules);
                                   expected_typ =
                                     (uu___885_69521.expected_typ);
                                   sigtab = (uu___885_69521.sigtab);
                                   attrtab = (uu___885_69521.attrtab);
                                   is_pattern = (uu___885_69521.is_pattern);
                                   instantiate_imp =
                                     (uu___885_69521.instantiate_imp);
                                   effects = (uu___885_69521.effects);
                                   generalize = (uu___885_69521.generalize);
                                   letrecs = (uu___885_69521.letrecs);
                                   top_level = (uu___885_69521.top_level);
                                   check_uvars = (uu___885_69521.check_uvars);
                                   use_eq = (uu___885_69521.use_eq);
                                   is_iface = (uu___885_69521.is_iface);
                                   admit = (uu___885_69521.admit);
                                   lax = (uu___885_69521.lax);
                                   lax_universes =
                                     (uu___885_69521.lax_universes);
                                   phase1 = (uu___885_69521.phase1);
                                   failhard = (uu___885_69521.failhard);
                                   nosynth = (uu___885_69521.nosynth);
                                   uvar_subtyping =
                                     (uu___885_69521.uvar_subtyping);
                                   tc_term = (uu___885_69521.tc_term);
                                   type_of = (uu___885_69521.type_of);
                                   universe_of = (uu___885_69521.universe_of);
                                   check_type_of =
                                     (uu___885_69521.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_69521.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_69521.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_69521.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_69521.fv_delta_depths);
                                   proof_ns = (uu___885_69521.proof_ns);
                                   synth_hook = (uu___885_69521.synth_hook);
                                   splice = (uu___885_69521.splice);
                                   postprocess = (uu___885_69521.postprocess);
                                   is_native_tactic =
                                     (uu___885_69521.is_native_tactic);
                                   identifier_info =
                                     (uu___885_69521.identifier_info);
                                   tc_hooks = (uu___885_69521.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_69521.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____69555  ->
             let uu____69556 =
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
             match uu____69556 with
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
                             ((let uu____69736 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____69736
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____69752 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____69752
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____69784,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____69826 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____69856  ->
                  match uu____69856 with
                  | (m,uu____69864) -> FStar_Ident.lid_equals l m))
           in
        (match uu____69826 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_69879 = env  in
               {
                 solver = (uu___930_69879.solver);
                 range = (uu___930_69879.range);
                 curmodule = (uu___930_69879.curmodule);
                 gamma = (uu___930_69879.gamma);
                 gamma_sig = (uu___930_69879.gamma_sig);
                 gamma_cache = (uu___930_69879.gamma_cache);
                 modules = (uu___930_69879.modules);
                 expected_typ = (uu___930_69879.expected_typ);
                 sigtab = (uu___930_69879.sigtab);
                 attrtab = (uu___930_69879.attrtab);
                 is_pattern = (uu___930_69879.is_pattern);
                 instantiate_imp = (uu___930_69879.instantiate_imp);
                 effects = (uu___930_69879.effects);
                 generalize = (uu___930_69879.generalize);
                 letrecs = (uu___930_69879.letrecs);
                 top_level = (uu___930_69879.top_level);
                 check_uvars = (uu___930_69879.check_uvars);
                 use_eq = (uu___930_69879.use_eq);
                 is_iface = (uu___930_69879.is_iface);
                 admit = (uu___930_69879.admit);
                 lax = (uu___930_69879.lax);
                 lax_universes = (uu___930_69879.lax_universes);
                 phase1 = (uu___930_69879.phase1);
                 failhard = (uu___930_69879.failhard);
                 nosynth = (uu___930_69879.nosynth);
                 uvar_subtyping = (uu___930_69879.uvar_subtyping);
                 tc_term = (uu___930_69879.tc_term);
                 type_of = (uu___930_69879.type_of);
                 universe_of = (uu___930_69879.universe_of);
                 check_type_of = (uu___930_69879.check_type_of);
                 use_bv_sorts = (uu___930_69879.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_69879.normalized_eff_names);
                 fv_delta_depths = (uu___930_69879.fv_delta_depths);
                 proof_ns = (uu___930_69879.proof_ns);
                 synth_hook = (uu___930_69879.synth_hook);
                 splice = (uu___930_69879.splice);
                 postprocess = (uu___930_69879.postprocess);
                 is_native_tactic = (uu___930_69879.is_native_tactic);
                 identifier_info = (uu___930_69879.identifier_info);
                 tc_hooks = (uu___930_69879.tc_hooks);
                 dsenv = (uu___930_69879.dsenv);
                 nbe = (uu___930_69879.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____69896,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_69912 = env  in
               {
                 solver = (uu___939_69912.solver);
                 range = (uu___939_69912.range);
                 curmodule = (uu___939_69912.curmodule);
                 gamma = (uu___939_69912.gamma);
                 gamma_sig = (uu___939_69912.gamma_sig);
                 gamma_cache = (uu___939_69912.gamma_cache);
                 modules = (uu___939_69912.modules);
                 expected_typ = (uu___939_69912.expected_typ);
                 sigtab = (uu___939_69912.sigtab);
                 attrtab = (uu___939_69912.attrtab);
                 is_pattern = (uu___939_69912.is_pattern);
                 instantiate_imp = (uu___939_69912.instantiate_imp);
                 effects = (uu___939_69912.effects);
                 generalize = (uu___939_69912.generalize);
                 letrecs = (uu___939_69912.letrecs);
                 top_level = (uu___939_69912.top_level);
                 check_uvars = (uu___939_69912.check_uvars);
                 use_eq = (uu___939_69912.use_eq);
                 is_iface = (uu___939_69912.is_iface);
                 admit = (uu___939_69912.admit);
                 lax = (uu___939_69912.lax);
                 lax_universes = (uu___939_69912.lax_universes);
                 phase1 = (uu___939_69912.phase1);
                 failhard = (uu___939_69912.failhard);
                 nosynth = (uu___939_69912.nosynth);
                 uvar_subtyping = (uu___939_69912.uvar_subtyping);
                 tc_term = (uu___939_69912.tc_term);
                 type_of = (uu___939_69912.type_of);
                 universe_of = (uu___939_69912.universe_of);
                 check_type_of = (uu___939_69912.check_type_of);
                 use_bv_sorts = (uu___939_69912.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_69912.normalized_eff_names);
                 fv_delta_depths = (uu___939_69912.fv_delta_depths);
                 proof_ns = (uu___939_69912.proof_ns);
                 synth_hook = (uu___939_69912.synth_hook);
                 splice = (uu___939_69912.splice);
                 postprocess = (uu___939_69912.postprocess);
                 is_native_tactic = (uu___939_69912.is_native_tactic);
                 identifier_info = (uu___939_69912.identifier_info);
                 tc_hooks = (uu___939_69912.tc_hooks);
                 dsenv = (uu___939_69912.dsenv);
                 nbe = (uu___939_69912.nbe)
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
        (let uu___946_69955 = e  in
         {
           solver = (uu___946_69955.solver);
           range = r;
           curmodule = (uu___946_69955.curmodule);
           gamma = (uu___946_69955.gamma);
           gamma_sig = (uu___946_69955.gamma_sig);
           gamma_cache = (uu___946_69955.gamma_cache);
           modules = (uu___946_69955.modules);
           expected_typ = (uu___946_69955.expected_typ);
           sigtab = (uu___946_69955.sigtab);
           attrtab = (uu___946_69955.attrtab);
           is_pattern = (uu___946_69955.is_pattern);
           instantiate_imp = (uu___946_69955.instantiate_imp);
           effects = (uu___946_69955.effects);
           generalize = (uu___946_69955.generalize);
           letrecs = (uu___946_69955.letrecs);
           top_level = (uu___946_69955.top_level);
           check_uvars = (uu___946_69955.check_uvars);
           use_eq = (uu___946_69955.use_eq);
           is_iface = (uu___946_69955.is_iface);
           admit = (uu___946_69955.admit);
           lax = (uu___946_69955.lax);
           lax_universes = (uu___946_69955.lax_universes);
           phase1 = (uu___946_69955.phase1);
           failhard = (uu___946_69955.failhard);
           nosynth = (uu___946_69955.nosynth);
           uvar_subtyping = (uu___946_69955.uvar_subtyping);
           tc_term = (uu___946_69955.tc_term);
           type_of = (uu___946_69955.type_of);
           universe_of = (uu___946_69955.universe_of);
           check_type_of = (uu___946_69955.check_type_of);
           use_bv_sorts = (uu___946_69955.use_bv_sorts);
           qtbl_name_and_index = (uu___946_69955.qtbl_name_and_index);
           normalized_eff_names = (uu___946_69955.normalized_eff_names);
           fv_delta_depths = (uu___946_69955.fv_delta_depths);
           proof_ns = (uu___946_69955.proof_ns);
           synth_hook = (uu___946_69955.synth_hook);
           splice = (uu___946_69955.splice);
           postprocess = (uu___946_69955.postprocess);
           is_native_tactic = (uu___946_69955.is_native_tactic);
           identifier_info = (uu___946_69955.identifier_info);
           tc_hooks = (uu___946_69955.tc_hooks);
           dsenv = (uu___946_69955.dsenv);
           nbe = (uu___946_69955.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____69975 =
        let uu____69976 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____69976 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____69975
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____70031 =
          let uu____70032 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____70032 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70031
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____70087 =
          let uu____70088 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____70088 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70087
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____70143 =
        let uu____70144 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____70144 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____70143
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_70208 = env  in
      {
        solver = (uu___963_70208.solver);
        range = (uu___963_70208.range);
        curmodule = lid;
        gamma = (uu___963_70208.gamma);
        gamma_sig = (uu___963_70208.gamma_sig);
        gamma_cache = (uu___963_70208.gamma_cache);
        modules = (uu___963_70208.modules);
        expected_typ = (uu___963_70208.expected_typ);
        sigtab = (uu___963_70208.sigtab);
        attrtab = (uu___963_70208.attrtab);
        is_pattern = (uu___963_70208.is_pattern);
        instantiate_imp = (uu___963_70208.instantiate_imp);
        effects = (uu___963_70208.effects);
        generalize = (uu___963_70208.generalize);
        letrecs = (uu___963_70208.letrecs);
        top_level = (uu___963_70208.top_level);
        check_uvars = (uu___963_70208.check_uvars);
        use_eq = (uu___963_70208.use_eq);
        is_iface = (uu___963_70208.is_iface);
        admit = (uu___963_70208.admit);
        lax = (uu___963_70208.lax);
        lax_universes = (uu___963_70208.lax_universes);
        phase1 = (uu___963_70208.phase1);
        failhard = (uu___963_70208.failhard);
        nosynth = (uu___963_70208.nosynth);
        uvar_subtyping = (uu___963_70208.uvar_subtyping);
        tc_term = (uu___963_70208.tc_term);
        type_of = (uu___963_70208.type_of);
        universe_of = (uu___963_70208.universe_of);
        check_type_of = (uu___963_70208.check_type_of);
        use_bv_sorts = (uu___963_70208.use_bv_sorts);
        qtbl_name_and_index = (uu___963_70208.qtbl_name_and_index);
        normalized_eff_names = (uu___963_70208.normalized_eff_names);
        fv_delta_depths = (uu___963_70208.fv_delta_depths);
        proof_ns = (uu___963_70208.proof_ns);
        synth_hook = (uu___963_70208.synth_hook);
        splice = (uu___963_70208.splice);
        postprocess = (uu___963_70208.postprocess);
        is_native_tactic = (uu___963_70208.is_native_tactic);
        identifier_info = (uu___963_70208.identifier_info);
        tc_hooks = (uu___963_70208.tc_hooks);
        dsenv = (uu___963_70208.dsenv);
        nbe = (uu___963_70208.nbe)
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
      let uu____70239 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____70239
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____70252 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____70252)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____70267 =
      let uu____70269 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____70269  in
    (FStar_Errors.Fatal_VariableNotFound, uu____70267)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____70278  ->
    let uu____70279 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____70279
  
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
      | ((formals,t),uu____70379) ->
          let vs = mk_univ_subst formals us  in
          let uu____70403 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____70403)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_70420  ->
    match uu___447_70420 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____70446  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____70466 = inst_tscheme t  in
      match uu____70466 with
      | (us,t1) ->
          let uu____70477 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____70477)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____70498  ->
          match uu____70498 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____70520 =
                         let uu____70522 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____70526 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____70530 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____70532 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____70522 uu____70526 uu____70530 uu____70532
                          in
                       failwith uu____70520)
                    else ();
                    (let uu____70537 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____70537))
               | uu____70546 ->
                   let uu____70547 =
                     let uu____70549 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____70549
                      in
                   failwith uu____70547)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____70561 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____70572 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____70583 -> false
  
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
             | ([],uu____70631) -> Maybe
             | (uu____70638,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____70658 -> No  in
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
          let uu____70752 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____70752 with
          | FStar_Pervasives_Native.None  ->
              let uu____70775 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_70819  ->
                     match uu___448_70819 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____70858 = FStar_Ident.lid_equals lid l  in
                         if uu____70858
                         then
                           let uu____70881 =
                             let uu____70900 =
                               let uu____70915 = inst_tscheme t  in
                               FStar_Util.Inl uu____70915  in
                             let uu____70930 = FStar_Ident.range_of_lid l  in
                             (uu____70900, uu____70930)  in
                           FStar_Pervasives_Native.Some uu____70881
                         else FStar_Pervasives_Native.None
                     | uu____70983 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____70775
                (fun uu____71021  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_71030  ->
                        match uu___449_71030 with
                        | (uu____71033,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____71035);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____71036;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____71037;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____71038;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____71039;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____71059 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____71059
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
                                  uu____71111 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____71118 -> cache t  in
                            let uu____71119 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____71119 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____71125 =
                                   let uu____71126 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____71126)
                                    in
                                 maybe_cache uu____71125)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____71197 = find_in_sigtab env lid  in
         match uu____71197 with
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
      let uu____71278 = lookup_qname env lid  in
      match uu____71278 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____71299,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____71413 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____71413 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____71458 =
          let uu____71461 = lookup_attr env1 attr  in se1 :: uu____71461  in
        FStar_Util.smap_add (attrtab env1) attr uu____71458  in
      FStar_List.iter
        (fun attr  ->
           let uu____71471 =
             let uu____71472 = FStar_Syntax_Subst.compress attr  in
             uu____71472.FStar_Syntax_Syntax.n  in
           match uu____71471 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____71476 =
                 let uu____71478 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____71478.FStar_Ident.str  in
               add_one1 env se uu____71476
           | uu____71479 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____71502) ->
          add_sigelts env ses
      | uu____71511 ->
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
            | uu____71526 -> ()))

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
        (fun uu___450_71558  ->
           match uu___450_71558 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____71576 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____71638,lb::[]),uu____71640) ->
            let uu____71649 =
              let uu____71658 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____71667 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____71658, uu____71667)  in
            FStar_Pervasives_Native.Some uu____71649
        | FStar_Syntax_Syntax.Sig_let ((uu____71680,lbs),uu____71682) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____71714 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____71727 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____71727
                     then
                       let uu____71740 =
                         let uu____71749 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____71758 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____71749, uu____71758)  in
                       FStar_Pervasives_Native.Some uu____71740
                     else FStar_Pervasives_Native.None)
        | uu____71781 -> FStar_Pervasives_Native.None
  
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
          let uu____71841 =
            let uu____71850 =
              let uu____71855 =
                let uu____71856 =
                  let uu____71859 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____71859
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____71856)  in
              inst_tscheme1 uu____71855  in
            (uu____71850, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71841
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____71881,uu____71882) ->
          let uu____71887 =
            let uu____71896 =
              let uu____71901 =
                let uu____71902 =
                  let uu____71905 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____71905  in
                (us, uu____71902)  in
              inst_tscheme1 uu____71901  in
            (uu____71896, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71887
      | uu____71924 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____72013 =
          match uu____72013 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____72109,uvs,t,uu____72112,uu____72113,uu____72114);
                      FStar_Syntax_Syntax.sigrng = uu____72115;
                      FStar_Syntax_Syntax.sigquals = uu____72116;
                      FStar_Syntax_Syntax.sigmeta = uu____72117;
                      FStar_Syntax_Syntax.sigattrs = uu____72118;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72141 =
                     let uu____72150 = inst_tscheme1 (uvs, t)  in
                     (uu____72150, rng)  in
                   FStar_Pervasives_Native.Some uu____72141
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____72174;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____72176;
                      FStar_Syntax_Syntax.sigattrs = uu____72177;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72194 =
                     let uu____72196 = in_cur_mod env l  in uu____72196 = Yes
                      in
                   if uu____72194
                   then
                     let uu____72208 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____72208
                      then
                        let uu____72224 =
                          let uu____72233 = inst_tscheme1 (uvs, t)  in
                          (uu____72233, rng)  in
                        FStar_Pervasives_Native.Some uu____72224
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____72266 =
                        let uu____72275 = inst_tscheme1 (uvs, t)  in
                        (uu____72275, rng)  in
                      FStar_Pervasives_Native.Some uu____72266)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72300,uu____72301);
                      FStar_Syntax_Syntax.sigrng = uu____72302;
                      FStar_Syntax_Syntax.sigquals = uu____72303;
                      FStar_Syntax_Syntax.sigmeta = uu____72304;
                      FStar_Syntax_Syntax.sigattrs = uu____72305;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____72346 =
                          let uu____72355 = inst_tscheme1 (uvs, k)  in
                          (uu____72355, rng)  in
                        FStar_Pervasives_Native.Some uu____72346
                    | uu____72376 ->
                        let uu____72377 =
                          let uu____72386 =
                            let uu____72391 =
                              let uu____72392 =
                                let uu____72395 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72395
                                 in
                              (uvs, uu____72392)  in
                            inst_tscheme1 uu____72391  in
                          (uu____72386, rng)  in
                        FStar_Pervasives_Native.Some uu____72377)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72418,uu____72419);
                      FStar_Syntax_Syntax.sigrng = uu____72420;
                      FStar_Syntax_Syntax.sigquals = uu____72421;
                      FStar_Syntax_Syntax.sigmeta = uu____72422;
                      FStar_Syntax_Syntax.sigattrs = uu____72423;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____72465 =
                          let uu____72474 = inst_tscheme_with (uvs, k) us  in
                          (uu____72474, rng)  in
                        FStar_Pervasives_Native.Some uu____72465
                    | uu____72495 ->
                        let uu____72496 =
                          let uu____72505 =
                            let uu____72510 =
                              let uu____72511 =
                                let uu____72514 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72514
                                 in
                              (uvs, uu____72511)  in
                            inst_tscheme_with uu____72510 us  in
                          (uu____72505, rng)  in
                        FStar_Pervasives_Native.Some uu____72496)
               | FStar_Util.Inr se ->
                   let uu____72550 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____72571;
                          FStar_Syntax_Syntax.sigrng = uu____72572;
                          FStar_Syntax_Syntax.sigquals = uu____72573;
                          FStar_Syntax_Syntax.sigmeta = uu____72574;
                          FStar_Syntax_Syntax.sigattrs = uu____72575;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____72590 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____72550
                     (FStar_Util.map_option
                        (fun uu____72638  ->
                           match uu____72638 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____72669 =
          let uu____72680 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____72680 mapper  in
        match uu____72669 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____72754 =
              let uu____72765 =
                let uu____72772 =
                  let uu___1290_72775 = t  in
                  let uu____72776 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_72775.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____72776;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_72775.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____72772)  in
              (uu____72765, r)  in
            FStar_Pervasives_Native.Some uu____72754
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____72825 = lookup_qname env l  in
      match uu____72825 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____72846 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____72900 = try_lookup_bv env bv  in
      match uu____72900 with
      | FStar_Pervasives_Native.None  ->
          let uu____72915 = variable_not_found bv  in
          FStar_Errors.raise_error uu____72915 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____72931 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____72932 =
            let uu____72933 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____72933  in
          (uu____72931, uu____72932)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____72955 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____72955 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____73021 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____73021  in
          let uu____73022 =
            let uu____73031 =
              let uu____73036 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____73036)  in
            (uu____73031, r1)  in
          FStar_Pervasives_Native.Some uu____73022
  
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
        let uu____73071 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____73071 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____73104,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____73129 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____73129  in
            let uu____73130 =
              let uu____73135 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____73135, r1)  in
            FStar_Pervasives_Native.Some uu____73130
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____73159 = try_lookup_lid env l  in
      match uu____73159 with
      | FStar_Pervasives_Native.None  ->
          let uu____73186 = name_not_found l  in
          let uu____73192 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____73186 uu____73192
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_73235  ->
              match uu___451_73235 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____73239 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____73260 = lookup_qname env lid  in
      match uu____73260 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73269,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73272;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73274;
              FStar_Syntax_Syntax.sigattrs = uu____73275;_},FStar_Pervasives_Native.None
            ),uu____73276)
          ->
          let uu____73325 =
            let uu____73332 =
              let uu____73333 =
                let uu____73336 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____73336 t  in
              (uvs, uu____73333)  in
            (uu____73332, q)  in
          FStar_Pervasives_Native.Some uu____73325
      | uu____73349 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73371 = lookup_qname env lid  in
      match uu____73371 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73376,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73379;
              FStar_Syntax_Syntax.sigquals = uu____73380;
              FStar_Syntax_Syntax.sigmeta = uu____73381;
              FStar_Syntax_Syntax.sigattrs = uu____73382;_},FStar_Pervasives_Native.None
            ),uu____73383)
          ->
          let uu____73432 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73432 (uvs, t)
      | uu____73437 ->
          let uu____73438 = name_not_found lid  in
          let uu____73444 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73438 uu____73444
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73464 = lookup_qname env lid  in
      match uu____73464 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73469,uvs,t,uu____73472,uu____73473,uu____73474);
              FStar_Syntax_Syntax.sigrng = uu____73475;
              FStar_Syntax_Syntax.sigquals = uu____73476;
              FStar_Syntax_Syntax.sigmeta = uu____73477;
              FStar_Syntax_Syntax.sigattrs = uu____73478;_},FStar_Pervasives_Native.None
            ),uu____73479)
          ->
          let uu____73534 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73534 (uvs, t)
      | uu____73539 ->
          let uu____73540 = name_not_found lid  in
          let uu____73546 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73540 uu____73546
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____73569 = lookup_qname env lid  in
      match uu____73569 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____73577,uu____73578,uu____73579,uu____73580,uu____73581,dcs);
              FStar_Syntax_Syntax.sigrng = uu____73583;
              FStar_Syntax_Syntax.sigquals = uu____73584;
              FStar_Syntax_Syntax.sigmeta = uu____73585;
              FStar_Syntax_Syntax.sigattrs = uu____73586;_},uu____73587),uu____73588)
          -> (true, dcs)
      | uu____73651 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____73667 = lookup_qname env lid  in
      match uu____73667 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73668,uu____73669,uu____73670,l,uu____73672,uu____73673);
              FStar_Syntax_Syntax.sigrng = uu____73674;
              FStar_Syntax_Syntax.sigquals = uu____73675;
              FStar_Syntax_Syntax.sigmeta = uu____73676;
              FStar_Syntax_Syntax.sigattrs = uu____73677;_},uu____73678),uu____73679)
          -> l
      | uu____73736 ->
          let uu____73737 =
            let uu____73739 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____73739  in
          failwith uu____73737
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____73809)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____73866) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____73890 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____73890
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____73925 -> FStar_Pervasives_Native.None)
          | uu____73934 -> FStar_Pervasives_Native.None
  
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
        let uu____73996 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____73996
  
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
        let uu____74029 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____74029
  
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
             (FStar_Util.Inl uu____74081,uu____74082) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____74131),uu____74132) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____74181 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____74199 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____74209 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____74226 ->
                  let uu____74233 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____74233
              | FStar_Syntax_Syntax.Sig_let ((uu____74234,lbs),uu____74236)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____74252 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____74252
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____74259 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____74267 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____74268 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____74275 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74276 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____74277 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74278 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____74291 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____74309 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____74309
           (fun d_opt  ->
              let uu____74322 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____74322
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____74332 =
                   let uu____74335 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____74335  in
                 match uu____74332 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____74336 =
                       let uu____74338 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____74338
                        in
                     failwith uu____74336
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____74343 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____74343
                       then
                         let uu____74346 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____74348 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____74350 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____74346 uu____74348 uu____74350
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
        (FStar_Util.Inr (se,uu____74375),uu____74376) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____74425 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____74447),uu____74448) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____74497 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____74519 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____74519
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____74542 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____74542 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____74566 =
                      let uu____74567 = FStar_Syntax_Util.un_uinst tm  in
                      uu____74567.FStar_Syntax_Syntax.n  in
                    match uu____74566 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____74572 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____74589 = lookup_qname env ftv  in
      match uu____74589 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____74593) ->
          let uu____74638 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____74638 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____74659,t),r) ->
               let uu____74674 =
                 let uu____74675 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____74675 t  in
               FStar_Pervasives_Native.Some uu____74674)
      | uu____74676 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____74688 = try_lookup_effect_lid env ftv  in
      match uu____74688 with
      | FStar_Pervasives_Native.None  ->
          let uu____74691 = name_not_found ftv  in
          let uu____74697 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____74691 uu____74697
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
        let uu____74721 = lookup_qname env lid0  in
        match uu____74721 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____74732);
                FStar_Syntax_Syntax.sigrng = uu____74733;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____74735;
                FStar_Syntax_Syntax.sigattrs = uu____74736;_},FStar_Pervasives_Native.None
              ),uu____74737)
            ->
            let lid1 =
              let uu____74791 =
                let uu____74792 = FStar_Ident.range_of_lid lid  in
                let uu____74793 =
                  let uu____74794 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____74794  in
                FStar_Range.set_use_range uu____74792 uu____74793  in
              FStar_Ident.set_lid_range lid uu____74791  in
            let uu____74795 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_74801  ->
                      match uu___452_74801 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____74804 -> false))
               in
            if uu____74795
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____74823 =
                      let uu____74825 =
                        let uu____74827 = get_range env  in
                        FStar_Range.string_of_range uu____74827  in
                      let uu____74828 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____74830 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____74825 uu____74828 uu____74830
                       in
                    failwith uu____74823)
                  in
               match (binders, univs1) with
               | ([],uu____74851) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____74877,uu____74878::uu____74879::uu____74880) ->
                   let uu____74901 =
                     let uu____74903 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____74905 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____74903 uu____74905
                      in
                   failwith uu____74901
               | uu____74916 ->
                   let uu____74931 =
                     let uu____74936 =
                       let uu____74937 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____74937)  in
                     inst_tscheme_with uu____74936 insts  in
                   (match uu____74931 with
                    | (uu____74950,t) ->
                        let t1 =
                          let uu____74953 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____74953 t  in
                        let uu____74954 =
                          let uu____74955 = FStar_Syntax_Subst.compress t1
                             in
                          uu____74955.FStar_Syntax_Syntax.n  in
                        (match uu____74954 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____74990 -> failwith "Impossible")))
        | uu____74998 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____75022 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____75022 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____75035,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____75042 = find1 l2  in
            (match uu____75042 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____75049 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____75049 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____75053 = find1 l  in
            (match uu____75053 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____75058 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____75058
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____75073 = lookup_qname env l1  in
      match uu____75073 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____75076;
              FStar_Syntax_Syntax.sigrng = uu____75077;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____75079;
              FStar_Syntax_Syntax.sigattrs = uu____75080;_},uu____75081),uu____75082)
          -> q
      | uu____75133 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____75157 =
          let uu____75158 =
            let uu____75160 = FStar_Util.string_of_int i  in
            let uu____75162 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____75160 uu____75162
             in
          failwith uu____75158  in
        let uu____75165 = lookup_datacon env lid  in
        match uu____75165 with
        | (uu____75170,t) ->
            let uu____75172 =
              let uu____75173 = FStar_Syntax_Subst.compress t  in
              uu____75173.FStar_Syntax_Syntax.n  in
            (match uu____75172 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75177) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____75221 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____75221
                      FStar_Pervasives_Native.fst)
             | uu____75232 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75246 = lookup_qname env l  in
      match uu____75246 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____75248,uu____75249,uu____75250);
              FStar_Syntax_Syntax.sigrng = uu____75251;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75253;
              FStar_Syntax_Syntax.sigattrs = uu____75254;_},uu____75255),uu____75256)
          ->
          FStar_Util.for_some
            (fun uu___453_75309  ->
               match uu___453_75309 with
               | FStar_Syntax_Syntax.Projector uu____75311 -> true
               | uu____75317 -> false) quals
      | uu____75319 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75333 = lookup_qname env lid  in
      match uu____75333 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____75335,uu____75336,uu____75337,uu____75338,uu____75339,uu____75340);
              FStar_Syntax_Syntax.sigrng = uu____75341;
              FStar_Syntax_Syntax.sigquals = uu____75342;
              FStar_Syntax_Syntax.sigmeta = uu____75343;
              FStar_Syntax_Syntax.sigattrs = uu____75344;_},uu____75345),uu____75346)
          -> true
      | uu____75404 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75418 = lookup_qname env lid  in
      match uu____75418 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75420,uu____75421,uu____75422,uu____75423,uu____75424,uu____75425);
              FStar_Syntax_Syntax.sigrng = uu____75426;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75428;
              FStar_Syntax_Syntax.sigattrs = uu____75429;_},uu____75430),uu____75431)
          ->
          FStar_Util.for_some
            (fun uu___454_75492  ->
               match uu___454_75492 with
               | FStar_Syntax_Syntax.RecordType uu____75494 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____75504 -> true
               | uu____75514 -> false) quals
      | uu____75516 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____75526,uu____75527);
            FStar_Syntax_Syntax.sigrng = uu____75528;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____75530;
            FStar_Syntax_Syntax.sigattrs = uu____75531;_},uu____75532),uu____75533)
        ->
        FStar_Util.for_some
          (fun uu___455_75590  ->
             match uu___455_75590 with
             | FStar_Syntax_Syntax.Action uu____75592 -> true
             | uu____75594 -> false) quals
    | uu____75596 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75610 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____75610
  
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
      let uu____75627 =
        let uu____75628 = FStar_Syntax_Util.un_uinst head1  in
        uu____75628.FStar_Syntax_Syntax.n  in
      match uu____75627 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75634 ->
               true
           | uu____75637 -> false)
      | uu____75639 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75653 = lookup_qname env l  in
      match uu____75653 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75656),uu____75657) ->
          FStar_Util.for_some
            (fun uu___456_75705  ->
               match uu___456_75705 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75708 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75710 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75786 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75804) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75822 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75830 ->
                 FStar_Pervasives_Native.Some true
             | uu____75849 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75852 =
        let uu____75856 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75856 mapper  in
      match uu____75852 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75916 = lookup_qname env lid  in
      match uu____75916 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75920,uu____75921,tps,uu____75923,uu____75924,uu____75925);
              FStar_Syntax_Syntax.sigrng = uu____75926;
              FStar_Syntax_Syntax.sigquals = uu____75927;
              FStar_Syntax_Syntax.sigmeta = uu____75928;
              FStar_Syntax_Syntax.sigattrs = uu____75929;_},uu____75930),uu____75931)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____75997 -> FStar_Pervasives_Native.None
  
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
           (fun uu____76043  ->
              match uu____76043 with
              | (d,uu____76052) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____76068 = effect_decl_opt env l  in
      match uu____76068 with
      | FStar_Pervasives_Native.None  ->
          let uu____76083 = name_not_found l  in
          let uu____76089 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76083 uu____76089
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76112  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76131  ->
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
        let uu____76163 = FStar_Ident.lid_equals l1 l2  in
        if uu____76163
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76174 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76174
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76185 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____76238  ->
                        match uu____76238 with
                        | (m1,m2,uu____76252,uu____76253,uu____76254) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76185 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76271 =
                    let uu____76277 =
                      let uu____76279 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____76281 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____76279
                        uu____76281
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____76277)
                     in
                  FStar_Errors.raise_error uu____76271 env.range
              | FStar_Pervasives_Native.Some
                  (uu____76291,uu____76292,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____76326 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____76326
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
  'Auu____76346 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____76346) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____76375 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____76401  ->
                match uu____76401 with
                | (d,uu____76408) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____76375 with
      | FStar_Pervasives_Native.None  ->
          let uu____76419 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____76419
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____76434 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____76434 with
           | (uu____76449,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____76467)::(wp,uu____76469)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____76525 -> failwith "Impossible"))
  
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
          let uu____76583 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____76583
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____76588 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____76588
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
                  let uu____76599 = get_range env  in
                  let uu____76600 =
                    let uu____76607 =
                      let uu____76608 =
                        let uu____76625 =
                          let uu____76636 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____76636]  in
                        (null_wp, uu____76625)  in
                      FStar_Syntax_Syntax.Tm_app uu____76608  in
                    FStar_Syntax_Syntax.mk uu____76607  in
                  uu____76600 FStar_Pervasives_Native.None uu____76599  in
                let uu____76676 =
                  let uu____76677 =
                    let uu____76688 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____76688]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____76677;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____76676))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1939_76726 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1939_76726.order);
              joins = (uu___1939_76726.joins)
            }  in
          let uu___1942_76735 = env  in
          {
            solver = (uu___1942_76735.solver);
            range = (uu___1942_76735.range);
            curmodule = (uu___1942_76735.curmodule);
            gamma = (uu___1942_76735.gamma);
            gamma_sig = (uu___1942_76735.gamma_sig);
            gamma_cache = (uu___1942_76735.gamma_cache);
            modules = (uu___1942_76735.modules);
            expected_typ = (uu___1942_76735.expected_typ);
            sigtab = (uu___1942_76735.sigtab);
            attrtab = (uu___1942_76735.attrtab);
            is_pattern = (uu___1942_76735.is_pattern);
            instantiate_imp = (uu___1942_76735.instantiate_imp);
            effects;
            generalize = (uu___1942_76735.generalize);
            letrecs = (uu___1942_76735.letrecs);
            top_level = (uu___1942_76735.top_level);
            check_uvars = (uu___1942_76735.check_uvars);
            use_eq = (uu___1942_76735.use_eq);
            is_iface = (uu___1942_76735.is_iface);
            admit = (uu___1942_76735.admit);
            lax = (uu___1942_76735.lax);
            lax_universes = (uu___1942_76735.lax_universes);
            phase1 = (uu___1942_76735.phase1);
            failhard = (uu___1942_76735.failhard);
            nosynth = (uu___1942_76735.nosynth);
            uvar_subtyping = (uu___1942_76735.uvar_subtyping);
            tc_term = (uu___1942_76735.tc_term);
            type_of = (uu___1942_76735.type_of);
            universe_of = (uu___1942_76735.universe_of);
            check_type_of = (uu___1942_76735.check_type_of);
            use_bv_sorts = (uu___1942_76735.use_bv_sorts);
            qtbl_name_and_index = (uu___1942_76735.qtbl_name_and_index);
            normalized_eff_names = (uu___1942_76735.normalized_eff_names);
            fv_delta_depths = (uu___1942_76735.fv_delta_depths);
            proof_ns = (uu___1942_76735.proof_ns);
            synth_hook = (uu___1942_76735.synth_hook);
            splice = (uu___1942_76735.splice);
            postprocess = (uu___1942_76735.postprocess);
            is_native_tactic = (uu___1942_76735.is_native_tactic);
            identifier_info = (uu___1942_76735.identifier_info);
            tc_hooks = (uu___1942_76735.tc_hooks);
            dsenv = (uu___1942_76735.dsenv);
            nbe = (uu___1942_76735.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____76765 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____76765  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____76923 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____76924 = l1 u t wp e  in
                                l2 u t uu____76923 uu____76924))
                | uu____76925 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____76997 = inst_tscheme_with lift_t [u]  in
            match uu____76997 with
            | (uu____77004,lift_t1) ->
                let uu____77006 =
                  let uu____77013 =
                    let uu____77014 =
                      let uu____77031 =
                        let uu____77042 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77051 =
                          let uu____77062 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____77062]  in
                        uu____77042 :: uu____77051  in
                      (lift_t1, uu____77031)  in
                    FStar_Syntax_Syntax.Tm_app uu____77014  in
                  FStar_Syntax_Syntax.mk uu____77013  in
                uu____77006 FStar_Pervasives_Native.None
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
            let uu____77175 = inst_tscheme_with lift_t [u]  in
            match uu____77175 with
            | (uu____77182,lift_t1) ->
                let uu____77184 =
                  let uu____77191 =
                    let uu____77192 =
                      let uu____77209 =
                        let uu____77220 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77229 =
                          let uu____77240 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____77249 =
                            let uu____77260 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____77260]  in
                          uu____77240 :: uu____77249  in
                        uu____77220 :: uu____77229  in
                      (lift_t1, uu____77209)  in
                    FStar_Syntax_Syntax.Tm_app uu____77192  in
                  FStar_Syntax_Syntax.mk uu____77191  in
                uu____77184 FStar_Pervasives_Native.None
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
              let uu____77365 =
                let uu____77366 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____77366
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____77365  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____77375 =
              let uu____77377 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____77377  in
            let uu____77378 =
              let uu____77380 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____77408 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____77408)
                 in
              FStar_Util.dflt "none" uu____77380  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____77375
              uu____77378
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____77437  ->
                    match uu____77437 with
                    | (e,uu____77445) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____77468 =
            match uu____77468 with
            | (i,j) ->
                let uu____77479 = FStar_Ident.lid_equals i j  in
                if uu____77479
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _77486  -> FStar_Pervasives_Native.Some _77486)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____77515 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____77525 = FStar_Ident.lid_equals i k  in
                        if uu____77525
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____77539 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____77539
                                  then []
                                  else
                                    (let uu____77546 =
                                       let uu____77555 =
                                         find_edge order1 (i, k)  in
                                       let uu____77558 =
                                         find_edge order1 (k, j)  in
                                       (uu____77555, uu____77558)  in
                                     match uu____77546 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____77573 =
                                           compose_edges e1 e2  in
                                         [uu____77573]
                                     | uu____77574 -> [])))))
                 in
              FStar_List.append order1 uu____77515  in
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
                   let uu____77604 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____77607 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____77607
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____77604
                   then
                     let uu____77614 =
                       let uu____77620 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____77620)
                        in
                     let uu____77624 = get_range env  in
                     FStar_Errors.raise_error uu____77614 uu____77624
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____77702 = FStar_Ident.lid_equals i j
                                   in
                                if uu____77702
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____77754 =
                                              let uu____77763 =
                                                find_edge order2 (i, k)  in
                                              let uu____77766 =
                                                find_edge order2 (j, k)  in
                                              (uu____77763, uu____77766)  in
                                            match uu____77754 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____77808,uu____77809)
                                                     ->
                                                     let uu____77816 =
                                                       let uu____77823 =
                                                         let uu____77825 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77825
                                                          in
                                                       let uu____77828 =
                                                         let uu____77830 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77830
                                                          in
                                                       (uu____77823,
                                                         uu____77828)
                                                        in
                                                     (match uu____77816 with
                                                      | (true ,true ) ->
                                                          let uu____77847 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____77847
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
                                            | uu____77890 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2069_77963 = env.effects  in
              { decls = (uu___2069_77963.decls); order = order2; joins }  in
            let uu___2072_77964 = env  in
            {
              solver = (uu___2072_77964.solver);
              range = (uu___2072_77964.range);
              curmodule = (uu___2072_77964.curmodule);
              gamma = (uu___2072_77964.gamma);
              gamma_sig = (uu___2072_77964.gamma_sig);
              gamma_cache = (uu___2072_77964.gamma_cache);
              modules = (uu___2072_77964.modules);
              expected_typ = (uu___2072_77964.expected_typ);
              sigtab = (uu___2072_77964.sigtab);
              attrtab = (uu___2072_77964.attrtab);
              is_pattern = (uu___2072_77964.is_pattern);
              instantiate_imp = (uu___2072_77964.instantiate_imp);
              effects;
              generalize = (uu___2072_77964.generalize);
              letrecs = (uu___2072_77964.letrecs);
              top_level = (uu___2072_77964.top_level);
              check_uvars = (uu___2072_77964.check_uvars);
              use_eq = (uu___2072_77964.use_eq);
              is_iface = (uu___2072_77964.is_iface);
              admit = (uu___2072_77964.admit);
              lax = (uu___2072_77964.lax);
              lax_universes = (uu___2072_77964.lax_universes);
              phase1 = (uu___2072_77964.phase1);
              failhard = (uu___2072_77964.failhard);
              nosynth = (uu___2072_77964.nosynth);
              uvar_subtyping = (uu___2072_77964.uvar_subtyping);
              tc_term = (uu___2072_77964.tc_term);
              type_of = (uu___2072_77964.type_of);
              universe_of = (uu___2072_77964.universe_of);
              check_type_of = (uu___2072_77964.check_type_of);
              use_bv_sorts = (uu___2072_77964.use_bv_sorts);
              qtbl_name_and_index = (uu___2072_77964.qtbl_name_and_index);
              normalized_eff_names = (uu___2072_77964.normalized_eff_names);
              fv_delta_depths = (uu___2072_77964.fv_delta_depths);
              proof_ns = (uu___2072_77964.proof_ns);
              synth_hook = (uu___2072_77964.synth_hook);
              splice = (uu___2072_77964.splice);
              postprocess = (uu___2072_77964.postprocess);
              is_native_tactic = (uu___2072_77964.is_native_tactic);
              identifier_info = (uu___2072_77964.identifier_info);
              tc_hooks = (uu___2072_77964.tc_hooks);
              dsenv = (uu___2072_77964.dsenv);
              nbe = (uu___2072_77964.nbe)
            }))
      | uu____77965 -> env
  
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
        | uu____77994 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____78007 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____78007 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____78024 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____78024 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____78049 =
                     let uu____78055 =
                       let uu____78057 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____78065 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____78076 =
                         let uu____78078 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____78078  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____78057 uu____78065 uu____78076
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____78055)
                      in
                   FStar_Errors.raise_error uu____78049
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____78086 =
                     let uu____78097 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____78097 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____78134  ->
                        fun uu____78135  ->
                          match (uu____78134, uu____78135) with
                          | ((x,uu____78165),(t,uu____78167)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____78086
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____78198 =
                     let uu___2110_78199 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2110_78199.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2110_78199.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2110_78199.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2110_78199.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____78198
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____78211 .
    'Auu____78211 ->
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
          let uu____78241 = effect_decl_opt env effect_name  in
          match uu____78241 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____78280 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____78303 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____78342 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____78342
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____78347 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____78347
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____78362 =
                     let uu____78365 = get_range env  in
                     let uu____78366 =
                       let uu____78373 =
                         let uu____78374 =
                           let uu____78391 =
                             let uu____78402 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____78402; wp]  in
                           (repr, uu____78391)  in
                         FStar_Syntax_Syntax.Tm_app uu____78374  in
                       FStar_Syntax_Syntax.mk uu____78373  in
                     uu____78366 FStar_Pervasives_Native.None uu____78365  in
                   FStar_Pervasives_Native.Some uu____78362)
  
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
      | uu____78549 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____78564 =
        let uu____78565 = FStar_Syntax_Subst.compress t  in
        uu____78565.FStar_Syntax_Syntax.n  in
      match uu____78564 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____78569,c) ->
          is_reifiable_comp env c
      | uu____78591 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____78611 =
           let uu____78613 = is_reifiable_effect env l  in
           Prims.op_Negation uu____78613  in
         if uu____78611
         then
           let uu____78616 =
             let uu____78622 =
               let uu____78624 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____78624
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____78622)  in
           let uu____78628 = get_range env  in
           FStar_Errors.raise_error uu____78616 uu____78628
         else ());
        (let uu____78631 = effect_repr_aux true env c u_c  in
         match uu____78631 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2175_78667 = env  in
        {
          solver = (uu___2175_78667.solver);
          range = (uu___2175_78667.range);
          curmodule = (uu___2175_78667.curmodule);
          gamma = (uu___2175_78667.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2175_78667.gamma_cache);
          modules = (uu___2175_78667.modules);
          expected_typ = (uu___2175_78667.expected_typ);
          sigtab = (uu___2175_78667.sigtab);
          attrtab = (uu___2175_78667.attrtab);
          is_pattern = (uu___2175_78667.is_pattern);
          instantiate_imp = (uu___2175_78667.instantiate_imp);
          effects = (uu___2175_78667.effects);
          generalize = (uu___2175_78667.generalize);
          letrecs = (uu___2175_78667.letrecs);
          top_level = (uu___2175_78667.top_level);
          check_uvars = (uu___2175_78667.check_uvars);
          use_eq = (uu___2175_78667.use_eq);
          is_iface = (uu___2175_78667.is_iface);
          admit = (uu___2175_78667.admit);
          lax = (uu___2175_78667.lax);
          lax_universes = (uu___2175_78667.lax_universes);
          phase1 = (uu___2175_78667.phase1);
          failhard = (uu___2175_78667.failhard);
          nosynth = (uu___2175_78667.nosynth);
          uvar_subtyping = (uu___2175_78667.uvar_subtyping);
          tc_term = (uu___2175_78667.tc_term);
          type_of = (uu___2175_78667.type_of);
          universe_of = (uu___2175_78667.universe_of);
          check_type_of = (uu___2175_78667.check_type_of);
          use_bv_sorts = (uu___2175_78667.use_bv_sorts);
          qtbl_name_and_index = (uu___2175_78667.qtbl_name_and_index);
          normalized_eff_names = (uu___2175_78667.normalized_eff_names);
          fv_delta_depths = (uu___2175_78667.fv_delta_depths);
          proof_ns = (uu___2175_78667.proof_ns);
          synth_hook = (uu___2175_78667.synth_hook);
          splice = (uu___2175_78667.splice);
          postprocess = (uu___2175_78667.postprocess);
          is_native_tactic = (uu___2175_78667.is_native_tactic);
          identifier_info = (uu___2175_78667.identifier_info);
          tc_hooks = (uu___2175_78667.tc_hooks);
          dsenv = (uu___2175_78667.dsenv);
          nbe = (uu___2175_78667.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2182_78681 = env  in
      {
        solver = (uu___2182_78681.solver);
        range = (uu___2182_78681.range);
        curmodule = (uu___2182_78681.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2182_78681.gamma_sig);
        gamma_cache = (uu___2182_78681.gamma_cache);
        modules = (uu___2182_78681.modules);
        expected_typ = (uu___2182_78681.expected_typ);
        sigtab = (uu___2182_78681.sigtab);
        attrtab = (uu___2182_78681.attrtab);
        is_pattern = (uu___2182_78681.is_pattern);
        instantiate_imp = (uu___2182_78681.instantiate_imp);
        effects = (uu___2182_78681.effects);
        generalize = (uu___2182_78681.generalize);
        letrecs = (uu___2182_78681.letrecs);
        top_level = (uu___2182_78681.top_level);
        check_uvars = (uu___2182_78681.check_uvars);
        use_eq = (uu___2182_78681.use_eq);
        is_iface = (uu___2182_78681.is_iface);
        admit = (uu___2182_78681.admit);
        lax = (uu___2182_78681.lax);
        lax_universes = (uu___2182_78681.lax_universes);
        phase1 = (uu___2182_78681.phase1);
        failhard = (uu___2182_78681.failhard);
        nosynth = (uu___2182_78681.nosynth);
        uvar_subtyping = (uu___2182_78681.uvar_subtyping);
        tc_term = (uu___2182_78681.tc_term);
        type_of = (uu___2182_78681.type_of);
        universe_of = (uu___2182_78681.universe_of);
        check_type_of = (uu___2182_78681.check_type_of);
        use_bv_sorts = (uu___2182_78681.use_bv_sorts);
        qtbl_name_and_index = (uu___2182_78681.qtbl_name_and_index);
        normalized_eff_names = (uu___2182_78681.normalized_eff_names);
        fv_delta_depths = (uu___2182_78681.fv_delta_depths);
        proof_ns = (uu___2182_78681.proof_ns);
        synth_hook = (uu___2182_78681.synth_hook);
        splice = (uu___2182_78681.splice);
        postprocess = (uu___2182_78681.postprocess);
        is_native_tactic = (uu___2182_78681.is_native_tactic);
        identifier_info = (uu___2182_78681.identifier_info);
        tc_hooks = (uu___2182_78681.tc_hooks);
        dsenv = (uu___2182_78681.dsenv);
        nbe = (uu___2182_78681.nbe)
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
            (let uu___2195_78739 = env  in
             {
               solver = (uu___2195_78739.solver);
               range = (uu___2195_78739.range);
               curmodule = (uu___2195_78739.curmodule);
               gamma = rest;
               gamma_sig = (uu___2195_78739.gamma_sig);
               gamma_cache = (uu___2195_78739.gamma_cache);
               modules = (uu___2195_78739.modules);
               expected_typ = (uu___2195_78739.expected_typ);
               sigtab = (uu___2195_78739.sigtab);
               attrtab = (uu___2195_78739.attrtab);
               is_pattern = (uu___2195_78739.is_pattern);
               instantiate_imp = (uu___2195_78739.instantiate_imp);
               effects = (uu___2195_78739.effects);
               generalize = (uu___2195_78739.generalize);
               letrecs = (uu___2195_78739.letrecs);
               top_level = (uu___2195_78739.top_level);
               check_uvars = (uu___2195_78739.check_uvars);
               use_eq = (uu___2195_78739.use_eq);
               is_iface = (uu___2195_78739.is_iface);
               admit = (uu___2195_78739.admit);
               lax = (uu___2195_78739.lax);
               lax_universes = (uu___2195_78739.lax_universes);
               phase1 = (uu___2195_78739.phase1);
               failhard = (uu___2195_78739.failhard);
               nosynth = (uu___2195_78739.nosynth);
               uvar_subtyping = (uu___2195_78739.uvar_subtyping);
               tc_term = (uu___2195_78739.tc_term);
               type_of = (uu___2195_78739.type_of);
               universe_of = (uu___2195_78739.universe_of);
               check_type_of = (uu___2195_78739.check_type_of);
               use_bv_sorts = (uu___2195_78739.use_bv_sorts);
               qtbl_name_and_index = (uu___2195_78739.qtbl_name_and_index);
               normalized_eff_names = (uu___2195_78739.normalized_eff_names);
               fv_delta_depths = (uu___2195_78739.fv_delta_depths);
               proof_ns = (uu___2195_78739.proof_ns);
               synth_hook = (uu___2195_78739.synth_hook);
               splice = (uu___2195_78739.splice);
               postprocess = (uu___2195_78739.postprocess);
               is_native_tactic = (uu___2195_78739.is_native_tactic);
               identifier_info = (uu___2195_78739.identifier_info);
               tc_hooks = (uu___2195_78739.tc_hooks);
               dsenv = (uu___2195_78739.dsenv);
               nbe = (uu___2195_78739.nbe)
             }))
    | uu____78740 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____78769  ->
             match uu____78769 with | (x,uu____78777) -> push_bv env1 x) env
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
            let uu___2209_78812 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2209_78812.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2209_78812.FStar_Syntax_Syntax.index);
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
      (let uu___2220_78854 = env  in
       {
         solver = (uu___2220_78854.solver);
         range = (uu___2220_78854.range);
         curmodule = (uu___2220_78854.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2220_78854.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2220_78854.sigtab);
         attrtab = (uu___2220_78854.attrtab);
         is_pattern = (uu___2220_78854.is_pattern);
         instantiate_imp = (uu___2220_78854.instantiate_imp);
         effects = (uu___2220_78854.effects);
         generalize = (uu___2220_78854.generalize);
         letrecs = (uu___2220_78854.letrecs);
         top_level = (uu___2220_78854.top_level);
         check_uvars = (uu___2220_78854.check_uvars);
         use_eq = (uu___2220_78854.use_eq);
         is_iface = (uu___2220_78854.is_iface);
         admit = (uu___2220_78854.admit);
         lax = (uu___2220_78854.lax);
         lax_universes = (uu___2220_78854.lax_universes);
         phase1 = (uu___2220_78854.phase1);
         failhard = (uu___2220_78854.failhard);
         nosynth = (uu___2220_78854.nosynth);
         uvar_subtyping = (uu___2220_78854.uvar_subtyping);
         tc_term = (uu___2220_78854.tc_term);
         type_of = (uu___2220_78854.type_of);
         universe_of = (uu___2220_78854.universe_of);
         check_type_of = (uu___2220_78854.check_type_of);
         use_bv_sorts = (uu___2220_78854.use_bv_sorts);
         qtbl_name_and_index = (uu___2220_78854.qtbl_name_and_index);
         normalized_eff_names = (uu___2220_78854.normalized_eff_names);
         fv_delta_depths = (uu___2220_78854.fv_delta_depths);
         proof_ns = (uu___2220_78854.proof_ns);
         synth_hook = (uu___2220_78854.synth_hook);
         splice = (uu___2220_78854.splice);
         postprocess = (uu___2220_78854.postprocess);
         is_native_tactic = (uu___2220_78854.is_native_tactic);
         identifier_info = (uu___2220_78854.identifier_info);
         tc_hooks = (uu___2220_78854.tc_hooks);
         dsenv = (uu___2220_78854.dsenv);
         nbe = (uu___2220_78854.nbe)
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
        let uu____78898 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____78898 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____78926 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____78926)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2235_78942 = env  in
      {
        solver = (uu___2235_78942.solver);
        range = (uu___2235_78942.range);
        curmodule = (uu___2235_78942.curmodule);
        gamma = (uu___2235_78942.gamma);
        gamma_sig = (uu___2235_78942.gamma_sig);
        gamma_cache = (uu___2235_78942.gamma_cache);
        modules = (uu___2235_78942.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2235_78942.sigtab);
        attrtab = (uu___2235_78942.attrtab);
        is_pattern = (uu___2235_78942.is_pattern);
        instantiate_imp = (uu___2235_78942.instantiate_imp);
        effects = (uu___2235_78942.effects);
        generalize = (uu___2235_78942.generalize);
        letrecs = (uu___2235_78942.letrecs);
        top_level = (uu___2235_78942.top_level);
        check_uvars = (uu___2235_78942.check_uvars);
        use_eq = false;
        is_iface = (uu___2235_78942.is_iface);
        admit = (uu___2235_78942.admit);
        lax = (uu___2235_78942.lax);
        lax_universes = (uu___2235_78942.lax_universes);
        phase1 = (uu___2235_78942.phase1);
        failhard = (uu___2235_78942.failhard);
        nosynth = (uu___2235_78942.nosynth);
        uvar_subtyping = (uu___2235_78942.uvar_subtyping);
        tc_term = (uu___2235_78942.tc_term);
        type_of = (uu___2235_78942.type_of);
        universe_of = (uu___2235_78942.universe_of);
        check_type_of = (uu___2235_78942.check_type_of);
        use_bv_sorts = (uu___2235_78942.use_bv_sorts);
        qtbl_name_and_index = (uu___2235_78942.qtbl_name_and_index);
        normalized_eff_names = (uu___2235_78942.normalized_eff_names);
        fv_delta_depths = (uu___2235_78942.fv_delta_depths);
        proof_ns = (uu___2235_78942.proof_ns);
        synth_hook = (uu___2235_78942.synth_hook);
        splice = (uu___2235_78942.splice);
        postprocess = (uu___2235_78942.postprocess);
        is_native_tactic = (uu___2235_78942.is_native_tactic);
        identifier_info = (uu___2235_78942.identifier_info);
        tc_hooks = (uu___2235_78942.tc_hooks);
        dsenv = (uu___2235_78942.dsenv);
        nbe = (uu___2235_78942.nbe)
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
    let uu____78973 = expected_typ env_  in
    ((let uu___2242_78979 = env_  in
      {
        solver = (uu___2242_78979.solver);
        range = (uu___2242_78979.range);
        curmodule = (uu___2242_78979.curmodule);
        gamma = (uu___2242_78979.gamma);
        gamma_sig = (uu___2242_78979.gamma_sig);
        gamma_cache = (uu___2242_78979.gamma_cache);
        modules = (uu___2242_78979.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2242_78979.sigtab);
        attrtab = (uu___2242_78979.attrtab);
        is_pattern = (uu___2242_78979.is_pattern);
        instantiate_imp = (uu___2242_78979.instantiate_imp);
        effects = (uu___2242_78979.effects);
        generalize = (uu___2242_78979.generalize);
        letrecs = (uu___2242_78979.letrecs);
        top_level = (uu___2242_78979.top_level);
        check_uvars = (uu___2242_78979.check_uvars);
        use_eq = false;
        is_iface = (uu___2242_78979.is_iface);
        admit = (uu___2242_78979.admit);
        lax = (uu___2242_78979.lax);
        lax_universes = (uu___2242_78979.lax_universes);
        phase1 = (uu___2242_78979.phase1);
        failhard = (uu___2242_78979.failhard);
        nosynth = (uu___2242_78979.nosynth);
        uvar_subtyping = (uu___2242_78979.uvar_subtyping);
        tc_term = (uu___2242_78979.tc_term);
        type_of = (uu___2242_78979.type_of);
        universe_of = (uu___2242_78979.universe_of);
        check_type_of = (uu___2242_78979.check_type_of);
        use_bv_sorts = (uu___2242_78979.use_bv_sorts);
        qtbl_name_and_index = (uu___2242_78979.qtbl_name_and_index);
        normalized_eff_names = (uu___2242_78979.normalized_eff_names);
        fv_delta_depths = (uu___2242_78979.fv_delta_depths);
        proof_ns = (uu___2242_78979.proof_ns);
        synth_hook = (uu___2242_78979.synth_hook);
        splice = (uu___2242_78979.splice);
        postprocess = (uu___2242_78979.postprocess);
        is_native_tactic = (uu___2242_78979.is_native_tactic);
        identifier_info = (uu___2242_78979.identifier_info);
        tc_hooks = (uu___2242_78979.tc_hooks);
        dsenv = (uu___2242_78979.dsenv);
        nbe = (uu___2242_78979.nbe)
      }), uu____78973)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____78991 =
      let uu____78994 = FStar_Ident.id_of_text ""  in [uu____78994]  in
    FStar_Ident.lid_of_ids uu____78991  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____79001 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____79001
        then
          let uu____79006 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____79006 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2250_79034 = env  in
       {
         solver = (uu___2250_79034.solver);
         range = (uu___2250_79034.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2250_79034.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2250_79034.expected_typ);
         sigtab = (uu___2250_79034.sigtab);
         attrtab = (uu___2250_79034.attrtab);
         is_pattern = (uu___2250_79034.is_pattern);
         instantiate_imp = (uu___2250_79034.instantiate_imp);
         effects = (uu___2250_79034.effects);
         generalize = (uu___2250_79034.generalize);
         letrecs = (uu___2250_79034.letrecs);
         top_level = (uu___2250_79034.top_level);
         check_uvars = (uu___2250_79034.check_uvars);
         use_eq = (uu___2250_79034.use_eq);
         is_iface = (uu___2250_79034.is_iface);
         admit = (uu___2250_79034.admit);
         lax = (uu___2250_79034.lax);
         lax_universes = (uu___2250_79034.lax_universes);
         phase1 = (uu___2250_79034.phase1);
         failhard = (uu___2250_79034.failhard);
         nosynth = (uu___2250_79034.nosynth);
         uvar_subtyping = (uu___2250_79034.uvar_subtyping);
         tc_term = (uu___2250_79034.tc_term);
         type_of = (uu___2250_79034.type_of);
         universe_of = (uu___2250_79034.universe_of);
         check_type_of = (uu___2250_79034.check_type_of);
         use_bv_sorts = (uu___2250_79034.use_bv_sorts);
         qtbl_name_and_index = (uu___2250_79034.qtbl_name_and_index);
         normalized_eff_names = (uu___2250_79034.normalized_eff_names);
         fv_delta_depths = (uu___2250_79034.fv_delta_depths);
         proof_ns = (uu___2250_79034.proof_ns);
         synth_hook = (uu___2250_79034.synth_hook);
         splice = (uu___2250_79034.splice);
         postprocess = (uu___2250_79034.postprocess);
         is_native_tactic = (uu___2250_79034.is_native_tactic);
         identifier_info = (uu___2250_79034.identifier_info);
         tc_hooks = (uu___2250_79034.tc_hooks);
         dsenv = (uu___2250_79034.dsenv);
         nbe = (uu___2250_79034.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79086)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79090,(uu____79091,t)))::tl1
          ->
          let uu____79112 =
            let uu____79115 = FStar_Syntax_Free.uvars t  in
            ext out uu____79115  in
          aux uu____79112 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79118;
            FStar_Syntax_Syntax.index = uu____79119;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79127 =
            let uu____79130 = FStar_Syntax_Free.uvars t  in
            ext out uu____79130  in
          aux uu____79127 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79188)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79192,(uu____79193,t)))::tl1
          ->
          let uu____79214 =
            let uu____79217 = FStar_Syntax_Free.univs t  in
            ext out uu____79217  in
          aux uu____79214 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79220;
            FStar_Syntax_Syntax.index = uu____79221;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79229 =
            let uu____79232 = FStar_Syntax_Free.univs t  in
            ext out uu____79232  in
          aux uu____79229 tl1
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
          let uu____79294 = FStar_Util.set_add uname out  in
          aux uu____79294 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79297,(uu____79298,t)))::tl1
          ->
          let uu____79319 =
            let uu____79322 = FStar_Syntax_Free.univnames t  in
            ext out uu____79322  in
          aux uu____79319 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79325;
            FStar_Syntax_Syntax.index = uu____79326;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79334 =
            let uu____79337 = FStar_Syntax_Free.univnames t  in
            ext out uu____79337  in
          aux uu____79334 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_79358  ->
            match uu___457_79358 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____79362 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____79375 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____79386 =
      let uu____79395 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____79395
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____79386 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____79443 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_79456  ->
              match uu___458_79456 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____79459 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____79459
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____79465) ->
                  let uu____79482 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____79482))
       in
    FStar_All.pipe_right uu____79443 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_79496  ->
    match uu___459_79496 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____79502 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____79502
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____79525  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____79580) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____79613,uu____79614) -> false  in
      let uu____79628 =
        FStar_List.tryFind
          (fun uu____79650  ->
             match uu____79650 with | (p,uu____79661) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____79628 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____79680,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____79710 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____79710
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2393_79732 = e  in
        {
          solver = (uu___2393_79732.solver);
          range = (uu___2393_79732.range);
          curmodule = (uu___2393_79732.curmodule);
          gamma = (uu___2393_79732.gamma);
          gamma_sig = (uu___2393_79732.gamma_sig);
          gamma_cache = (uu___2393_79732.gamma_cache);
          modules = (uu___2393_79732.modules);
          expected_typ = (uu___2393_79732.expected_typ);
          sigtab = (uu___2393_79732.sigtab);
          attrtab = (uu___2393_79732.attrtab);
          is_pattern = (uu___2393_79732.is_pattern);
          instantiate_imp = (uu___2393_79732.instantiate_imp);
          effects = (uu___2393_79732.effects);
          generalize = (uu___2393_79732.generalize);
          letrecs = (uu___2393_79732.letrecs);
          top_level = (uu___2393_79732.top_level);
          check_uvars = (uu___2393_79732.check_uvars);
          use_eq = (uu___2393_79732.use_eq);
          is_iface = (uu___2393_79732.is_iface);
          admit = (uu___2393_79732.admit);
          lax = (uu___2393_79732.lax);
          lax_universes = (uu___2393_79732.lax_universes);
          phase1 = (uu___2393_79732.phase1);
          failhard = (uu___2393_79732.failhard);
          nosynth = (uu___2393_79732.nosynth);
          uvar_subtyping = (uu___2393_79732.uvar_subtyping);
          tc_term = (uu___2393_79732.tc_term);
          type_of = (uu___2393_79732.type_of);
          universe_of = (uu___2393_79732.universe_of);
          check_type_of = (uu___2393_79732.check_type_of);
          use_bv_sorts = (uu___2393_79732.use_bv_sorts);
          qtbl_name_and_index = (uu___2393_79732.qtbl_name_and_index);
          normalized_eff_names = (uu___2393_79732.normalized_eff_names);
          fv_delta_depths = (uu___2393_79732.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2393_79732.synth_hook);
          splice = (uu___2393_79732.splice);
          postprocess = (uu___2393_79732.postprocess);
          is_native_tactic = (uu___2393_79732.is_native_tactic);
          identifier_info = (uu___2393_79732.identifier_info);
          tc_hooks = (uu___2393_79732.tc_hooks);
          dsenv = (uu___2393_79732.dsenv);
          nbe = (uu___2393_79732.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2402_79780 = e  in
      {
        solver = (uu___2402_79780.solver);
        range = (uu___2402_79780.range);
        curmodule = (uu___2402_79780.curmodule);
        gamma = (uu___2402_79780.gamma);
        gamma_sig = (uu___2402_79780.gamma_sig);
        gamma_cache = (uu___2402_79780.gamma_cache);
        modules = (uu___2402_79780.modules);
        expected_typ = (uu___2402_79780.expected_typ);
        sigtab = (uu___2402_79780.sigtab);
        attrtab = (uu___2402_79780.attrtab);
        is_pattern = (uu___2402_79780.is_pattern);
        instantiate_imp = (uu___2402_79780.instantiate_imp);
        effects = (uu___2402_79780.effects);
        generalize = (uu___2402_79780.generalize);
        letrecs = (uu___2402_79780.letrecs);
        top_level = (uu___2402_79780.top_level);
        check_uvars = (uu___2402_79780.check_uvars);
        use_eq = (uu___2402_79780.use_eq);
        is_iface = (uu___2402_79780.is_iface);
        admit = (uu___2402_79780.admit);
        lax = (uu___2402_79780.lax);
        lax_universes = (uu___2402_79780.lax_universes);
        phase1 = (uu___2402_79780.phase1);
        failhard = (uu___2402_79780.failhard);
        nosynth = (uu___2402_79780.nosynth);
        uvar_subtyping = (uu___2402_79780.uvar_subtyping);
        tc_term = (uu___2402_79780.tc_term);
        type_of = (uu___2402_79780.type_of);
        universe_of = (uu___2402_79780.universe_of);
        check_type_of = (uu___2402_79780.check_type_of);
        use_bv_sorts = (uu___2402_79780.use_bv_sorts);
        qtbl_name_and_index = (uu___2402_79780.qtbl_name_and_index);
        normalized_eff_names = (uu___2402_79780.normalized_eff_names);
        fv_delta_depths = (uu___2402_79780.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2402_79780.synth_hook);
        splice = (uu___2402_79780.splice);
        postprocess = (uu___2402_79780.postprocess);
        is_native_tactic = (uu___2402_79780.is_native_tactic);
        identifier_info = (uu___2402_79780.identifier_info);
        tc_hooks = (uu___2402_79780.tc_hooks);
        dsenv = (uu___2402_79780.dsenv);
        nbe = (uu___2402_79780.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____79796 = FStar_Syntax_Free.names t  in
      let uu____79799 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____79796 uu____79799
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____79822 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____79822
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____79832 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____79832
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____79853 =
      match uu____79853 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____79873 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____79873)
       in
    let uu____79881 =
      let uu____79885 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____79885 FStar_List.rev  in
    FStar_All.pipe_right uu____79881 (FStar_String.concat " ")
  
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
                  (let uu____79955 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____79955 with
                   | FStar_Pervasives_Native.Some uu____79959 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____79962 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____79972;
        univ_ineqs = uu____79973; implicits = uu____79974;_} -> true
    | uu____79986 -> false
  
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
          let uu___2446_80017 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2446_80017.deferred);
            univ_ineqs = (uu___2446_80017.univ_ineqs);
            implicits = (uu___2446_80017.implicits)
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
          let uu____80056 = FStar_Options.defensive ()  in
          if uu____80056
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____80062 =
              let uu____80064 =
                let uu____80066 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____80066  in
              Prims.op_Negation uu____80064  in
            (if uu____80062
             then
               let uu____80073 =
                 let uu____80079 =
                   let uu____80081 = FStar_Syntax_Print.term_to_string t  in
                   let uu____80083 =
                     let uu____80085 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____80085
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____80081 uu____80083
                    in
                 (FStar_Errors.Warning_Defensive, uu____80079)  in
               FStar_Errors.log_issue rng uu____80073
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
          let uu____80125 =
            let uu____80127 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80127  in
          if uu____80125
          then ()
          else
            (let uu____80132 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____80132 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____80158 =
            let uu____80160 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80160  in
          if uu____80158
          then ()
          else
            (let uu____80165 = bound_vars e  in
             def_check_closed_in rng msg uu____80165 t)
  
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
          let uu___2483_80204 = g  in
          let uu____80205 =
            let uu____80206 =
              let uu____80207 =
                let uu____80214 =
                  let uu____80215 =
                    let uu____80232 =
                      let uu____80243 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____80243]  in
                    (f, uu____80232)  in
                  FStar_Syntax_Syntax.Tm_app uu____80215  in
                FStar_Syntax_Syntax.mk uu____80214  in
              uu____80207 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _80283  -> FStar_TypeChecker_Common.NonTrivial _80283)
              uu____80206
             in
          {
            guard_f = uu____80205;
            deferred = (uu___2483_80204.deferred);
            univ_ineqs = (uu___2483_80204.univ_ineqs);
            implicits = (uu___2483_80204.implicits)
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
          let uu___2490_80301 = g  in
          let uu____80302 =
            let uu____80303 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80303  in
          {
            guard_f = uu____80302;
            deferred = (uu___2490_80301.deferred);
            univ_ineqs = (uu___2490_80301.univ_ineqs);
            implicits = (uu___2490_80301.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2495_80320 = g  in
          let uu____80321 =
            let uu____80322 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____80322  in
          {
            guard_f = uu____80321;
            deferred = (uu___2495_80320.deferred);
            univ_ineqs = (uu___2495_80320.univ_ineqs);
            implicits = (uu___2495_80320.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2499_80324 = g  in
          let uu____80325 =
            let uu____80326 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80326  in
          {
            guard_f = uu____80325;
            deferred = (uu___2499_80324.deferred);
            univ_ineqs = (uu___2499_80324.univ_ineqs);
            implicits = (uu___2499_80324.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____80333 ->
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
          let uu____80350 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____80350
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____80357 =
      let uu____80358 = FStar_Syntax_Util.unmeta t  in
      uu____80358.FStar_Syntax_Syntax.n  in
    match uu____80357 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____80362 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____80405 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____80405;
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
                       let uu____80500 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____80500
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2554_80507 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2554_80507.deferred);
              univ_ineqs = (uu___2554_80507.univ_ineqs);
              implicits = (uu___2554_80507.implicits)
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
               let uu____80541 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____80541
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
            let uu___2569_80568 = g  in
            let uu____80569 =
              let uu____80570 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____80570  in
            {
              guard_f = uu____80569;
              deferred = (uu___2569_80568.deferred);
              univ_ineqs = (uu___2569_80568.univ_ineqs);
              implicits = (uu___2569_80568.implicits)
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
              let uu____80628 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____80628 with
              | FStar_Pervasives_Native.Some
                  (uu____80653::(tm,uu____80655)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____80719 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____80737 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____80737;
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
                      let uu___2591_80769 = trivial_guard  in
                      {
                        guard_f = (uu___2591_80769.guard_f);
                        deferred = (uu___2591_80769.deferred);
                        univ_ineqs = (uu___2591_80769.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____80787  -> ());
    push = (fun uu____80789  -> ());
    pop = (fun uu____80792  -> ());
    snapshot =
      (fun uu____80795  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____80814  -> fun uu____80815  -> ());
    encode_sig = (fun uu____80830  -> fun uu____80831  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____80837 =
             let uu____80844 = FStar_Options.peek ()  in (e, g, uu____80844)
              in
           [uu____80837]);
    solve = (fun uu____80860  -> fun uu____80861  -> fun uu____80862  -> ());
    finish = (fun uu____80869  -> ());
    refresh = (fun uu____80871  -> ())
  } 