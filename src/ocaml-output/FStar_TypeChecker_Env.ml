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
  fun projectee  -> match projectee with | Beta  -> true | uu____103 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____114 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____125 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____137 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____155 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____166 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____177 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____188 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____199 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____210 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____222 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____243 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____270 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____297 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____321 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____332 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____343 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____354 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____365 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____376 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____387 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____398 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____409 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____420 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____431 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____442 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____453 -> false
  
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
      | uu____513 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____539 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____550 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____561 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____573 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type mlift =
  {
  mlift_t: FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ;
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
let (__proj__Mkmlift__item__mlift_t :
  mlift -> FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_t
  
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_term
  
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
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t)
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t
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
    ;
  strict_args_tab:
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap }
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> solver
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> range
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> curmodule
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> gamma
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> gamma_sig
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> gamma_cache
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> modules
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> expected_typ
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> sigtab
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> attrtab
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> is_pattern
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> instantiate_imp
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> effects
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> generalize
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> letrecs
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> top_level
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> check_uvars
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> use_eq
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> is_iface
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> admit1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> lax1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> lax_universes
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> phase1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> failhard
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> nosynth
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> type_of
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> check_type_of
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> use_bv_sorts
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        qtbl_name_and_index
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} ->
        normalized_eff_names
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> fv_delta_depths
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> proof_ns
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> synth_hook
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> splice1
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> postprocess
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> is_native_tactic
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> identifier_info
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> tc_hooks
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> dsenv
  
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
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
        tc_hooks; dsenv; nbe = nbe1; strict_args_tab;_} -> strict_args_tab
  
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
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
  
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicit = FStar_TypeChecker_Common.implicit
type implicits = FStar_TypeChecker_Common.implicits
type guard_t = FStar_TypeChecker_Common.guard_t
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
           (fun uu___0_12215  ->
              match uu___0_12215 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12218 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12218  in
                  let uu____12219 =
                    let uu____12220 = FStar_Syntax_Subst.compress y  in
                    uu____12220.FStar_Syntax_Syntax.n  in
                  (match uu____12219 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12224 =
                         let uu___311_12225 = y1  in
                         let uu____12226 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___311_12225.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___311_12225.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12226
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12224
                   | uu____12229 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___317_12243 = env  in
      let uu____12244 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___317_12243.solver);
        range = (uu___317_12243.range);
        curmodule = (uu___317_12243.curmodule);
        gamma = uu____12244;
        gamma_sig = (uu___317_12243.gamma_sig);
        gamma_cache = (uu___317_12243.gamma_cache);
        modules = (uu___317_12243.modules);
        expected_typ = (uu___317_12243.expected_typ);
        sigtab = (uu___317_12243.sigtab);
        attrtab = (uu___317_12243.attrtab);
        is_pattern = (uu___317_12243.is_pattern);
        instantiate_imp = (uu___317_12243.instantiate_imp);
        effects = (uu___317_12243.effects);
        generalize = (uu___317_12243.generalize);
        letrecs = (uu___317_12243.letrecs);
        top_level = (uu___317_12243.top_level);
        check_uvars = (uu___317_12243.check_uvars);
        use_eq = (uu___317_12243.use_eq);
        is_iface = (uu___317_12243.is_iface);
        admit = (uu___317_12243.admit);
        lax = (uu___317_12243.lax);
        lax_universes = (uu___317_12243.lax_universes);
        phase1 = (uu___317_12243.phase1);
        failhard = (uu___317_12243.failhard);
        nosynth = (uu___317_12243.nosynth);
        uvar_subtyping = (uu___317_12243.uvar_subtyping);
        tc_term = (uu___317_12243.tc_term);
        type_of = (uu___317_12243.type_of);
        universe_of = (uu___317_12243.universe_of);
        check_type_of = (uu___317_12243.check_type_of);
        use_bv_sorts = (uu___317_12243.use_bv_sorts);
        qtbl_name_and_index = (uu___317_12243.qtbl_name_and_index);
        normalized_eff_names = (uu___317_12243.normalized_eff_names);
        fv_delta_depths = (uu___317_12243.fv_delta_depths);
        proof_ns = (uu___317_12243.proof_ns);
        synth_hook = (uu___317_12243.synth_hook);
        splice = (uu___317_12243.splice);
        postprocess = (uu___317_12243.postprocess);
        is_native_tactic = (uu___317_12243.is_native_tactic);
        identifier_info = (uu___317_12243.identifier_info);
        tc_hooks = (uu___317_12243.tc_hooks);
        dsenv = (uu___317_12243.dsenv);
        nbe = (uu___317_12243.nbe);
        strict_args_tab = (uu___317_12243.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12252  -> fun uu____12253  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___324_12275 = env  in
      {
        solver = (uu___324_12275.solver);
        range = (uu___324_12275.range);
        curmodule = (uu___324_12275.curmodule);
        gamma = (uu___324_12275.gamma);
        gamma_sig = (uu___324_12275.gamma_sig);
        gamma_cache = (uu___324_12275.gamma_cache);
        modules = (uu___324_12275.modules);
        expected_typ = (uu___324_12275.expected_typ);
        sigtab = (uu___324_12275.sigtab);
        attrtab = (uu___324_12275.attrtab);
        is_pattern = (uu___324_12275.is_pattern);
        instantiate_imp = (uu___324_12275.instantiate_imp);
        effects = (uu___324_12275.effects);
        generalize = (uu___324_12275.generalize);
        letrecs = (uu___324_12275.letrecs);
        top_level = (uu___324_12275.top_level);
        check_uvars = (uu___324_12275.check_uvars);
        use_eq = (uu___324_12275.use_eq);
        is_iface = (uu___324_12275.is_iface);
        admit = (uu___324_12275.admit);
        lax = (uu___324_12275.lax);
        lax_universes = (uu___324_12275.lax_universes);
        phase1 = (uu___324_12275.phase1);
        failhard = (uu___324_12275.failhard);
        nosynth = (uu___324_12275.nosynth);
        uvar_subtyping = (uu___324_12275.uvar_subtyping);
        tc_term = (uu___324_12275.tc_term);
        type_of = (uu___324_12275.type_of);
        universe_of = (uu___324_12275.universe_of);
        check_type_of = (uu___324_12275.check_type_of);
        use_bv_sorts = (uu___324_12275.use_bv_sorts);
        qtbl_name_and_index = (uu___324_12275.qtbl_name_and_index);
        normalized_eff_names = (uu___324_12275.normalized_eff_names);
        fv_delta_depths = (uu___324_12275.fv_delta_depths);
        proof_ns = (uu___324_12275.proof_ns);
        synth_hook = (uu___324_12275.synth_hook);
        splice = (uu___324_12275.splice);
        postprocess = (uu___324_12275.postprocess);
        is_native_tactic = (uu___324_12275.is_native_tactic);
        identifier_info = (uu___324_12275.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___324_12275.dsenv);
        nbe = (uu___324_12275.nbe);
        strict_args_tab = (uu___324_12275.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___328_12287 = e  in
      let uu____12288 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___328_12287.solver);
        range = (uu___328_12287.range);
        curmodule = (uu___328_12287.curmodule);
        gamma = (uu___328_12287.gamma);
        gamma_sig = (uu___328_12287.gamma_sig);
        gamma_cache = (uu___328_12287.gamma_cache);
        modules = (uu___328_12287.modules);
        expected_typ = (uu___328_12287.expected_typ);
        sigtab = (uu___328_12287.sigtab);
        attrtab = (uu___328_12287.attrtab);
        is_pattern = (uu___328_12287.is_pattern);
        instantiate_imp = (uu___328_12287.instantiate_imp);
        effects = (uu___328_12287.effects);
        generalize = (uu___328_12287.generalize);
        letrecs = (uu___328_12287.letrecs);
        top_level = (uu___328_12287.top_level);
        check_uvars = (uu___328_12287.check_uvars);
        use_eq = (uu___328_12287.use_eq);
        is_iface = (uu___328_12287.is_iface);
        admit = (uu___328_12287.admit);
        lax = (uu___328_12287.lax);
        lax_universes = (uu___328_12287.lax_universes);
        phase1 = (uu___328_12287.phase1);
        failhard = (uu___328_12287.failhard);
        nosynth = (uu___328_12287.nosynth);
        uvar_subtyping = (uu___328_12287.uvar_subtyping);
        tc_term = (uu___328_12287.tc_term);
        type_of = (uu___328_12287.type_of);
        universe_of = (uu___328_12287.universe_of);
        check_type_of = (uu___328_12287.check_type_of);
        use_bv_sorts = (uu___328_12287.use_bv_sorts);
        qtbl_name_and_index = (uu___328_12287.qtbl_name_and_index);
        normalized_eff_names = (uu___328_12287.normalized_eff_names);
        fv_delta_depths = (uu___328_12287.fv_delta_depths);
        proof_ns = (uu___328_12287.proof_ns);
        synth_hook = (uu___328_12287.synth_hook);
        splice = (uu___328_12287.splice);
        postprocess = (uu___328_12287.postprocess);
        is_native_tactic = (uu___328_12287.is_native_tactic);
        identifier_info = (uu___328_12287.identifier_info);
        tc_hooks = (uu___328_12287.tc_hooks);
        dsenv = uu____12288;
        nbe = (uu___328_12287.nbe);
        strict_args_tab = (uu___328_12287.strict_args_tab)
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
      | (NoDelta ,uu____12317) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12320,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12322,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12325 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12339 . unit -> 'Auu____12339 FStar_Util.smap =
  fun uu____12346  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12352 . unit -> 'Auu____12352 FStar_Util.smap =
  fun uu____12359  -> FStar_Util.smap_create (Prims.of_int (100)) 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
           guard_t))
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
                  let uu____12497 = new_gamma_cache ()  in
                  let uu____12500 = new_sigtab ()  in
                  let uu____12503 = new_sigtab ()  in
                  let uu____12510 =
                    let uu____12525 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____12525, FStar_Pervasives_Native.None)  in
                  let uu____12546 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12550 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____12554 = FStar_Options.using_facts_from ()  in
                  let uu____12555 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12558 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____12559 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12497;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12500;
                    attrtab = uu____12503;
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
                    qtbl_name_and_index = uu____12510;
                    normalized_eff_names = uu____12546;
                    fv_delta_depths = uu____12550;
                    proof_ns = uu____12554;
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
                    is_native_tactic = (fun uu____12634  -> false);
                    identifier_info = uu____12555;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12558;
                    nbe = nbe1;
                    strict_args_tab = uu____12559
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
  fun uu____12713  ->
    let uu____12714 = FStar_ST.op_Bang query_indices  in
    match uu____12714 with
    | [] -> failwith "Empty query indices!"
    | uu____12769 ->
        let uu____12779 =
          let uu____12789 =
            let uu____12797 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12797  in
          let uu____12851 = FStar_ST.op_Bang query_indices  in uu____12789 ::
            uu____12851
           in
        FStar_ST.op_Colon_Equals query_indices uu____12779
  
let (pop_query_indices : unit -> unit) =
  fun uu____12947  ->
    let uu____12948 = FStar_ST.op_Bang query_indices  in
    match uu____12948 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13075  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13112  ->
    match uu____13112 with
    | (l,n1) ->
        let uu____13122 = FStar_ST.op_Bang query_indices  in
        (match uu____13122 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13244 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13267  ->
    let uu____13268 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13268
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13336 =
       let uu____13339 = FStar_ST.op_Bang stack  in env :: uu____13339  in
     FStar_ST.op_Colon_Equals stack uu____13336);
    (let uu___396_13388 = env  in
     let uu____13389 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13392 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13395 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13402 =
       let uu____13417 =
         let uu____13421 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13421  in
       let uu____13453 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13417, uu____13453)  in
     let uu____13502 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13505 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13508 =
       let uu____13511 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13511  in
     let uu____13531 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___396_13388.solver);
       range = (uu___396_13388.range);
       curmodule = (uu___396_13388.curmodule);
       gamma = (uu___396_13388.gamma);
       gamma_sig = (uu___396_13388.gamma_sig);
       gamma_cache = uu____13389;
       modules = (uu___396_13388.modules);
       expected_typ = (uu___396_13388.expected_typ);
       sigtab = uu____13392;
       attrtab = uu____13395;
       is_pattern = (uu___396_13388.is_pattern);
       instantiate_imp = (uu___396_13388.instantiate_imp);
       effects = (uu___396_13388.effects);
       generalize = (uu___396_13388.generalize);
       letrecs = (uu___396_13388.letrecs);
       top_level = (uu___396_13388.top_level);
       check_uvars = (uu___396_13388.check_uvars);
       use_eq = (uu___396_13388.use_eq);
       is_iface = (uu___396_13388.is_iface);
       admit = (uu___396_13388.admit);
       lax = (uu___396_13388.lax);
       lax_universes = (uu___396_13388.lax_universes);
       phase1 = (uu___396_13388.phase1);
       failhard = (uu___396_13388.failhard);
       nosynth = (uu___396_13388.nosynth);
       uvar_subtyping = (uu___396_13388.uvar_subtyping);
       tc_term = (uu___396_13388.tc_term);
       type_of = (uu___396_13388.type_of);
       universe_of = (uu___396_13388.universe_of);
       check_type_of = (uu___396_13388.check_type_of);
       use_bv_sorts = (uu___396_13388.use_bv_sorts);
       qtbl_name_and_index = uu____13402;
       normalized_eff_names = uu____13502;
       fv_delta_depths = uu____13505;
       proof_ns = (uu___396_13388.proof_ns);
       synth_hook = (uu___396_13388.synth_hook);
       splice = (uu___396_13388.splice);
       postprocess = (uu___396_13388.postprocess);
       is_native_tactic = (uu___396_13388.is_native_tactic);
       identifier_info = uu____13508;
       tc_hooks = (uu___396_13388.tc_hooks);
       dsenv = (uu___396_13388.dsenv);
       nbe = (uu___396_13388.nbe);
       strict_args_tab = uu____13531
     })
  
let (pop_stack : unit -> env) =
  fun uu____13549  ->
    let uu____13550 = FStar_ST.op_Bang stack  in
    match uu____13550 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13604 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13694  ->
           let uu____13695 = snapshot_stack env  in
           match uu____13695 with
           | (stack_depth,env1) ->
               let uu____13729 = snapshot_query_indices ()  in
               (match uu____13729 with
                | (query_indices_depth,()) ->
                    let uu____13762 = (env1.solver).snapshot msg  in
                    (match uu____13762 with
                     | (solver_depth,()) ->
                         let uu____13819 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13819 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___421_13886 = env1  in
                                 {
                                   solver = (uu___421_13886.solver);
                                   range = (uu___421_13886.range);
                                   curmodule = (uu___421_13886.curmodule);
                                   gamma = (uu___421_13886.gamma);
                                   gamma_sig = (uu___421_13886.gamma_sig);
                                   gamma_cache = (uu___421_13886.gamma_cache);
                                   modules = (uu___421_13886.modules);
                                   expected_typ =
                                     (uu___421_13886.expected_typ);
                                   sigtab = (uu___421_13886.sigtab);
                                   attrtab = (uu___421_13886.attrtab);
                                   is_pattern = (uu___421_13886.is_pattern);
                                   instantiate_imp =
                                     (uu___421_13886.instantiate_imp);
                                   effects = (uu___421_13886.effects);
                                   generalize = (uu___421_13886.generalize);
                                   letrecs = (uu___421_13886.letrecs);
                                   top_level = (uu___421_13886.top_level);
                                   check_uvars = (uu___421_13886.check_uvars);
                                   use_eq = (uu___421_13886.use_eq);
                                   is_iface = (uu___421_13886.is_iface);
                                   admit = (uu___421_13886.admit);
                                   lax = (uu___421_13886.lax);
                                   lax_universes =
                                     (uu___421_13886.lax_universes);
                                   phase1 = (uu___421_13886.phase1);
                                   failhard = (uu___421_13886.failhard);
                                   nosynth = (uu___421_13886.nosynth);
                                   uvar_subtyping =
                                     (uu___421_13886.uvar_subtyping);
                                   tc_term = (uu___421_13886.tc_term);
                                   type_of = (uu___421_13886.type_of);
                                   universe_of = (uu___421_13886.universe_of);
                                   check_type_of =
                                     (uu___421_13886.check_type_of);
                                   use_bv_sorts =
                                     (uu___421_13886.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___421_13886.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___421_13886.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___421_13886.fv_delta_depths);
                                   proof_ns = (uu___421_13886.proof_ns);
                                   synth_hook = (uu___421_13886.synth_hook);
                                   splice = (uu___421_13886.splice);
                                   postprocess = (uu___421_13886.postprocess);
                                   is_native_tactic =
                                     (uu___421_13886.is_native_tactic);
                                   identifier_info =
                                     (uu___421_13886.identifier_info);
                                   tc_hooks = (uu___421_13886.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___421_13886.nbe);
                                   strict_args_tab =
                                     (uu___421_13886.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13920  ->
             let uu____13921 =
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
             match uu____13921 with
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
                             ((let uu____14101 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14101
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14117 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14117
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14149,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14191 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14221  ->
                  match uu____14221 with
                  | (m,uu____14229) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14191 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___466_14244 = env  in
               {
                 solver = (uu___466_14244.solver);
                 range = (uu___466_14244.range);
                 curmodule = (uu___466_14244.curmodule);
                 gamma = (uu___466_14244.gamma);
                 gamma_sig = (uu___466_14244.gamma_sig);
                 gamma_cache = (uu___466_14244.gamma_cache);
                 modules = (uu___466_14244.modules);
                 expected_typ = (uu___466_14244.expected_typ);
                 sigtab = (uu___466_14244.sigtab);
                 attrtab = (uu___466_14244.attrtab);
                 is_pattern = (uu___466_14244.is_pattern);
                 instantiate_imp = (uu___466_14244.instantiate_imp);
                 effects = (uu___466_14244.effects);
                 generalize = (uu___466_14244.generalize);
                 letrecs = (uu___466_14244.letrecs);
                 top_level = (uu___466_14244.top_level);
                 check_uvars = (uu___466_14244.check_uvars);
                 use_eq = (uu___466_14244.use_eq);
                 is_iface = (uu___466_14244.is_iface);
                 admit = (uu___466_14244.admit);
                 lax = (uu___466_14244.lax);
                 lax_universes = (uu___466_14244.lax_universes);
                 phase1 = (uu___466_14244.phase1);
                 failhard = (uu___466_14244.failhard);
                 nosynth = (uu___466_14244.nosynth);
                 uvar_subtyping = (uu___466_14244.uvar_subtyping);
                 tc_term = (uu___466_14244.tc_term);
                 type_of = (uu___466_14244.type_of);
                 universe_of = (uu___466_14244.universe_of);
                 check_type_of = (uu___466_14244.check_type_of);
                 use_bv_sorts = (uu___466_14244.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___466_14244.normalized_eff_names);
                 fv_delta_depths = (uu___466_14244.fv_delta_depths);
                 proof_ns = (uu___466_14244.proof_ns);
                 synth_hook = (uu___466_14244.synth_hook);
                 splice = (uu___466_14244.splice);
                 postprocess = (uu___466_14244.postprocess);
                 is_native_tactic = (uu___466_14244.is_native_tactic);
                 identifier_info = (uu___466_14244.identifier_info);
                 tc_hooks = (uu___466_14244.tc_hooks);
                 dsenv = (uu___466_14244.dsenv);
                 nbe = (uu___466_14244.nbe);
                 strict_args_tab = (uu___466_14244.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14261,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___475_14277 = env  in
               {
                 solver = (uu___475_14277.solver);
                 range = (uu___475_14277.range);
                 curmodule = (uu___475_14277.curmodule);
                 gamma = (uu___475_14277.gamma);
                 gamma_sig = (uu___475_14277.gamma_sig);
                 gamma_cache = (uu___475_14277.gamma_cache);
                 modules = (uu___475_14277.modules);
                 expected_typ = (uu___475_14277.expected_typ);
                 sigtab = (uu___475_14277.sigtab);
                 attrtab = (uu___475_14277.attrtab);
                 is_pattern = (uu___475_14277.is_pattern);
                 instantiate_imp = (uu___475_14277.instantiate_imp);
                 effects = (uu___475_14277.effects);
                 generalize = (uu___475_14277.generalize);
                 letrecs = (uu___475_14277.letrecs);
                 top_level = (uu___475_14277.top_level);
                 check_uvars = (uu___475_14277.check_uvars);
                 use_eq = (uu___475_14277.use_eq);
                 is_iface = (uu___475_14277.is_iface);
                 admit = (uu___475_14277.admit);
                 lax = (uu___475_14277.lax);
                 lax_universes = (uu___475_14277.lax_universes);
                 phase1 = (uu___475_14277.phase1);
                 failhard = (uu___475_14277.failhard);
                 nosynth = (uu___475_14277.nosynth);
                 uvar_subtyping = (uu___475_14277.uvar_subtyping);
                 tc_term = (uu___475_14277.tc_term);
                 type_of = (uu___475_14277.type_of);
                 universe_of = (uu___475_14277.universe_of);
                 check_type_of = (uu___475_14277.check_type_of);
                 use_bv_sorts = (uu___475_14277.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___475_14277.normalized_eff_names);
                 fv_delta_depths = (uu___475_14277.fv_delta_depths);
                 proof_ns = (uu___475_14277.proof_ns);
                 synth_hook = (uu___475_14277.synth_hook);
                 splice = (uu___475_14277.splice);
                 postprocess = (uu___475_14277.postprocess);
                 is_native_tactic = (uu___475_14277.is_native_tactic);
                 identifier_info = (uu___475_14277.identifier_info);
                 tc_hooks = (uu___475_14277.tc_hooks);
                 dsenv = (uu___475_14277.dsenv);
                 nbe = (uu___475_14277.nbe);
                 strict_args_tab = (uu___475_14277.strict_args_tab)
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
        (let uu___482_14320 = e  in
         {
           solver = (uu___482_14320.solver);
           range = r;
           curmodule = (uu___482_14320.curmodule);
           gamma = (uu___482_14320.gamma);
           gamma_sig = (uu___482_14320.gamma_sig);
           gamma_cache = (uu___482_14320.gamma_cache);
           modules = (uu___482_14320.modules);
           expected_typ = (uu___482_14320.expected_typ);
           sigtab = (uu___482_14320.sigtab);
           attrtab = (uu___482_14320.attrtab);
           is_pattern = (uu___482_14320.is_pattern);
           instantiate_imp = (uu___482_14320.instantiate_imp);
           effects = (uu___482_14320.effects);
           generalize = (uu___482_14320.generalize);
           letrecs = (uu___482_14320.letrecs);
           top_level = (uu___482_14320.top_level);
           check_uvars = (uu___482_14320.check_uvars);
           use_eq = (uu___482_14320.use_eq);
           is_iface = (uu___482_14320.is_iface);
           admit = (uu___482_14320.admit);
           lax = (uu___482_14320.lax);
           lax_universes = (uu___482_14320.lax_universes);
           phase1 = (uu___482_14320.phase1);
           failhard = (uu___482_14320.failhard);
           nosynth = (uu___482_14320.nosynth);
           uvar_subtyping = (uu___482_14320.uvar_subtyping);
           tc_term = (uu___482_14320.tc_term);
           type_of = (uu___482_14320.type_of);
           universe_of = (uu___482_14320.universe_of);
           check_type_of = (uu___482_14320.check_type_of);
           use_bv_sorts = (uu___482_14320.use_bv_sorts);
           qtbl_name_and_index = (uu___482_14320.qtbl_name_and_index);
           normalized_eff_names = (uu___482_14320.normalized_eff_names);
           fv_delta_depths = (uu___482_14320.fv_delta_depths);
           proof_ns = (uu___482_14320.proof_ns);
           synth_hook = (uu___482_14320.synth_hook);
           splice = (uu___482_14320.splice);
           postprocess = (uu___482_14320.postprocess);
           is_native_tactic = (uu___482_14320.is_native_tactic);
           identifier_info = (uu___482_14320.identifier_info);
           tc_hooks = (uu___482_14320.tc_hooks);
           dsenv = (uu___482_14320.dsenv);
           nbe = (uu___482_14320.nbe);
           strict_args_tab = (uu___482_14320.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14340 =
        let uu____14341 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14341 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14340
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14396 =
          let uu____14397 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14397 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14396
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14452 =
          let uu____14453 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14453 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14452
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14508 =
        let uu____14509 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14509 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14508
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___499_14573 = env  in
      {
        solver = (uu___499_14573.solver);
        range = (uu___499_14573.range);
        curmodule = lid;
        gamma = (uu___499_14573.gamma);
        gamma_sig = (uu___499_14573.gamma_sig);
        gamma_cache = (uu___499_14573.gamma_cache);
        modules = (uu___499_14573.modules);
        expected_typ = (uu___499_14573.expected_typ);
        sigtab = (uu___499_14573.sigtab);
        attrtab = (uu___499_14573.attrtab);
        is_pattern = (uu___499_14573.is_pattern);
        instantiate_imp = (uu___499_14573.instantiate_imp);
        effects = (uu___499_14573.effects);
        generalize = (uu___499_14573.generalize);
        letrecs = (uu___499_14573.letrecs);
        top_level = (uu___499_14573.top_level);
        check_uvars = (uu___499_14573.check_uvars);
        use_eq = (uu___499_14573.use_eq);
        is_iface = (uu___499_14573.is_iface);
        admit = (uu___499_14573.admit);
        lax = (uu___499_14573.lax);
        lax_universes = (uu___499_14573.lax_universes);
        phase1 = (uu___499_14573.phase1);
        failhard = (uu___499_14573.failhard);
        nosynth = (uu___499_14573.nosynth);
        uvar_subtyping = (uu___499_14573.uvar_subtyping);
        tc_term = (uu___499_14573.tc_term);
        type_of = (uu___499_14573.type_of);
        universe_of = (uu___499_14573.universe_of);
        check_type_of = (uu___499_14573.check_type_of);
        use_bv_sorts = (uu___499_14573.use_bv_sorts);
        qtbl_name_and_index = (uu___499_14573.qtbl_name_and_index);
        normalized_eff_names = (uu___499_14573.normalized_eff_names);
        fv_delta_depths = (uu___499_14573.fv_delta_depths);
        proof_ns = (uu___499_14573.proof_ns);
        synth_hook = (uu___499_14573.synth_hook);
        splice = (uu___499_14573.splice);
        postprocess = (uu___499_14573.postprocess);
        is_native_tactic = (uu___499_14573.is_native_tactic);
        identifier_info = (uu___499_14573.identifier_info);
        tc_hooks = (uu___499_14573.tc_hooks);
        dsenv = (uu___499_14573.dsenv);
        nbe = (uu___499_14573.nbe);
        strict_args_tab = (uu___499_14573.strict_args_tab)
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
      let uu____14604 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14604
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14617 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14617)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14632 =
      let uu____14634 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14634  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14632)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14643  ->
    let uu____14644 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14644
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - Prims.int_one  in
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
      | ((formals,t),uu____14744) ->
          let vs = mk_univ_subst formals us  in
          let uu____14768 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14768)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_14785  ->
    match uu___1_14785 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14811  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14831 = inst_tscheme t  in
      match uu____14831 with
      | (us,t1) ->
          let uu____14842 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14842)
  
let (check_effect_is_not_a_template :
  FStar_Syntax_Syntax.eff_decl -> FStar_Range.range -> unit) =
  fun ed  ->
    fun rng  ->
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        let msg =
          let uu____14867 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____14869 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____14867 uu____14869
           in
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect, msg) rng
      else ()
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14896  ->
          match uu____14896 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____14910 =
                    let uu____14912 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____14916 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____14920 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____14922 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____14912 uu____14916 uu____14920 uu____14922
                     in
                  failwith uu____14910)
               else ();
               (let uu____14927 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____14927))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14945 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14956 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14967 -> false
  
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
             | ([],uu____15015) -> Maybe
             | (uu____15022,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15042 -> No  in
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
          let uu____15136 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15136 with
          | FStar_Pervasives_Native.None  ->
              let uu____15159 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15203  ->
                     match uu___2_15203 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15242 = FStar_Ident.lid_equals lid l  in
                         if uu____15242
                         then
                           let uu____15265 =
                             let uu____15284 =
                               let uu____15299 = inst_tscheme t  in
                               FStar_Util.Inl uu____15299  in
                             let uu____15314 = FStar_Ident.range_of_lid l  in
                             (uu____15284, uu____15314)  in
                           FStar_Pervasives_Native.Some uu____15265
                         else FStar_Pervasives_Native.None
                     | uu____15367 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15159
                (fun uu____15405  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15414  ->
                        match uu___3_15414 with
                        | (uu____15417,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15419);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15420;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15421;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15422;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15423;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15443 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15443
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
                                  uu____15495 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15502 -> cache t  in
                            let uu____15503 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15503 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15509 =
                                   let uu____15510 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15510)
                                    in
                                 maybe_cache uu____15509)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15581 = find_in_sigtab env lid  in
         match uu____15581 with
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
      let uu____15662 = lookup_qname env lid  in
      match uu____15662 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15683,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15797 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15797 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15842 =
          let uu____15845 = lookup_attr env1 attr  in se1 :: uu____15845  in
        FStar_Util.smap_add (attrtab env1) attr uu____15842  in
      FStar_List.iter
        (fun attr  ->
           let uu____15855 =
             let uu____15856 = FStar_Syntax_Subst.compress attr  in
             uu____15856.FStar_Syntax_Syntax.n  in
           match uu____15855 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15860 =
                 let uu____15862 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15862.FStar_Ident.str  in
               add_one1 env se uu____15860
           | uu____15863 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15886) ->
          add_sigelts env ses
      | uu____15895 ->
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
            | uu____15910 -> ()))

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
        (fun uu___4_15942  ->
           match uu___4_15942 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15960 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16022,lb::[]),uu____16024) ->
            let uu____16033 =
              let uu____16042 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16051 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16042, uu____16051)  in
            FStar_Pervasives_Native.Some uu____16033
        | FStar_Syntax_Syntax.Sig_let ((uu____16064,lbs),uu____16066) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16098 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16111 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16111
                     then
                       let uu____16124 =
                         let uu____16133 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16142 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16133, uu____16142)  in
                       FStar_Pervasives_Native.Some uu____16124
                     else FStar_Pervasives_Native.None)
        | uu____16165 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Range.range ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
          FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun rng  ->
        let inst_ts us_opt1 ts =
          match us_opt1 with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_new_effect ne ->
            (check_effect_is_not_a_template ne rng;
             (match us_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some us ->
                  if
                    (FStar_List.length us) <>
                      (FStar_List.length
                         (FStar_Pervasives_Native.fst
                            ne.FStar_Syntax_Syntax.signature))
                  then
                    let uu____16257 =
                      let uu____16259 =
                        let uu____16261 =
                          let uu____16263 =
                            let uu____16265 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16271 =
                              let uu____16273 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16273  in
                            Prims.op_Hat uu____16265 uu____16271  in
                          Prims.op_Hat ", expected " uu____16263  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16261
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16259
                       in
                    failwith uu____16257
                  else ());
             (let uu____16280 =
                let uu____16289 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16289, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16280))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16309,uu____16310) ->
            let uu____16315 =
              let uu____16324 =
                let uu____16329 =
                  let uu____16330 =
                    let uu____16333 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16333  in
                  (us, uu____16330)  in
                inst_ts us_opt uu____16329  in
              (uu____16324, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16315
        | uu____16352 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16441 =
          match uu____16441 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16537,uvs,t,uu____16540,uu____16541,uu____16542);
                      FStar_Syntax_Syntax.sigrng = uu____16543;
                      FStar_Syntax_Syntax.sigquals = uu____16544;
                      FStar_Syntax_Syntax.sigmeta = uu____16545;
                      FStar_Syntax_Syntax.sigattrs = uu____16546;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16569 =
                     let uu____16578 = inst_tscheme1 (uvs, t)  in
                     (uu____16578, rng)  in
                   FStar_Pervasives_Native.Some uu____16569
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16602;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16604;
                      FStar_Syntax_Syntax.sigattrs = uu____16605;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16622 =
                     let uu____16624 = in_cur_mod env l  in uu____16624 = Yes
                      in
                   if uu____16622
                   then
                     let uu____16636 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16636
                      then
                        let uu____16652 =
                          let uu____16661 = inst_tscheme1 (uvs, t)  in
                          (uu____16661, rng)  in
                        FStar_Pervasives_Native.Some uu____16652
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16694 =
                        let uu____16703 = inst_tscheme1 (uvs, t)  in
                        (uu____16703, rng)  in
                      FStar_Pervasives_Native.Some uu____16694)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16728,uu____16729);
                      FStar_Syntax_Syntax.sigrng = uu____16730;
                      FStar_Syntax_Syntax.sigquals = uu____16731;
                      FStar_Syntax_Syntax.sigmeta = uu____16732;
                      FStar_Syntax_Syntax.sigattrs = uu____16733;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16774 =
                          let uu____16783 = inst_tscheme1 (uvs, k)  in
                          (uu____16783, rng)  in
                        FStar_Pervasives_Native.Some uu____16774
                    | uu____16804 ->
                        let uu____16805 =
                          let uu____16814 =
                            let uu____16819 =
                              let uu____16820 =
                                let uu____16823 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16823
                                 in
                              (uvs, uu____16820)  in
                            inst_tscheme1 uu____16819  in
                          (uu____16814, rng)  in
                        FStar_Pervasives_Native.Some uu____16805)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16846,uu____16847);
                      FStar_Syntax_Syntax.sigrng = uu____16848;
                      FStar_Syntax_Syntax.sigquals = uu____16849;
                      FStar_Syntax_Syntax.sigmeta = uu____16850;
                      FStar_Syntax_Syntax.sigattrs = uu____16851;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16893 =
                          let uu____16902 = inst_tscheme_with (uvs, k) us  in
                          (uu____16902, rng)  in
                        FStar_Pervasives_Native.Some uu____16893
                    | uu____16923 ->
                        let uu____16924 =
                          let uu____16933 =
                            let uu____16938 =
                              let uu____16939 =
                                let uu____16942 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16942
                                 in
                              (uvs, uu____16939)  in
                            inst_tscheme_with uu____16938 us  in
                          (uu____16933, rng)  in
                        FStar_Pervasives_Native.Some uu____16924)
               | FStar_Util.Inr se ->
                   let uu____16978 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16999;
                          FStar_Syntax_Syntax.sigrng = uu____17000;
                          FStar_Syntax_Syntax.sigquals = uu____17001;
                          FStar_Syntax_Syntax.sigmeta = uu____17002;
                          FStar_Syntax_Syntax.sigattrs = uu____17003;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17018 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____16978
                     (FStar_Util.map_option
                        (fun uu____17066  ->
                           match uu____17066 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17097 =
          let uu____17108 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17108 mapper  in
        match uu____17097 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17182 =
              let uu____17193 =
                let uu____17200 =
                  let uu___836_17203 = t  in
                  let uu____17204 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___836_17203.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17204;
                    FStar_Syntax_Syntax.vars =
                      (uu___836_17203.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17200)  in
              (uu____17193, r)  in
            FStar_Pervasives_Native.Some uu____17182
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17253 = lookup_qname env l  in
      match uu____17253 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17274 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17328 = try_lookup_bv env bv  in
      match uu____17328 with
      | FStar_Pervasives_Native.None  ->
          let uu____17343 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17343 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17359 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17360 =
            let uu____17361 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17361  in
          (uu____17359, uu____17360)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17383 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17383 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17449 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17449  in
          let uu____17450 =
            let uu____17459 =
              let uu____17464 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17464)  in
            (uu____17459, r1)  in
          FStar_Pervasives_Native.Some uu____17450
  
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
        let uu____17499 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17499 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17532,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17557 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17557  in
            let uu____17558 =
              let uu____17563 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17563, r1)  in
            FStar_Pervasives_Native.Some uu____17558
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17587 = try_lookup_lid env l  in
      match uu____17587 with
      | FStar_Pervasives_Native.None  ->
          let uu____17614 = name_not_found l  in
          let uu____17620 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17614 uu____17620
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17663  ->
              match uu___5_17663 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17667 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17688 = lookup_qname env lid  in
      match uu____17688 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17697,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17700;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17702;
              FStar_Syntax_Syntax.sigattrs = uu____17703;_},FStar_Pervasives_Native.None
            ),uu____17704)
          ->
          let uu____17753 =
            let uu____17760 =
              let uu____17761 =
                let uu____17764 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17764 t  in
              (uvs, uu____17761)  in
            (uu____17760, q)  in
          FStar_Pervasives_Native.Some uu____17753
      | uu____17777 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17799 = lookup_qname env lid  in
      match uu____17799 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17804,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17807;
              FStar_Syntax_Syntax.sigquals = uu____17808;
              FStar_Syntax_Syntax.sigmeta = uu____17809;
              FStar_Syntax_Syntax.sigattrs = uu____17810;_},FStar_Pervasives_Native.None
            ),uu____17811)
          ->
          let uu____17860 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17860 (uvs, t)
      | uu____17865 ->
          let uu____17866 = name_not_found lid  in
          let uu____17872 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17866 uu____17872
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17892 = lookup_qname env lid  in
      match uu____17892 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17897,uvs,t,uu____17900,uu____17901,uu____17902);
              FStar_Syntax_Syntax.sigrng = uu____17903;
              FStar_Syntax_Syntax.sigquals = uu____17904;
              FStar_Syntax_Syntax.sigmeta = uu____17905;
              FStar_Syntax_Syntax.sigattrs = uu____17906;_},FStar_Pervasives_Native.None
            ),uu____17907)
          ->
          let uu____17962 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17962 (uvs, t)
      | uu____17967 ->
          let uu____17968 = name_not_found lid  in
          let uu____17974 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17968 uu____17974
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17997 = lookup_qname env lid  in
      match uu____17997 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18005,uu____18006,uu____18007,uu____18008,uu____18009,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18011;
              FStar_Syntax_Syntax.sigquals = uu____18012;
              FStar_Syntax_Syntax.sigmeta = uu____18013;
              FStar_Syntax_Syntax.sigattrs = uu____18014;_},uu____18015),uu____18016)
          -> (true, dcs)
      | uu____18079 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18095 = lookup_qname env lid  in
      match uu____18095 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18096,uu____18097,uu____18098,l,uu____18100,uu____18101);
              FStar_Syntax_Syntax.sigrng = uu____18102;
              FStar_Syntax_Syntax.sigquals = uu____18103;
              FStar_Syntax_Syntax.sigmeta = uu____18104;
              FStar_Syntax_Syntax.sigattrs = uu____18105;_},uu____18106),uu____18107)
          -> l
      | uu____18164 ->
          let uu____18165 =
            let uu____18167 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18167  in
          failwith uu____18165
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18237)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18294) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18318 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18318
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18353 -> FStar_Pervasives_Native.None)
          | uu____18362 -> FStar_Pervasives_Native.None
  
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
        let uu____18424 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18424
  
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
        let uu____18457 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18457
  
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
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____18509,uu____18510) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18559),uu____18560) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18609 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18627 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18637 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18654 ->
                  let uu____18661 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18661
              | FStar_Syntax_Syntax.Sig_let ((uu____18662,lbs),uu____18664)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18680 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18680
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18687 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18695 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18696 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18703 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18704 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18705 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18706 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18719 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18737 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18737
           (fun d_opt  ->
              let uu____18750 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18750
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18760 =
                   let uu____18763 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18763  in
                 match uu____18760 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18764 =
                       let uu____18766 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18766
                        in
                     failwith uu____18764
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18771 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18771
                       then
                         let uu____18774 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18776 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18778 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18774 uu____18776 uu____18778
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
        (FStar_Util.Inr (se,uu____18803),uu____18804) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18853 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18875),uu____18876) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18925 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18947 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18947
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____18970 = lookup_attrs_of_lid env fv_lid1  in
        match uu____18970 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18994 =
                      let uu____18995 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18995.FStar_Syntax_Syntax.n  in
                    match uu____18994 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19000 -> false))
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let s =
        let uu____19037 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19037.FStar_Ident.str  in
      let uu____19038 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19038 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19066 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19066  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____19094 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____19094)
                  in
               (FStar_Util.smap_add env.strict_args_tab s res; res))
      | FStar_Pervasives_Native.Some l -> l
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____19144 = lookup_qname env ftv  in
      match uu____19144 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19148) ->
          let uu____19193 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19193 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19214,t),r) ->
               let uu____19229 =
                 let uu____19230 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19230 t  in
               FStar_Pervasives_Native.Some uu____19229)
      | uu____19231 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19243 = try_lookup_effect_lid env ftv  in
      match uu____19243 with
      | FStar_Pervasives_Native.None  ->
          let uu____19246 = name_not_found ftv  in
          let uu____19252 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19246 uu____19252
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
        let uu____19276 = lookup_qname env lid0  in
        match uu____19276 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19287);
                FStar_Syntax_Syntax.sigrng = uu____19288;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19290;
                FStar_Syntax_Syntax.sigattrs = uu____19291;_},FStar_Pervasives_Native.None
              ),uu____19292)
            ->
            let lid1 =
              let uu____19346 =
                let uu____19347 = FStar_Ident.range_of_lid lid  in
                let uu____19348 =
                  let uu____19349 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19349  in
                FStar_Range.set_use_range uu____19347 uu____19348  in
              FStar_Ident.set_lid_range lid uu____19346  in
            let uu____19350 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19356  ->
                      match uu___6_19356 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19359 -> false))
               in
            if uu____19350
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19378 =
                      let uu____19380 =
                        let uu____19382 = get_range env  in
                        FStar_Range.string_of_range uu____19382  in
                      let uu____19383 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19385 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19380 uu____19383 uu____19385
                       in
                    failwith uu____19378)
                  in
               match (binders, univs1) with
               | ([],uu____19406) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19432,uu____19433::uu____19434::uu____19435) ->
                   let uu____19456 =
                     let uu____19458 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19460 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19458 uu____19460
                      in
                   failwith uu____19456
               | uu____19471 ->
                   let uu____19486 =
                     let uu____19491 =
                       let uu____19492 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19492)  in
                     inst_tscheme_with uu____19491 insts  in
                   (match uu____19486 with
                    | (uu____19505,t) ->
                        let t1 =
                          let uu____19508 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19508 t  in
                        let uu____19509 =
                          let uu____19510 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19510.FStar_Syntax_Syntax.n  in
                        (match uu____19509 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19545 -> failwith "Impossible")))
        | uu____19553 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19577 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19577 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19590,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19597 = find1 l2  in
            (match uu____19597 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19604 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19604 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19608 = find1 l  in
            (match uu____19608 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19613 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19613
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19628 = lookup_qname env l1  in
      match uu____19628 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19631;
              FStar_Syntax_Syntax.sigrng = uu____19632;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19634;
              FStar_Syntax_Syntax.sigattrs = uu____19635;_},uu____19636),uu____19637)
          -> q
      | uu____19688 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19712 =
          let uu____19713 =
            let uu____19715 = FStar_Util.string_of_int i  in
            let uu____19717 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19715 uu____19717
             in
          failwith uu____19713  in
        let uu____19720 = lookup_datacon env lid  in
        match uu____19720 with
        | (uu____19725,t) ->
            let uu____19727 =
              let uu____19728 = FStar_Syntax_Subst.compress t  in
              uu____19728.FStar_Syntax_Syntax.n  in
            (match uu____19727 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19732) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19776 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19776
                      FStar_Pervasives_Native.fst)
             | uu____19787 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19801 = lookup_qname env l  in
      match uu____19801 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19803,uu____19804,uu____19805);
              FStar_Syntax_Syntax.sigrng = uu____19806;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19808;
              FStar_Syntax_Syntax.sigattrs = uu____19809;_},uu____19810),uu____19811)
          ->
          FStar_Util.for_some
            (fun uu___7_19864  ->
               match uu___7_19864 with
               | FStar_Syntax_Syntax.Projector uu____19866 -> true
               | uu____19872 -> false) quals
      | uu____19874 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19888 = lookup_qname env lid  in
      match uu____19888 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19890,uu____19891,uu____19892,uu____19893,uu____19894,uu____19895);
              FStar_Syntax_Syntax.sigrng = uu____19896;
              FStar_Syntax_Syntax.sigquals = uu____19897;
              FStar_Syntax_Syntax.sigmeta = uu____19898;
              FStar_Syntax_Syntax.sigattrs = uu____19899;_},uu____19900),uu____19901)
          -> true
      | uu____19959 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19973 = lookup_qname env lid  in
      match uu____19973 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19975,uu____19976,uu____19977,uu____19978,uu____19979,uu____19980);
              FStar_Syntax_Syntax.sigrng = uu____19981;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19983;
              FStar_Syntax_Syntax.sigattrs = uu____19984;_},uu____19985),uu____19986)
          ->
          FStar_Util.for_some
            (fun uu___8_20047  ->
               match uu___8_20047 with
               | FStar_Syntax_Syntax.RecordType uu____20049 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20059 -> true
               | uu____20069 -> false) quals
      | uu____20071 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20081,uu____20082);
            FStar_Syntax_Syntax.sigrng = uu____20083;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20085;
            FStar_Syntax_Syntax.sigattrs = uu____20086;_},uu____20087),uu____20088)
        ->
        FStar_Util.for_some
          (fun uu___9_20145  ->
             match uu___9_20145 with
             | FStar_Syntax_Syntax.Action uu____20147 -> true
             | uu____20149 -> false) quals
    | uu____20151 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20165 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20165
  
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
      let uu____20182 =
        let uu____20183 = FStar_Syntax_Util.un_uinst head1  in
        uu____20183.FStar_Syntax_Syntax.n  in
      match uu____20182 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20189 ->
               true
           | uu____20192 -> false)
      | uu____20194 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20208 = lookup_qname env l  in
      match uu____20208 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20211),uu____20212) ->
          FStar_Util.for_some
            (fun uu___10_20260  ->
               match uu___10_20260 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20263 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20265 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20341 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20359) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20377 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20385 ->
                 FStar_Pervasives_Native.Some true
             | uu____20404 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20407 =
        let uu____20411 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20411 mapper  in
      match uu____20407 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20471 = lookup_qname env lid  in
      match uu____20471 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20475,uu____20476,tps,uu____20478,uu____20479,uu____20480);
              FStar_Syntax_Syntax.sigrng = uu____20481;
              FStar_Syntax_Syntax.sigquals = uu____20482;
              FStar_Syntax_Syntax.sigmeta = uu____20483;
              FStar_Syntax_Syntax.sigattrs = uu____20484;_},uu____20485),uu____20486)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20552 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20598  ->
              match uu____20598 with
              | (d,uu____20607) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20623 = effect_decl_opt env l  in
      match uu____20623 with
      | FStar_Pervasives_Native.None  ->
          let uu____20638 = name_not_found l  in
          let uu____20644 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20638 uu____20644
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20672 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____20672
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_t = FStar_Pervasives_Native.None;
    mlift_wp = (fun uu____20680  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20699  ->
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
        let uu____20731 = FStar_Ident.lid_equals l1 l2  in
        if uu____20731
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20742 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20742
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20753 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20806  ->
                        match uu____20806 with
                        | (m1,m2,uu____20820,uu____20821,uu____20822) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20753 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20839 =
                    let uu____20845 =
                      let uu____20847 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20849 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20847
                        uu____20849
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20845)
                     in
                  FStar_Errors.raise_error uu____20839 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20859,uu____20860,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20894 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20894
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
  'Auu____20914 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20914) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20943 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20969  ->
                match uu____20969 with
                | (d,uu____20976) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20943 with
      | FStar_Pervasives_Native.None  ->
          let uu____20987 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20987
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21002 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21002 with
           | (uu____21013,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21031)::(wp,uu____21033)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21089 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1496_21139 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1496_21139.order);
              joins = (uu___1496_21139.joins)
            }  in
          let uu___1499_21148 = env  in
          {
            solver = (uu___1499_21148.solver);
            range = (uu___1499_21148.range);
            curmodule = (uu___1499_21148.curmodule);
            gamma = (uu___1499_21148.gamma);
            gamma_sig = (uu___1499_21148.gamma_sig);
            gamma_cache = (uu___1499_21148.gamma_cache);
            modules = (uu___1499_21148.modules);
            expected_typ = (uu___1499_21148.expected_typ);
            sigtab = (uu___1499_21148.sigtab);
            attrtab = (uu___1499_21148.attrtab);
            is_pattern = (uu___1499_21148.is_pattern);
            instantiate_imp = (uu___1499_21148.instantiate_imp);
            effects;
            generalize = (uu___1499_21148.generalize);
            letrecs = (uu___1499_21148.letrecs);
            top_level = (uu___1499_21148.top_level);
            check_uvars = (uu___1499_21148.check_uvars);
            use_eq = (uu___1499_21148.use_eq);
            is_iface = (uu___1499_21148.is_iface);
            admit = (uu___1499_21148.admit);
            lax = (uu___1499_21148.lax);
            lax_universes = (uu___1499_21148.lax_universes);
            phase1 = (uu___1499_21148.phase1);
            failhard = (uu___1499_21148.failhard);
            nosynth = (uu___1499_21148.nosynth);
            uvar_subtyping = (uu___1499_21148.uvar_subtyping);
            tc_term = (uu___1499_21148.tc_term);
            type_of = (uu___1499_21148.type_of);
            universe_of = (uu___1499_21148.universe_of);
            check_type_of = (uu___1499_21148.check_type_of);
            use_bv_sorts = (uu___1499_21148.use_bv_sorts);
            qtbl_name_and_index = (uu___1499_21148.qtbl_name_and_index);
            normalized_eff_names = (uu___1499_21148.normalized_eff_names);
            fv_delta_depths = (uu___1499_21148.fv_delta_depths);
            proof_ns = (uu___1499_21148.proof_ns);
            synth_hook = (uu___1499_21148.synth_hook);
            splice = (uu___1499_21148.splice);
            postprocess = (uu___1499_21148.postprocess);
            is_native_tactic = (uu___1499_21148.is_native_tactic);
            identifier_info = (uu___1499_21148.identifier_info);
            tc_hooks = (uu___1499_21148.tc_hooks);
            dsenv = (uu___1499_21148.dsenv);
            nbe = (uu___1499_21148.nbe);
            strict_args_tab = (uu___1499_21148.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let src_ed = get_effect_decl env sub1.FStar_Syntax_Syntax.source
             in
          let dst_ed = get_effect_decl env sub1.FStar_Syntax_Syntax.target
             in
          if
            src_ed.FStar_Syntax_Syntax.is_layered ||
              dst_ed.FStar_Syntax_Syntax.is_layered
          then
            let edge =
              {
                msource = (sub1.FStar_Syntax_Syntax.source);
                mtarget = (sub1.FStar_Syntax_Syntax.target);
                mlift =
                  {
                    mlift_t = (sub1.FStar_Syntax_Syntax.lift_wp);
                    mlift_wp =
                      (fun uu____21157  ->
                         fun uu____21158  ->
                           fun uu____21159  -> FStar_Syntax_Syntax.tun);
                    mlift_term = FStar_Pervasives_Native.None
                  }
              }  in
            let dummy_mlift =
              {
                mlift_t = FStar_Pervasives_Native.None;
                mlift_wp =
                  (fun uu____21176  ->
                     fun uu____21177  ->
                       fun uu____21178  -> FStar_Syntax_Syntax.tun);
                mlift_term = FStar_Pervasives_Native.None
              }  in
            let n_join1 =
              ((src_ed.FStar_Syntax_Syntax.mname),
                (dst_ed.FStar_Syntax_Syntax.mname),
                (dst_ed.FStar_Syntax_Syntax.mname), dummy_mlift, dummy_mlift)
               in
            let n_join2 =
              ((dst_ed.FStar_Syntax_Syntax.mname),
                (src_ed.FStar_Syntax_Syntax.mname),
                (dst_ed.FStar_Syntax_Syntax.mname), dummy_mlift, dummy_mlift)
               in
            let uu___1516_21213 = env  in
            {
              solver = (uu___1516_21213.solver);
              range = (uu___1516_21213.range);
              curmodule = (uu___1516_21213.curmodule);
              gamma = (uu___1516_21213.gamma);
              gamma_sig = (uu___1516_21213.gamma_sig);
              gamma_cache = (uu___1516_21213.gamma_cache);
              modules = (uu___1516_21213.modules);
              expected_typ = (uu___1516_21213.expected_typ);
              sigtab = (uu___1516_21213.sigtab);
              attrtab = (uu___1516_21213.attrtab);
              is_pattern = (uu___1516_21213.is_pattern);
              instantiate_imp = (uu___1516_21213.instantiate_imp);
              effects =
                (let uu___1518_21215 = env.effects  in
                 {
                   decls = (uu___1518_21215.decls);
                   order = (edge :: ((env.effects).order));
                   joins = (n_join1 :: n_join2 :: ((env.effects).joins))
                 });
              generalize = (uu___1516_21213.generalize);
              letrecs = (uu___1516_21213.letrecs);
              top_level = (uu___1516_21213.top_level);
              check_uvars = (uu___1516_21213.check_uvars);
              use_eq = (uu___1516_21213.use_eq);
              is_iface = (uu___1516_21213.is_iface);
              admit = (uu___1516_21213.admit);
              lax = (uu___1516_21213.lax);
              lax_universes = (uu___1516_21213.lax_universes);
              phase1 = (uu___1516_21213.phase1);
              failhard = (uu___1516_21213.failhard);
              nosynth = (uu___1516_21213.nosynth);
              uvar_subtyping = (uu___1516_21213.uvar_subtyping);
              tc_term = (uu___1516_21213.tc_term);
              type_of = (uu___1516_21213.type_of);
              universe_of = (uu___1516_21213.universe_of);
              check_type_of = (uu___1516_21213.check_type_of);
              use_bv_sorts = (uu___1516_21213.use_bv_sorts);
              qtbl_name_and_index = (uu___1516_21213.qtbl_name_and_index);
              normalized_eff_names = (uu___1516_21213.normalized_eff_names);
              fv_delta_depths = (uu___1516_21213.fv_delta_depths);
              proof_ns = (uu___1516_21213.proof_ns);
              synth_hook = (uu___1516_21213.synth_hook);
              splice = (uu___1516_21213.splice);
              postprocess = (uu___1516_21213.postprocess);
              is_native_tactic = (uu___1516_21213.is_native_tactic);
              identifier_info = (uu___1516_21213.identifier_info);
              tc_hooks = (uu___1516_21213.tc_hooks);
              dsenv = (uu___1516_21213.dsenv);
              nbe = (uu___1516_21213.nbe);
              strict_args_tab = (uu___1516_21213.strict_args_tab)
            }
          else
            (let compose_edges e1 e2 =
               let composed_lift =
                 let mlift_wp u r wp1 =
                   let uu____21266 = (e1.mlift).mlift_wp u r wp1  in
                   (e2.mlift).mlift_wp u r uu____21266  in
                 let mlift_term =
                   match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term))
                   with
                   | (FStar_Pervasives_Native.Some
                      l1,FStar_Pervasives_Native.Some l2) ->
                       FStar_Pervasives_Native.Some
                         ((fun u  ->
                             fun t  ->
                               fun wp  ->
                                 fun e  ->
                                   let uu____21424 =
                                     (e1.mlift).mlift_wp u t wp  in
                                   let uu____21425 = l1 u t wp e  in
                                   l2 u t uu____21424 uu____21425))
                   | uu____21426 -> FStar_Pervasives_Native.None  in
                 {
                   mlift_t = FStar_Pervasives_Native.None;
                   mlift_wp;
                   mlift_term
                 }  in
               {
                 msource = (e1.msource);
                 mtarget = (e2.mtarget);
                 mlift = composed_lift
               }  in
             let mk_mlift_wp lift_t u r wp1 =
               let uu____21498 = inst_tscheme_with lift_t [u]  in
               match uu____21498 with
               | (uu____21505,lift_t1) ->
                   let uu____21507 =
                     let uu____21514 =
                       let uu____21515 =
                         let uu____21532 =
                           let uu____21543 = FStar_Syntax_Syntax.as_arg r  in
                           let uu____21552 =
                             let uu____21563 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____21563]  in
                           uu____21543 :: uu____21552  in
                         (lift_t1, uu____21532)  in
                       FStar_Syntax_Syntax.Tm_app uu____21515  in
                     FStar_Syntax_Syntax.mk uu____21514  in
                   uu____21507 FStar_Pervasives_Native.None
                     wp1.FStar_Syntax_Syntax.pos
                in
             let sub_mlift_wp =
               match sub1.FStar_Syntax_Syntax.lift_wp with
               | FStar_Pervasives_Native.Some sub_lift_wp ->
                   mk_mlift_wp sub_lift_wp
               | FStar_Pervasives_Native.None  ->
                   failwith
                     "sub effect should've been elaborated at this stage"
                in
             let mk_mlift_term lift_t u r wp1 e =
               let uu____21673 = inst_tscheme_with lift_t [u]  in
               match uu____21673 with
               | (uu____21680,lift_t1) ->
                   let uu____21682 =
                     let uu____21689 =
                       let uu____21690 =
                         let uu____21707 =
                           let uu____21718 = FStar_Syntax_Syntax.as_arg r  in
                           let uu____21727 =
                             let uu____21738 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             let uu____21747 =
                               let uu____21758 = FStar_Syntax_Syntax.as_arg e
                                  in
                               [uu____21758]  in
                             uu____21738 :: uu____21747  in
                           uu____21718 :: uu____21727  in
                         (lift_t1, uu____21707)  in
                       FStar_Syntax_Syntax.Tm_app uu____21690  in
                     FStar_Syntax_Syntax.mk uu____21689  in
                   uu____21682 FStar_Pervasives_Native.None
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
                   {
                     mlift_t = FStar_Pervasives_Native.None;
                     mlift_wp = sub_mlift_wp;
                     mlift_term = sub_mlift_term
                   }
               }  in
             let id_edge l =
               {
                 msource = (sub1.FStar_Syntax_Syntax.source);
                 mtarget = (sub1.FStar_Syntax_Syntax.target);
                 mlift = identity_mlift
               }  in
             let print_mlift l =
               let bogus_term s =
                 let uu____21860 =
                   let uu____21861 =
                     FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                   FStar_Syntax_Syntax.lid_as_fv uu____21861
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____21860  in
               let arg = bogus_term "ARG"  in
               let wp = bogus_term "WP"  in
               let e = bogus_term "COMP"  in
               let uu____21870 =
                 let uu____21872 =
                   l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
                 FStar_Syntax_Print.term_to_string uu____21872  in
               let uu____21873 =
                 let uu____21875 =
                   FStar_Util.map_opt l.mlift_term
                     (fun l1  ->
                        let uu____21903 =
                          l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                        FStar_Syntax_Print.term_to_string uu____21903)
                    in
                 FStar_Util.dflt "none" uu____21875  in
               FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21870
                 uu____21873
                in
             let order = edge :: ((env.effects).order)  in
             let ms =
               FStar_All.pipe_right (env.effects).decls
                 (FStar_List.map
                    (fun uu____21932  ->
                       match uu____21932 with
                       | (e,uu____21940) -> e.FStar_Syntax_Syntax.mname))
                in
             let find_edge order1 uu____21963 =
               match uu____21963 with
               | (i,j) ->
                   let uu____21974 = FStar_Ident.lid_equals i j  in
                   if uu____21974
                   then
                     FStar_All.pipe_right (id_edge i)
                       (fun _21981  -> FStar_Pervasives_Native.Some _21981)
                   else
                     FStar_All.pipe_right order1
                       (FStar_Util.find_opt
                          (fun e  ->
                             (FStar_Ident.lid_equals e.msource i) &&
                               (FStar_Ident.lid_equals e.mtarget j)))
                in
             let order1 =
               let fold_fun order1 k =
                 let uu____22010 =
                   FStar_All.pipe_right ms
                     (FStar_List.collect
                        (fun i  ->
                           let uu____22020 = FStar_Ident.lid_equals i k  in
                           if uu____22020
                           then []
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.collect
                                  (fun j  ->
                                     let uu____22034 =
                                       FStar_Ident.lid_equals j k  in
                                     if uu____22034
                                     then []
                                     else
                                       (let uu____22041 =
                                          let uu____22050 =
                                            find_edge order1 (i, k)  in
                                          let uu____22053 =
                                            find_edge order1 (k, j)  in
                                          (uu____22050, uu____22053)  in
                                        match uu____22041 with
                                        | (FStar_Pervasives_Native.Some
                                           e1,FStar_Pervasives_Native.Some
                                           e2) ->
                                            let uu____22068 =
                                              compose_edges e1 e2  in
                                            [uu____22068]
                                        | uu____22069 -> [])))))
                    in
                 FStar_List.append order1 uu____22010  in
               FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)
                in
             let order2 =
               FStar_Util.remove_dups
                 (fun e1  ->
                    fun e2  ->
                      (FStar_Ident.lid_equals e1.msource e2.msource) &&
                        (FStar_Ident.lid_equals e1.mtarget e2.mtarget))
                 order1
                in
             FStar_All.pipe_right order2
               (FStar_List.iter
                  (fun edge1  ->
                     let uu____22099 =
                       (FStar_Ident.lid_equals edge1.msource
                          FStar_Parser_Const.effect_DIV_lid)
                         &&
                         (let uu____22102 =
                            lookup_effect_quals env edge1.mtarget  in
                          FStar_All.pipe_right uu____22102
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect))
                        in
                     if uu____22099
                     then
                       let uu____22109 =
                         let uu____22115 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                           uu____22115)
                          in
                       let uu____22119 = get_range env  in
                       FStar_Errors.raise_error uu____22109 uu____22119
                     else ()));
             (let joins =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        FStar_All.pipe_right ms
                          (FStar_List.collect
                             (fun j  ->
                                let join_opt =
                                  let uu____22197 =
                                    FStar_Ident.lid_equals i j  in
                                  if uu____22197
                                  then
                                    FStar_Pervasives_Native.Some
                                      (i, (id_edge i), (id_edge i))
                                  else
                                    FStar_All.pipe_right ms
                                      (FStar_List.fold_left
                                         (fun bopt  ->
                                            fun k  ->
                                              let uu____22249 =
                                                let uu____22258 =
                                                  find_edge order2 (i, k)  in
                                                let uu____22261 =
                                                  find_edge order2 (j, k)  in
                                                (uu____22258, uu____22261)
                                                 in
                                              match uu____22249 with
                                              | (FStar_Pervasives_Native.Some
                                                 ik,FStar_Pervasives_Native.Some
                                                 jk) ->
                                                  (match bopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.Some
                                                         (k, ik, jk)
                                                   | FStar_Pervasives_Native.Some
                                                       (ub,uu____22303,uu____22304)
                                                       ->
                                                       let uu____22311 =
                                                         let uu____22318 =
                                                           let uu____22320 =
                                                             find_edge order2
                                                               (k, ub)
                                                              in
                                                           FStar_Util.is_some
                                                             uu____22320
                                                            in
                                                         let uu____22323 =
                                                           let uu____22325 =
                                                             find_edge order2
                                                               (ub, k)
                                                              in
                                                           FStar_Util.is_some
                                                             uu____22325
                                                            in
                                                         (uu____22318,
                                                           uu____22323)
                                                          in
                                                       (match uu____22311
                                                        with
                                                        | (true ,true ) ->
                                                            let uu____22342 =
                                                              FStar_Ident.lid_equals
                                                                k ub
                                                               in
                                                            if uu____22342
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
                                              | uu____22385 -> bopt)
                                         FStar_Pervasives_Native.None)
                                   in
                                match join_opt with
                                | FStar_Pervasives_Native.None  -> []
                                | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                    [(i, j, k, (e1.mlift), (e2.mlift))]))))
                 in
              let effects =
                let uu___1643_22458 = env.effects  in
                { decls = (uu___1643_22458.decls); order = order2; joins }
                 in
              let uu___1646_22459 = env  in
              {
                solver = (uu___1646_22459.solver);
                range = (uu___1646_22459.range);
                curmodule = (uu___1646_22459.curmodule);
                gamma = (uu___1646_22459.gamma);
                gamma_sig = (uu___1646_22459.gamma_sig);
                gamma_cache = (uu___1646_22459.gamma_cache);
                modules = (uu___1646_22459.modules);
                expected_typ = (uu___1646_22459.expected_typ);
                sigtab = (uu___1646_22459.sigtab);
                attrtab = (uu___1646_22459.attrtab);
                is_pattern = (uu___1646_22459.is_pattern);
                instantiate_imp = (uu___1646_22459.instantiate_imp);
                effects;
                generalize = (uu___1646_22459.generalize);
                letrecs = (uu___1646_22459.letrecs);
                top_level = (uu___1646_22459.top_level);
                check_uvars = (uu___1646_22459.check_uvars);
                use_eq = (uu___1646_22459.use_eq);
                is_iface = (uu___1646_22459.is_iface);
                admit = (uu___1646_22459.admit);
                lax = (uu___1646_22459.lax);
                lax_universes = (uu___1646_22459.lax_universes);
                phase1 = (uu___1646_22459.phase1);
                failhard = (uu___1646_22459.failhard);
                nosynth = (uu___1646_22459.nosynth);
                uvar_subtyping = (uu___1646_22459.uvar_subtyping);
                tc_term = (uu___1646_22459.tc_term);
                type_of = (uu___1646_22459.type_of);
                universe_of = (uu___1646_22459.universe_of);
                check_type_of = (uu___1646_22459.check_type_of);
                use_bv_sorts = (uu___1646_22459.use_bv_sorts);
                qtbl_name_and_index = (uu___1646_22459.qtbl_name_and_index);
                normalized_eff_names = (uu___1646_22459.normalized_eff_names);
                fv_delta_depths = (uu___1646_22459.fv_delta_depths);
                proof_ns = (uu___1646_22459.proof_ns);
                synth_hook = (uu___1646_22459.synth_hook);
                splice = (uu___1646_22459.splice);
                postprocess = (uu___1646_22459.postprocess);
                is_native_tactic = (uu___1646_22459.is_native_tactic);
                identifier_info = (uu___1646_22459.identifier_info);
                tc_hooks = (uu___1646_22459.tc_hooks);
                dsenv = (uu___1646_22459.dsenv);
                nbe = (uu___1646_22459.nbe);
                strict_args_tab = (uu___1646_22459.strict_args_tab)
              }))
      | uu____22460 -> env
  
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
        | uu____22489 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22502 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22502 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22519 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22519 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22544 =
                     let uu____22550 =
                       let uu____22552 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22560 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22571 =
                         let uu____22573 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22573  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22552 uu____22560 uu____22571
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22550)
                      in
                   FStar_Errors.raise_error uu____22544
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22581 =
                     let uu____22592 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22592 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22629  ->
                        fun uu____22630  ->
                          match (uu____22629, uu____22630) with
                          | ((x,uu____22660),(t,uu____22662)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22581
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22693 =
                     let uu___1684_22694 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1684_22694.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1684_22694.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1684_22694.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1684_22694.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22693
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22706 .
    'Auu____22706 ->
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
          let uu____22736 = effect_decl_opt env effect_name  in
          match uu____22736 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22779 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22802 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22841 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22841
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22846 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22846
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____22857 =
                     let uu____22860 = get_range env  in
                     let uu____22861 =
                       let uu____22868 =
                         let uu____22869 =
                           let uu____22886 =
                             let uu____22897 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22897; wp]  in
                           (repr, uu____22886)  in
                         FStar_Syntax_Syntax.Tm_app uu____22869  in
                       FStar_Syntax_Syntax.mk uu____22868  in
                     uu____22861 FStar_Pervasives_Native.None uu____22860  in
                   FStar_Pervasives_Native.Some uu____22857)
  
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
      | uu____23041 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23056 =
        let uu____23057 = FStar_Syntax_Subst.compress t  in
        uu____23057.FStar_Syntax_Syntax.n  in
      match uu____23056 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23061,c) ->
          is_reifiable_comp env c
      | uu____23083 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23103 =
           let uu____23105 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23105  in
         if uu____23103
         then
           let uu____23108 =
             let uu____23114 =
               let uu____23116 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23116
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23114)  in
           let uu____23120 = get_range env  in
           FStar_Errors.raise_error uu____23108 uu____23120
         else ());
        (let uu____23123 = effect_repr_aux true env c u_c  in
         match uu____23123 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1749_23159 = env  in
        {
          solver = (uu___1749_23159.solver);
          range = (uu___1749_23159.range);
          curmodule = (uu___1749_23159.curmodule);
          gamma = (uu___1749_23159.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1749_23159.gamma_cache);
          modules = (uu___1749_23159.modules);
          expected_typ = (uu___1749_23159.expected_typ);
          sigtab = (uu___1749_23159.sigtab);
          attrtab = (uu___1749_23159.attrtab);
          is_pattern = (uu___1749_23159.is_pattern);
          instantiate_imp = (uu___1749_23159.instantiate_imp);
          effects = (uu___1749_23159.effects);
          generalize = (uu___1749_23159.generalize);
          letrecs = (uu___1749_23159.letrecs);
          top_level = (uu___1749_23159.top_level);
          check_uvars = (uu___1749_23159.check_uvars);
          use_eq = (uu___1749_23159.use_eq);
          is_iface = (uu___1749_23159.is_iface);
          admit = (uu___1749_23159.admit);
          lax = (uu___1749_23159.lax);
          lax_universes = (uu___1749_23159.lax_universes);
          phase1 = (uu___1749_23159.phase1);
          failhard = (uu___1749_23159.failhard);
          nosynth = (uu___1749_23159.nosynth);
          uvar_subtyping = (uu___1749_23159.uvar_subtyping);
          tc_term = (uu___1749_23159.tc_term);
          type_of = (uu___1749_23159.type_of);
          universe_of = (uu___1749_23159.universe_of);
          check_type_of = (uu___1749_23159.check_type_of);
          use_bv_sorts = (uu___1749_23159.use_bv_sorts);
          qtbl_name_and_index = (uu___1749_23159.qtbl_name_and_index);
          normalized_eff_names = (uu___1749_23159.normalized_eff_names);
          fv_delta_depths = (uu___1749_23159.fv_delta_depths);
          proof_ns = (uu___1749_23159.proof_ns);
          synth_hook = (uu___1749_23159.synth_hook);
          splice = (uu___1749_23159.splice);
          postprocess = (uu___1749_23159.postprocess);
          is_native_tactic = (uu___1749_23159.is_native_tactic);
          identifier_info = (uu___1749_23159.identifier_info);
          tc_hooks = (uu___1749_23159.tc_hooks);
          dsenv = (uu___1749_23159.dsenv);
          nbe = (uu___1749_23159.nbe);
          strict_args_tab = (uu___1749_23159.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1756_23173 = env  in
      {
        solver = (uu___1756_23173.solver);
        range = (uu___1756_23173.range);
        curmodule = (uu___1756_23173.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1756_23173.gamma_sig);
        gamma_cache = (uu___1756_23173.gamma_cache);
        modules = (uu___1756_23173.modules);
        expected_typ = (uu___1756_23173.expected_typ);
        sigtab = (uu___1756_23173.sigtab);
        attrtab = (uu___1756_23173.attrtab);
        is_pattern = (uu___1756_23173.is_pattern);
        instantiate_imp = (uu___1756_23173.instantiate_imp);
        effects = (uu___1756_23173.effects);
        generalize = (uu___1756_23173.generalize);
        letrecs = (uu___1756_23173.letrecs);
        top_level = (uu___1756_23173.top_level);
        check_uvars = (uu___1756_23173.check_uvars);
        use_eq = (uu___1756_23173.use_eq);
        is_iface = (uu___1756_23173.is_iface);
        admit = (uu___1756_23173.admit);
        lax = (uu___1756_23173.lax);
        lax_universes = (uu___1756_23173.lax_universes);
        phase1 = (uu___1756_23173.phase1);
        failhard = (uu___1756_23173.failhard);
        nosynth = (uu___1756_23173.nosynth);
        uvar_subtyping = (uu___1756_23173.uvar_subtyping);
        tc_term = (uu___1756_23173.tc_term);
        type_of = (uu___1756_23173.type_of);
        universe_of = (uu___1756_23173.universe_of);
        check_type_of = (uu___1756_23173.check_type_of);
        use_bv_sorts = (uu___1756_23173.use_bv_sorts);
        qtbl_name_and_index = (uu___1756_23173.qtbl_name_and_index);
        normalized_eff_names = (uu___1756_23173.normalized_eff_names);
        fv_delta_depths = (uu___1756_23173.fv_delta_depths);
        proof_ns = (uu___1756_23173.proof_ns);
        synth_hook = (uu___1756_23173.synth_hook);
        splice = (uu___1756_23173.splice);
        postprocess = (uu___1756_23173.postprocess);
        is_native_tactic = (uu___1756_23173.is_native_tactic);
        identifier_info = (uu___1756_23173.identifier_info);
        tc_hooks = (uu___1756_23173.tc_hooks);
        dsenv = (uu___1756_23173.dsenv);
        nbe = (uu___1756_23173.nbe);
        strict_args_tab = (uu___1756_23173.strict_args_tab)
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
            (let uu___1769_23231 = env  in
             {
               solver = (uu___1769_23231.solver);
               range = (uu___1769_23231.range);
               curmodule = (uu___1769_23231.curmodule);
               gamma = rest;
               gamma_sig = (uu___1769_23231.gamma_sig);
               gamma_cache = (uu___1769_23231.gamma_cache);
               modules = (uu___1769_23231.modules);
               expected_typ = (uu___1769_23231.expected_typ);
               sigtab = (uu___1769_23231.sigtab);
               attrtab = (uu___1769_23231.attrtab);
               is_pattern = (uu___1769_23231.is_pattern);
               instantiate_imp = (uu___1769_23231.instantiate_imp);
               effects = (uu___1769_23231.effects);
               generalize = (uu___1769_23231.generalize);
               letrecs = (uu___1769_23231.letrecs);
               top_level = (uu___1769_23231.top_level);
               check_uvars = (uu___1769_23231.check_uvars);
               use_eq = (uu___1769_23231.use_eq);
               is_iface = (uu___1769_23231.is_iface);
               admit = (uu___1769_23231.admit);
               lax = (uu___1769_23231.lax);
               lax_universes = (uu___1769_23231.lax_universes);
               phase1 = (uu___1769_23231.phase1);
               failhard = (uu___1769_23231.failhard);
               nosynth = (uu___1769_23231.nosynth);
               uvar_subtyping = (uu___1769_23231.uvar_subtyping);
               tc_term = (uu___1769_23231.tc_term);
               type_of = (uu___1769_23231.type_of);
               universe_of = (uu___1769_23231.universe_of);
               check_type_of = (uu___1769_23231.check_type_of);
               use_bv_sorts = (uu___1769_23231.use_bv_sorts);
               qtbl_name_and_index = (uu___1769_23231.qtbl_name_and_index);
               normalized_eff_names = (uu___1769_23231.normalized_eff_names);
               fv_delta_depths = (uu___1769_23231.fv_delta_depths);
               proof_ns = (uu___1769_23231.proof_ns);
               synth_hook = (uu___1769_23231.synth_hook);
               splice = (uu___1769_23231.splice);
               postprocess = (uu___1769_23231.postprocess);
               is_native_tactic = (uu___1769_23231.is_native_tactic);
               identifier_info = (uu___1769_23231.identifier_info);
               tc_hooks = (uu___1769_23231.tc_hooks);
               dsenv = (uu___1769_23231.dsenv);
               nbe = (uu___1769_23231.nbe);
               strict_args_tab = (uu___1769_23231.strict_args_tab)
             }))
    | uu____23232 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23261  ->
             match uu____23261 with | (x,uu____23269) -> push_bv env1 x) env
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
            let uu___1783_23304 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1783_23304.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1783_23304.FStar_Syntax_Syntax.index);
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
      (let uu___1794_23346 = env  in
       {
         solver = (uu___1794_23346.solver);
         range = (uu___1794_23346.range);
         curmodule = (uu___1794_23346.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1794_23346.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1794_23346.sigtab);
         attrtab = (uu___1794_23346.attrtab);
         is_pattern = (uu___1794_23346.is_pattern);
         instantiate_imp = (uu___1794_23346.instantiate_imp);
         effects = (uu___1794_23346.effects);
         generalize = (uu___1794_23346.generalize);
         letrecs = (uu___1794_23346.letrecs);
         top_level = (uu___1794_23346.top_level);
         check_uvars = (uu___1794_23346.check_uvars);
         use_eq = (uu___1794_23346.use_eq);
         is_iface = (uu___1794_23346.is_iface);
         admit = (uu___1794_23346.admit);
         lax = (uu___1794_23346.lax);
         lax_universes = (uu___1794_23346.lax_universes);
         phase1 = (uu___1794_23346.phase1);
         failhard = (uu___1794_23346.failhard);
         nosynth = (uu___1794_23346.nosynth);
         uvar_subtyping = (uu___1794_23346.uvar_subtyping);
         tc_term = (uu___1794_23346.tc_term);
         type_of = (uu___1794_23346.type_of);
         universe_of = (uu___1794_23346.universe_of);
         check_type_of = (uu___1794_23346.check_type_of);
         use_bv_sorts = (uu___1794_23346.use_bv_sorts);
         qtbl_name_and_index = (uu___1794_23346.qtbl_name_and_index);
         normalized_eff_names = (uu___1794_23346.normalized_eff_names);
         fv_delta_depths = (uu___1794_23346.fv_delta_depths);
         proof_ns = (uu___1794_23346.proof_ns);
         synth_hook = (uu___1794_23346.synth_hook);
         splice = (uu___1794_23346.splice);
         postprocess = (uu___1794_23346.postprocess);
         is_native_tactic = (uu___1794_23346.is_native_tactic);
         identifier_info = (uu___1794_23346.identifier_info);
         tc_hooks = (uu___1794_23346.tc_hooks);
         dsenv = (uu___1794_23346.dsenv);
         nbe = (uu___1794_23346.nbe);
         strict_args_tab = (uu___1794_23346.strict_args_tab)
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
        let uu____23390 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23390 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23418 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23418)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1809_23434 = env  in
      {
        solver = (uu___1809_23434.solver);
        range = (uu___1809_23434.range);
        curmodule = (uu___1809_23434.curmodule);
        gamma = (uu___1809_23434.gamma);
        gamma_sig = (uu___1809_23434.gamma_sig);
        gamma_cache = (uu___1809_23434.gamma_cache);
        modules = (uu___1809_23434.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1809_23434.sigtab);
        attrtab = (uu___1809_23434.attrtab);
        is_pattern = (uu___1809_23434.is_pattern);
        instantiate_imp = (uu___1809_23434.instantiate_imp);
        effects = (uu___1809_23434.effects);
        generalize = (uu___1809_23434.generalize);
        letrecs = (uu___1809_23434.letrecs);
        top_level = (uu___1809_23434.top_level);
        check_uvars = (uu___1809_23434.check_uvars);
        use_eq = false;
        is_iface = (uu___1809_23434.is_iface);
        admit = (uu___1809_23434.admit);
        lax = (uu___1809_23434.lax);
        lax_universes = (uu___1809_23434.lax_universes);
        phase1 = (uu___1809_23434.phase1);
        failhard = (uu___1809_23434.failhard);
        nosynth = (uu___1809_23434.nosynth);
        uvar_subtyping = (uu___1809_23434.uvar_subtyping);
        tc_term = (uu___1809_23434.tc_term);
        type_of = (uu___1809_23434.type_of);
        universe_of = (uu___1809_23434.universe_of);
        check_type_of = (uu___1809_23434.check_type_of);
        use_bv_sorts = (uu___1809_23434.use_bv_sorts);
        qtbl_name_and_index = (uu___1809_23434.qtbl_name_and_index);
        normalized_eff_names = (uu___1809_23434.normalized_eff_names);
        fv_delta_depths = (uu___1809_23434.fv_delta_depths);
        proof_ns = (uu___1809_23434.proof_ns);
        synth_hook = (uu___1809_23434.synth_hook);
        splice = (uu___1809_23434.splice);
        postprocess = (uu___1809_23434.postprocess);
        is_native_tactic = (uu___1809_23434.is_native_tactic);
        identifier_info = (uu___1809_23434.identifier_info);
        tc_hooks = (uu___1809_23434.tc_hooks);
        dsenv = (uu___1809_23434.dsenv);
        nbe = (uu___1809_23434.nbe);
        strict_args_tab = (uu___1809_23434.strict_args_tab)
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
    let uu____23465 = expected_typ env_  in
    ((let uu___1816_23471 = env_  in
      {
        solver = (uu___1816_23471.solver);
        range = (uu___1816_23471.range);
        curmodule = (uu___1816_23471.curmodule);
        gamma = (uu___1816_23471.gamma);
        gamma_sig = (uu___1816_23471.gamma_sig);
        gamma_cache = (uu___1816_23471.gamma_cache);
        modules = (uu___1816_23471.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1816_23471.sigtab);
        attrtab = (uu___1816_23471.attrtab);
        is_pattern = (uu___1816_23471.is_pattern);
        instantiate_imp = (uu___1816_23471.instantiate_imp);
        effects = (uu___1816_23471.effects);
        generalize = (uu___1816_23471.generalize);
        letrecs = (uu___1816_23471.letrecs);
        top_level = (uu___1816_23471.top_level);
        check_uvars = (uu___1816_23471.check_uvars);
        use_eq = false;
        is_iface = (uu___1816_23471.is_iface);
        admit = (uu___1816_23471.admit);
        lax = (uu___1816_23471.lax);
        lax_universes = (uu___1816_23471.lax_universes);
        phase1 = (uu___1816_23471.phase1);
        failhard = (uu___1816_23471.failhard);
        nosynth = (uu___1816_23471.nosynth);
        uvar_subtyping = (uu___1816_23471.uvar_subtyping);
        tc_term = (uu___1816_23471.tc_term);
        type_of = (uu___1816_23471.type_of);
        universe_of = (uu___1816_23471.universe_of);
        check_type_of = (uu___1816_23471.check_type_of);
        use_bv_sorts = (uu___1816_23471.use_bv_sorts);
        qtbl_name_and_index = (uu___1816_23471.qtbl_name_and_index);
        normalized_eff_names = (uu___1816_23471.normalized_eff_names);
        fv_delta_depths = (uu___1816_23471.fv_delta_depths);
        proof_ns = (uu___1816_23471.proof_ns);
        synth_hook = (uu___1816_23471.synth_hook);
        splice = (uu___1816_23471.splice);
        postprocess = (uu___1816_23471.postprocess);
        is_native_tactic = (uu___1816_23471.is_native_tactic);
        identifier_info = (uu___1816_23471.identifier_info);
        tc_hooks = (uu___1816_23471.tc_hooks);
        dsenv = (uu___1816_23471.dsenv);
        nbe = (uu___1816_23471.nbe);
        strict_args_tab = (uu___1816_23471.strict_args_tab)
      }), uu____23465)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23483 =
      let uu____23486 = FStar_Ident.id_of_text ""  in [uu____23486]  in
    FStar_Ident.lid_of_ids uu____23483  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23493 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23493
        then
          let uu____23498 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23498 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1824_23526 = env  in
       {
         solver = (uu___1824_23526.solver);
         range = (uu___1824_23526.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1824_23526.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1824_23526.expected_typ);
         sigtab = (uu___1824_23526.sigtab);
         attrtab = (uu___1824_23526.attrtab);
         is_pattern = (uu___1824_23526.is_pattern);
         instantiate_imp = (uu___1824_23526.instantiate_imp);
         effects = (uu___1824_23526.effects);
         generalize = (uu___1824_23526.generalize);
         letrecs = (uu___1824_23526.letrecs);
         top_level = (uu___1824_23526.top_level);
         check_uvars = (uu___1824_23526.check_uvars);
         use_eq = (uu___1824_23526.use_eq);
         is_iface = (uu___1824_23526.is_iface);
         admit = (uu___1824_23526.admit);
         lax = (uu___1824_23526.lax);
         lax_universes = (uu___1824_23526.lax_universes);
         phase1 = (uu___1824_23526.phase1);
         failhard = (uu___1824_23526.failhard);
         nosynth = (uu___1824_23526.nosynth);
         uvar_subtyping = (uu___1824_23526.uvar_subtyping);
         tc_term = (uu___1824_23526.tc_term);
         type_of = (uu___1824_23526.type_of);
         universe_of = (uu___1824_23526.universe_of);
         check_type_of = (uu___1824_23526.check_type_of);
         use_bv_sorts = (uu___1824_23526.use_bv_sorts);
         qtbl_name_and_index = (uu___1824_23526.qtbl_name_and_index);
         normalized_eff_names = (uu___1824_23526.normalized_eff_names);
         fv_delta_depths = (uu___1824_23526.fv_delta_depths);
         proof_ns = (uu___1824_23526.proof_ns);
         synth_hook = (uu___1824_23526.synth_hook);
         splice = (uu___1824_23526.splice);
         postprocess = (uu___1824_23526.postprocess);
         is_native_tactic = (uu___1824_23526.is_native_tactic);
         identifier_info = (uu___1824_23526.identifier_info);
         tc_hooks = (uu___1824_23526.tc_hooks);
         dsenv = (uu___1824_23526.dsenv);
         nbe = (uu___1824_23526.nbe);
         strict_args_tab = (uu___1824_23526.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23578)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23582,(uu____23583,t)))::tl1
          ->
          let uu____23604 =
            let uu____23607 = FStar_Syntax_Free.uvars t  in
            ext out uu____23607  in
          aux uu____23604 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23610;
            FStar_Syntax_Syntax.index = uu____23611;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23619 =
            let uu____23622 = FStar_Syntax_Free.uvars t  in
            ext out uu____23622  in
          aux uu____23619 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23680)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23684,(uu____23685,t)))::tl1
          ->
          let uu____23706 =
            let uu____23709 = FStar_Syntax_Free.univs t  in
            ext out uu____23709  in
          aux uu____23706 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23712;
            FStar_Syntax_Syntax.index = uu____23713;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23721 =
            let uu____23724 = FStar_Syntax_Free.univs t  in
            ext out uu____23724  in
          aux uu____23721 tl1
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
          let uu____23786 = FStar_Util.set_add uname out  in
          aux uu____23786 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23789,(uu____23790,t)))::tl1
          ->
          let uu____23811 =
            let uu____23814 = FStar_Syntax_Free.univnames t  in
            ext out uu____23814  in
          aux uu____23811 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23817;
            FStar_Syntax_Syntax.index = uu____23818;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23826 =
            let uu____23829 = FStar_Syntax_Free.univnames t  in
            ext out uu____23829  in
          aux uu____23826 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_23850  ->
            match uu___11_23850 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23854 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23867 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23878 =
      let uu____23887 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23887
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23878 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23935 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_23948  ->
              match uu___12_23948 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23951 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____23951
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23957) ->
                  let uu____23974 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____23974))
       in
    FStar_All.pipe_right uu____23935 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_23988  ->
    match uu___13_23988 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23994 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____23994
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24017  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24072) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24105,uu____24106) -> false  in
      let uu____24120 =
        FStar_List.tryFind
          (fun uu____24142  ->
             match uu____24142 with | (p,uu____24153) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24120 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24172,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24202 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24202
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1967_24224 = e  in
        {
          solver = (uu___1967_24224.solver);
          range = (uu___1967_24224.range);
          curmodule = (uu___1967_24224.curmodule);
          gamma = (uu___1967_24224.gamma);
          gamma_sig = (uu___1967_24224.gamma_sig);
          gamma_cache = (uu___1967_24224.gamma_cache);
          modules = (uu___1967_24224.modules);
          expected_typ = (uu___1967_24224.expected_typ);
          sigtab = (uu___1967_24224.sigtab);
          attrtab = (uu___1967_24224.attrtab);
          is_pattern = (uu___1967_24224.is_pattern);
          instantiate_imp = (uu___1967_24224.instantiate_imp);
          effects = (uu___1967_24224.effects);
          generalize = (uu___1967_24224.generalize);
          letrecs = (uu___1967_24224.letrecs);
          top_level = (uu___1967_24224.top_level);
          check_uvars = (uu___1967_24224.check_uvars);
          use_eq = (uu___1967_24224.use_eq);
          is_iface = (uu___1967_24224.is_iface);
          admit = (uu___1967_24224.admit);
          lax = (uu___1967_24224.lax);
          lax_universes = (uu___1967_24224.lax_universes);
          phase1 = (uu___1967_24224.phase1);
          failhard = (uu___1967_24224.failhard);
          nosynth = (uu___1967_24224.nosynth);
          uvar_subtyping = (uu___1967_24224.uvar_subtyping);
          tc_term = (uu___1967_24224.tc_term);
          type_of = (uu___1967_24224.type_of);
          universe_of = (uu___1967_24224.universe_of);
          check_type_of = (uu___1967_24224.check_type_of);
          use_bv_sorts = (uu___1967_24224.use_bv_sorts);
          qtbl_name_and_index = (uu___1967_24224.qtbl_name_and_index);
          normalized_eff_names = (uu___1967_24224.normalized_eff_names);
          fv_delta_depths = (uu___1967_24224.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1967_24224.synth_hook);
          splice = (uu___1967_24224.splice);
          postprocess = (uu___1967_24224.postprocess);
          is_native_tactic = (uu___1967_24224.is_native_tactic);
          identifier_info = (uu___1967_24224.identifier_info);
          tc_hooks = (uu___1967_24224.tc_hooks);
          dsenv = (uu___1967_24224.dsenv);
          nbe = (uu___1967_24224.nbe);
          strict_args_tab = (uu___1967_24224.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1976_24272 = e  in
      {
        solver = (uu___1976_24272.solver);
        range = (uu___1976_24272.range);
        curmodule = (uu___1976_24272.curmodule);
        gamma = (uu___1976_24272.gamma);
        gamma_sig = (uu___1976_24272.gamma_sig);
        gamma_cache = (uu___1976_24272.gamma_cache);
        modules = (uu___1976_24272.modules);
        expected_typ = (uu___1976_24272.expected_typ);
        sigtab = (uu___1976_24272.sigtab);
        attrtab = (uu___1976_24272.attrtab);
        is_pattern = (uu___1976_24272.is_pattern);
        instantiate_imp = (uu___1976_24272.instantiate_imp);
        effects = (uu___1976_24272.effects);
        generalize = (uu___1976_24272.generalize);
        letrecs = (uu___1976_24272.letrecs);
        top_level = (uu___1976_24272.top_level);
        check_uvars = (uu___1976_24272.check_uvars);
        use_eq = (uu___1976_24272.use_eq);
        is_iface = (uu___1976_24272.is_iface);
        admit = (uu___1976_24272.admit);
        lax = (uu___1976_24272.lax);
        lax_universes = (uu___1976_24272.lax_universes);
        phase1 = (uu___1976_24272.phase1);
        failhard = (uu___1976_24272.failhard);
        nosynth = (uu___1976_24272.nosynth);
        uvar_subtyping = (uu___1976_24272.uvar_subtyping);
        tc_term = (uu___1976_24272.tc_term);
        type_of = (uu___1976_24272.type_of);
        universe_of = (uu___1976_24272.universe_of);
        check_type_of = (uu___1976_24272.check_type_of);
        use_bv_sorts = (uu___1976_24272.use_bv_sorts);
        qtbl_name_and_index = (uu___1976_24272.qtbl_name_and_index);
        normalized_eff_names = (uu___1976_24272.normalized_eff_names);
        fv_delta_depths = (uu___1976_24272.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1976_24272.synth_hook);
        splice = (uu___1976_24272.splice);
        postprocess = (uu___1976_24272.postprocess);
        is_native_tactic = (uu___1976_24272.is_native_tactic);
        identifier_info = (uu___1976_24272.identifier_info);
        tc_hooks = (uu___1976_24272.tc_hooks);
        dsenv = (uu___1976_24272.dsenv);
        nbe = (uu___1976_24272.nbe);
        strict_args_tab = (uu___1976_24272.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24288 = FStar_Syntax_Free.names t  in
      let uu____24291 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24288 uu____24291
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24314 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24314
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24324 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24324
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24345 =
      match uu____24345 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24365 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24365)
       in
    let uu____24373 =
      let uu____24377 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24377 FStar_List.rev  in
    FStar_All.pipe_right uu____24373 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Common.guard_f = g;
      FStar_TypeChecker_Common.deferred = [];
      FStar_TypeChecker_Common.univ_ineqs = ([], []);
      FStar_TypeChecker_Common.implicits = []
    }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.FStar_TypeChecker_Common.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([],[]);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____24445 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24445 with
                   | FStar_Pervasives_Native.Some uu____24449 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24452 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____24462;
        FStar_TypeChecker_Common.univ_ineqs = uu____24463;
        FStar_TypeChecker_Common.implicits = uu____24464;_} -> true
    | uu____24474 -> false
  
let (trivial_guard : guard_t) = FStar_TypeChecker_Common.trivial_guard 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___2020_24496 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2020_24496.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2020_24496.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2020_24496.FStar_TypeChecker_Common.implicits)
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
          let uu____24535 = FStar_Options.defensive ()  in
          if uu____24535
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24541 =
              let uu____24543 =
                let uu____24545 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24545  in
              Prims.op_Negation uu____24543  in
            (if uu____24541
             then
               let uu____24552 =
                 let uu____24558 =
                   let uu____24560 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24562 =
                     let uu____24564 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24564
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24560 uu____24562
                    in
                 (FStar_Errors.Warning_Defensive, uu____24558)  in
               FStar_Errors.log_issue rng uu____24552
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
          let uu____24604 =
            let uu____24606 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24606  in
          if uu____24604
          then ()
          else
            (let uu____24611 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24611 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24637 =
            let uu____24639 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24639  in
          if uu____24637
          then ()
          else
            (let uu____24644 = bound_vars e  in
             def_check_closed_in rng msg uu____24644 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.FStar_TypeChecker_Common.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2057_24683 = g  in
          let uu____24684 =
            let uu____24685 =
              let uu____24686 =
                let uu____24693 =
                  let uu____24694 =
                    let uu____24711 =
                      let uu____24722 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24722]  in
                    (f, uu____24711)  in
                  FStar_Syntax_Syntax.Tm_app uu____24694  in
                FStar_Syntax_Syntax.mk uu____24693  in
              uu____24686 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24759  -> FStar_TypeChecker_Common.NonTrivial _24759)
              uu____24685
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____24684;
            FStar_TypeChecker_Common.deferred =
              (uu___2057_24683.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2057_24683.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2057_24683.FStar_TypeChecker_Common.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2064_24777 = g  in
          let uu____24778 =
            let uu____24779 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24779  in
          {
            FStar_TypeChecker_Common.guard_f = uu____24778;
            FStar_TypeChecker_Common.deferred =
              (uu___2064_24777.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2064_24777.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2064_24777.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2069_24796 = g  in
          let uu____24797 =
            let uu____24798 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24798  in
          {
            FStar_TypeChecker_Common.guard_f = uu____24797;
            FStar_TypeChecker_Common.deferred =
              (uu___2069_24796.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2069_24796.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2069_24796.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2073_24800 = g  in
          let uu____24801 =
            let uu____24802 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24802  in
          {
            FStar_TypeChecker_Common.guard_f = uu____24801;
            FStar_TypeChecker_Common.deferred =
              (uu___2073_24800.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2073_24800.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2073_24800.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24809 ->
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
          let uu____24826 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24826
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24833 =
      let uu____24834 = FStar_Syntax_Util.unmeta t  in
      uu____24834.FStar_Syntax_Syntax.n  in
    match uu____24833 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24838 -> FStar_TypeChecker_Common.NonTrivial t
  
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
    ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____24881 =
          f g1.FStar_TypeChecker_Common.guard_f
            g2.FStar_TypeChecker_Common.guard_f
           in
        {
          FStar_TypeChecker_Common.guard_f = uu____24881;
          FStar_TypeChecker_Common.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Common.deferred
               g2.FStar_TypeChecker_Common.deferred);
          FStar_TypeChecker_Common.univ_ineqs =
            ((FStar_List.append
                (FStar_Pervasives_Native.fst
                   g1.FStar_TypeChecker_Common.univ_ineqs)
                (FStar_Pervasives_Native.fst
                   g2.FStar_TypeChecker_Common.univ_ineqs)),
              (FStar_List.append
                 (FStar_Pervasives_Native.snd
                    g1.FStar_TypeChecker_Common.univ_ineqs)
                 (FStar_Pervasives_Native.snd
                    g2.FStar_TypeChecker_Common.univ_ineqs)));
          FStar_TypeChecker_Common.implicits =
            (FStar_List.append g1.FStar_TypeChecker_Common.implicits
               g2.FStar_TypeChecker_Common.implicits)
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
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____24976 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24976
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2128_24983 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2128_24983.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2128_24983.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2128_24983.FStar_TypeChecker_Common.implicits)
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
               let uu____25017 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25017
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
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2143_25044 = g  in
            let uu____25045 =
              let uu____25046 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25046  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25045;
              FStar_TypeChecker_Common.deferred =
                (uu___2143_25044.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2143_25044.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2143_25044.FStar_TypeChecker_Common.implicits)
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
              let uu____25104 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25104 with
              | FStar_Pervasives_Native.Some
                  (uu____25129::(tm,uu____25131)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25195 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25213 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25213;
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
                        FStar_TypeChecker_Common.imp_reason = reason;
                        FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                        FStar_TypeChecker_Common.imp_tm = t;
                        FStar_TypeChecker_Common.imp_range = r
                      }  in
                    let g =
                      let uu___2165_25245 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2165_25245.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2165_25245.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2165_25245.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (lift_to_layered_effect :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Ident.lident -> (FStar_Syntax_Syntax.comp * guard_t))
  =
  fun env  ->
    fun c  ->
      fun eff_name  ->
        (let uu____25285 =
           FStar_All.pipe_left (debug env)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____25285
         then
           let uu____25290 = FStar_Syntax_Print.comp_to_string c  in
           let uu____25292 = FStar_Syntax_Print.lid_to_string eff_name  in
           FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
             uu____25290 uu____25292
         else ());
        (let ct = unfold_effect_abbrev env c  in
         let uu____25298 =
           FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name eff_name
            in
         if uu____25298
         then (c, trivial_guard)
         else
           (let src_ed =
              get_effect_decl env ct.FStar_Syntax_Syntax.effect_name  in
            let dst_ed = get_effect_decl env eff_name  in
            if
              src_ed.FStar_Syntax_Syntax.is_layered ||
                (Prims.op_Negation dst_ed.FStar_Syntax_Syntax.is_layered)
            then
              failwith
                "lift_to_layered_effect called with layered src or non-layered dst"
            else ();
            (let lift_t =
               let uu____25315 =
                 monad_leq env src_ed.FStar_Syntax_Syntax.mname
                   dst_ed.FStar_Syntax_Syntax.mname
                  in
               match uu____25315 with
               | FStar_Pervasives_Native.None  ->
                   failwith
                     (Prims.op_Hat "Could not find an edge from "
                        (Prims.op_Hat
                           (src_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                           (Prims.op_Hat " to "
                              (dst_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str)))
               | FStar_Pervasives_Native.Some lift ->
                   FStar_All.pipe_right (lift.mlift).mlift_t FStar_Util.must
                in
             let uu____25323 = FStar_Syntax_Util.destruct_comp ct  in
             match uu____25323 with
             | (u,a,wp) ->
                 let uu____25337 = inst_tscheme_with lift_t [u]  in
                 (match uu____25337 with
                  | (uu____25346,lift_t1) ->
                      let uu____25348 =
                        let uu____25361 =
                          let uu____25362 =
                            FStar_Syntax_Subst.compress lift_t1  in
                          uu____25362.FStar_Syntax_Syntax.n  in
                        match uu____25361 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs,c1) ->
                            let uu____25399 =
                              FStar_Syntax_Subst.open_comp bs c1  in
                            FStar_All.pipe_right uu____25399
                              (fun uu____25416  ->
                                 match uu____25416 with
                                 | (bs1,c2) ->
                                     let uu____25427 =
                                       FStar_Syntax_Util.comp_to_comp_typ c2
                                        in
                                     (bs1, uu____25427))
                        | uu____25428 ->
                            let uu____25429 =
                              let uu____25431 =
                                let uu____25433 =
                                  FStar_Syntax_Print.term_to_string lift_t1
                                   in
                                Prims.op_Hat uu____25433
                                  " is not an arrow type"
                                 in
                              Prims.op_Hat "lift_t: " uu____25431  in
                            failwith uu____25429
                         in
                      (match uu____25348 with
                       | (lift_bs,lift_ct) ->
                           let uu____25471 =
                             match lift_bs with
                             | a_b::wp_b::bs when
                                 (FStar_List.length bs) >= Prims.int_one ->
                                 let uu____25550 =
                                   let uu____25551 =
                                     FStar_List.splitAt
                                       ((FStar_List.length bs) -
                                          Prims.int_one) bs
                                      in
                                   FStar_All.pipe_right uu____25551
                                     FStar_Pervasives_Native.fst
                                    in
                                 (a_b, wp_b, uu____25550)
                             | uu____25609 ->
                                 let uu____25618 =
                                   let uu____25620 =
                                     let uu____25622 =
                                       FStar_Syntax_Print.term_to_string
                                         lift_t1
                                        in
                                     Prims.op_Hat uu____25622
                                       " does not have enough binders"
                                      in
                                   Prims.op_Hat "lift_t: " uu____25620  in
                                 failwith uu____25618
                              in
                           (match uu____25471 with
                            | (a_b,wp_b,rest_bs) ->
                                let rest_bs1 =
                                  let uu____25676 =
                                    let uu____25679 =
                                      let uu____25680 =
                                        let uu____25687 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____25687, a)  in
                                      FStar_Syntax_Syntax.NT uu____25680  in
                                    let uu____25698 =
                                      let uu____25701 =
                                        let uu____25702 =
                                          let uu____25709 =
                                            FStar_All.pipe_right wp_b
                                              FStar_Pervasives_Native.fst
                                             in
                                          (uu____25709, wp)  in
                                        FStar_Syntax_Syntax.NT uu____25702
                                         in
                                      [uu____25701]  in
                                    uu____25679 :: uu____25698  in
                                  FStar_Syntax_Subst.subst_binders
                                    uu____25676 rest_bs
                                   in
                                let uu____25720 =
                                  let uu____25727 =
                                    let uu____25728 =
                                      FStar_Syntax_Subst.compress
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                       in
                                    uu____25728.FStar_Syntax_Syntax.n  in
                                  match uu____25727 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____25737,uu____25738::is) ->
                                      let uu____25780 =
                                        FStar_List.map
                                          FStar_Pervasives_Native.fst is
                                         in
                                      ((lift_ct.FStar_Syntax_Syntax.comp_univs),
                                        uu____25780)
                                  | uu____25797 ->
                                      let uu____25798 =
                                        let uu____25800 =
                                          let uu____25802 =
                                            FStar_Syntax_Print.term_to_string
                                              lift_t1
                                             in
                                          Prims.op_Hat uu____25802
                                            " does not have a repr return type"
                                           in
                                        Prims.op_Hat "lift_t: " uu____25800
                                         in
                                      failwith uu____25798
                                   in
                                (match uu____25720 with
                                 | (u_m,is) ->
                                     let uu____25822 =
                                       let uu____25831 =
                                         FStar_List.fold_left
                                           (fun uu____25871  ->
                                              fun b  ->
                                                match uu____25871 with
                                                | (substs,is_uvars,g) ->
                                                    let sort =
                                                      FStar_Syntax_Subst.subst
                                                        substs
                                                        (FStar_Pervasives_Native.fst
                                                           b).FStar_Syntax_Syntax.sort
                                                       in
                                                    let uu____25913 =
                                                      new_implicit_var_aux ""
                                                        FStar_Range.dummyRange
                                                        env sort
                                                        FStar_Syntax_Syntax.Strict
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    (match uu____25913 with
                                                     | (t,uu____25942,g_t) ->
                                                         ((let uu____25957 =
                                                             FStar_All.pipe_left
                                                               (debug env)
                                                               (FStar_Options.Other
                                                                  "LayeredEffects")
                                                              in
                                                           if uu____25957
                                                           then
                                                             let uu____25962
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t
                                                                in
                                                             let uu____25964
                                                               =
                                                               FStar_Syntax_Print.binder_to_string
                                                                 b
                                                                in
                                                             FStar_Util.print2
                                                               "lift_to_layered_effect: introduced uvar %s for binder %s\n"
                                                               uu____25962
                                                               uu____25964
                                                           else ());
                                                          (let uu____25969 =
                                                             let uu____25972
                                                               =
                                                               let uu____25975
                                                                 =
                                                                 let uu____25976
                                                                   =
                                                                   let uu____25983
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                   (uu____25983,
                                                                    t)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____25976
                                                                  in
                                                               [uu____25975]
                                                                in
                                                             FStar_List.append
                                                               substs
                                                               uu____25972
                                                              in
                                                           let uu____25994 =
                                                             conj_guard g g_t
                                                              in
                                                           (uu____25969,
                                                             (FStar_List.append
                                                                is_uvars 
                                                                [t]),
                                                             uu____25994)))))
                                           ([], [], trivial_guard) rest_bs1
                                          in
                                       match uu____25831 with
                                       | (uu____26011,rest_bs_uvars,g) ->
                                           (rest_bs_uvars, g)
                                        in
                                     (match uu____25822 with
                                      | (rest_bs_uvars,g) ->
                                          let subst_for_is =
                                            FStar_List.map2
                                              (fun b  ->
                                                 fun t  ->
                                                   let uu____26064 =
                                                     let uu____26071 =
                                                       FStar_All.pipe_right b
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     (uu____26071, t)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____26064) (a_b ::
                                              wp_b :: rest_bs1) (a :: wp ::
                                              rest_bs_uvars)
                                             in
                                          let is1 =
                                            FStar_List.map
                                              (FStar_Syntax_Subst.subst
                                                 subst_for_is) is
                                             in
                                          let c1 =
                                            let uu____26102 =
                                              let uu____26103 =
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  is1
                                                 in
                                              {
                                                FStar_Syntax_Syntax.comp_univs
                                                  = u_m;
                                                FStar_Syntax_Syntax.effect_name
                                                  = eff_name;
                                                FStar_Syntax_Syntax.result_typ
                                                  = a;
                                                FStar_Syntax_Syntax.effect_args
                                                  = uu____26103;
                                                FStar_Syntax_Syntax.flags =
                                                  []
                                              }  in
                                            FStar_Syntax_Syntax.mk_Comp
                                              uu____26102
                                             in
                                          ((let uu____26123 =
                                              FStar_All.pipe_left (debug env)
                                                (FStar_Options.Other
                                                   "LayeredEffects")
                                               in
                                            if uu____26123
                                            then
                                              let uu____26128 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c1
                                                 in
                                              FStar_Util.print1
                                                "} Lifted comp: %s\n"
                                                uu____26128
                                            else ());
                                           (c1, g))))))))))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26136  -> ());
    push = (fun uu____26138  -> ());
    pop = (fun uu____26141  -> ());
    snapshot =
      (fun uu____26144  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26163  -> fun uu____26164  -> ());
    encode_sig = (fun uu____26179  -> fun uu____26180  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26186 =
             let uu____26193 = FStar_Options.peek ()  in (e, g, uu____26193)
              in
           [uu____26186]);
    solve = (fun uu____26209  -> fun uu____26210  -> fun uu____26211  -> ());
    finish = (fun uu____26218  -> ());
    refresh = (fun uu____26220  -> ())
  } 