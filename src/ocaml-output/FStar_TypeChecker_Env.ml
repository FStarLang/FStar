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
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type mlift =
  {
  mlift_wp:
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
and edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
and effects =
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
and env =
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
  try_solve_implicits_hook:
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit
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
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
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
  
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mlift
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> solver
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> range
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> curmodule
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> gamma
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> gamma_sig
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> gamma_cache
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> modules
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> expected_typ
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> sigtab
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> attrtab
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> is_pattern
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> instantiate_imp
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> effects
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> generalize
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> letrecs
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> top_level
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> check_uvars
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> use_eq
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> is_iface
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> admit1
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> lax1
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> lax_universes
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> phase1
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> failhard
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> nosynth
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> uvar_subtyping
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> tc_term
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> type_of
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> universe_of
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> check_type_of
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> use_bv_sorts
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> qtbl_name_and_index
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> normalized_eff_names
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> fv_delta_depths
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> proof_ns
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> try_solve_implicits_hook
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> splice1
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> postprocess
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> is_native_tactic
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> identifier_info
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> tc_hooks
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> dsenv
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> nbe1
  
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
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> strict_args_tab
  
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
  
type lift_comp_t =
  env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
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
           (fun uu___0_12870  ->
              match uu___0_12870 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12873 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12873  in
                  let uu____12874 =
                    let uu____12875 = FStar_Syntax_Subst.compress y  in
                    uu____12875.FStar_Syntax_Syntax.n  in
                  (match uu____12874 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12879 =
                         let uu___311_12880 = y1  in
                         let uu____12881 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___311_12880.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___311_12880.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12881
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12879
                   | uu____12884 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___317_12898 = env  in
      let uu____12899 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___317_12898.solver);
        range = (uu___317_12898.range);
        curmodule = (uu___317_12898.curmodule);
        gamma = uu____12899;
        gamma_sig = (uu___317_12898.gamma_sig);
        gamma_cache = (uu___317_12898.gamma_cache);
        modules = (uu___317_12898.modules);
        expected_typ = (uu___317_12898.expected_typ);
        sigtab = (uu___317_12898.sigtab);
        attrtab = (uu___317_12898.attrtab);
        is_pattern = (uu___317_12898.is_pattern);
        instantiate_imp = (uu___317_12898.instantiate_imp);
        effects = (uu___317_12898.effects);
        generalize = (uu___317_12898.generalize);
        letrecs = (uu___317_12898.letrecs);
        top_level = (uu___317_12898.top_level);
        check_uvars = (uu___317_12898.check_uvars);
        use_eq = (uu___317_12898.use_eq);
        is_iface = (uu___317_12898.is_iface);
        admit = (uu___317_12898.admit);
        lax = (uu___317_12898.lax);
        lax_universes = (uu___317_12898.lax_universes);
        phase1 = (uu___317_12898.phase1);
        failhard = (uu___317_12898.failhard);
        nosynth = (uu___317_12898.nosynth);
        uvar_subtyping = (uu___317_12898.uvar_subtyping);
        tc_term = (uu___317_12898.tc_term);
        type_of = (uu___317_12898.type_of);
        universe_of = (uu___317_12898.universe_of);
        check_type_of = (uu___317_12898.check_type_of);
        use_bv_sorts = (uu___317_12898.use_bv_sorts);
        qtbl_name_and_index = (uu___317_12898.qtbl_name_and_index);
        normalized_eff_names = (uu___317_12898.normalized_eff_names);
        fv_delta_depths = (uu___317_12898.fv_delta_depths);
        proof_ns = (uu___317_12898.proof_ns);
        synth_hook = (uu___317_12898.synth_hook);
        try_solve_implicits_hook = (uu___317_12898.try_solve_implicits_hook);
        splice = (uu___317_12898.splice);
        postprocess = (uu___317_12898.postprocess);
        is_native_tactic = (uu___317_12898.is_native_tactic);
        identifier_info = (uu___317_12898.identifier_info);
        tc_hooks = (uu___317_12898.tc_hooks);
        dsenv = (uu___317_12898.dsenv);
        nbe = (uu___317_12898.nbe);
        strict_args_tab = (uu___317_12898.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12907  -> fun uu____12908  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___324_12930 = env  in
      {
        solver = (uu___324_12930.solver);
        range = (uu___324_12930.range);
        curmodule = (uu___324_12930.curmodule);
        gamma = (uu___324_12930.gamma);
        gamma_sig = (uu___324_12930.gamma_sig);
        gamma_cache = (uu___324_12930.gamma_cache);
        modules = (uu___324_12930.modules);
        expected_typ = (uu___324_12930.expected_typ);
        sigtab = (uu___324_12930.sigtab);
        attrtab = (uu___324_12930.attrtab);
        is_pattern = (uu___324_12930.is_pattern);
        instantiate_imp = (uu___324_12930.instantiate_imp);
        effects = (uu___324_12930.effects);
        generalize = (uu___324_12930.generalize);
        letrecs = (uu___324_12930.letrecs);
        top_level = (uu___324_12930.top_level);
        check_uvars = (uu___324_12930.check_uvars);
        use_eq = (uu___324_12930.use_eq);
        is_iface = (uu___324_12930.is_iface);
        admit = (uu___324_12930.admit);
        lax = (uu___324_12930.lax);
        lax_universes = (uu___324_12930.lax_universes);
        phase1 = (uu___324_12930.phase1);
        failhard = (uu___324_12930.failhard);
        nosynth = (uu___324_12930.nosynth);
        uvar_subtyping = (uu___324_12930.uvar_subtyping);
        tc_term = (uu___324_12930.tc_term);
        type_of = (uu___324_12930.type_of);
        universe_of = (uu___324_12930.universe_of);
        check_type_of = (uu___324_12930.check_type_of);
        use_bv_sorts = (uu___324_12930.use_bv_sorts);
        qtbl_name_and_index = (uu___324_12930.qtbl_name_and_index);
        normalized_eff_names = (uu___324_12930.normalized_eff_names);
        fv_delta_depths = (uu___324_12930.fv_delta_depths);
        proof_ns = (uu___324_12930.proof_ns);
        synth_hook = (uu___324_12930.synth_hook);
        try_solve_implicits_hook = (uu___324_12930.try_solve_implicits_hook);
        splice = (uu___324_12930.splice);
        postprocess = (uu___324_12930.postprocess);
        is_native_tactic = (uu___324_12930.is_native_tactic);
        identifier_info = (uu___324_12930.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___324_12930.dsenv);
        nbe = (uu___324_12930.nbe);
        strict_args_tab = (uu___324_12930.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___328_12942 = e  in
      let uu____12943 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___328_12942.solver);
        range = (uu___328_12942.range);
        curmodule = (uu___328_12942.curmodule);
        gamma = (uu___328_12942.gamma);
        gamma_sig = (uu___328_12942.gamma_sig);
        gamma_cache = (uu___328_12942.gamma_cache);
        modules = (uu___328_12942.modules);
        expected_typ = (uu___328_12942.expected_typ);
        sigtab = (uu___328_12942.sigtab);
        attrtab = (uu___328_12942.attrtab);
        is_pattern = (uu___328_12942.is_pattern);
        instantiate_imp = (uu___328_12942.instantiate_imp);
        effects = (uu___328_12942.effects);
        generalize = (uu___328_12942.generalize);
        letrecs = (uu___328_12942.letrecs);
        top_level = (uu___328_12942.top_level);
        check_uvars = (uu___328_12942.check_uvars);
        use_eq = (uu___328_12942.use_eq);
        is_iface = (uu___328_12942.is_iface);
        admit = (uu___328_12942.admit);
        lax = (uu___328_12942.lax);
        lax_universes = (uu___328_12942.lax_universes);
        phase1 = (uu___328_12942.phase1);
        failhard = (uu___328_12942.failhard);
        nosynth = (uu___328_12942.nosynth);
        uvar_subtyping = (uu___328_12942.uvar_subtyping);
        tc_term = (uu___328_12942.tc_term);
        type_of = (uu___328_12942.type_of);
        universe_of = (uu___328_12942.universe_of);
        check_type_of = (uu___328_12942.check_type_of);
        use_bv_sorts = (uu___328_12942.use_bv_sorts);
        qtbl_name_and_index = (uu___328_12942.qtbl_name_and_index);
        normalized_eff_names = (uu___328_12942.normalized_eff_names);
        fv_delta_depths = (uu___328_12942.fv_delta_depths);
        proof_ns = (uu___328_12942.proof_ns);
        synth_hook = (uu___328_12942.synth_hook);
        try_solve_implicits_hook = (uu___328_12942.try_solve_implicits_hook);
        splice = (uu___328_12942.splice);
        postprocess = (uu___328_12942.postprocess);
        is_native_tactic = (uu___328_12942.is_native_tactic);
        identifier_info = (uu___328_12942.identifier_info);
        tc_hooks = (uu___328_12942.tc_hooks);
        dsenv = uu____12943;
        nbe = (uu___328_12942.nbe);
        strict_args_tab = (uu___328_12942.strict_args_tab)
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
      | (NoDelta ,uu____12972) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12975,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12977,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12980 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12994 . unit -> 'Auu____12994 FStar_Util.smap =
  fun uu____13001  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13007 . unit -> 'Auu____13007 FStar_Util.smap =
  fun uu____13014  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13152 = new_gamma_cache ()  in
                  let uu____13155 = new_sigtab ()  in
                  let uu____13158 = new_sigtab ()  in
                  let uu____13165 =
                    let uu____13180 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13180, FStar_Pervasives_Native.None)  in
                  let uu____13201 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13205 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13209 = FStar_Options.using_facts_from ()  in
                  let uu____13210 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13213 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13214 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13152;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13155;
                    attrtab = uu____13158;
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
                    qtbl_name_and_index = uu____13165;
                    normalized_eff_names = uu____13201;
                    fv_delta_depths = uu____13205;
                    proof_ns = uu____13209;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    try_solve_implicits_hook =
                      (fun e  ->
                         fun tau  ->
                           fun imps  -> failwith "no implicit hook available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____13296  -> false);
                    identifier_info = uu____13210;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13213;
                    nbe = nbe1;
                    strict_args_tab = uu____13214
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
  fun uu____13375  ->
    let uu____13376 = FStar_ST.op_Bang query_indices  in
    match uu____13376 with
    | [] -> failwith "Empty query indices!"
    | uu____13431 ->
        let uu____13441 =
          let uu____13451 =
            let uu____13459 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13459  in
          let uu____13513 = FStar_ST.op_Bang query_indices  in uu____13451 ::
            uu____13513
           in
        FStar_ST.op_Colon_Equals query_indices uu____13441
  
let (pop_query_indices : unit -> unit) =
  fun uu____13609  ->
    let uu____13610 = FStar_ST.op_Bang query_indices  in
    match uu____13610 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13737  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13774  ->
    match uu____13774 with
    | (l,n1) ->
        let uu____13784 = FStar_ST.op_Bang query_indices  in
        (match uu____13784 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13906 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13929  ->
    let uu____13930 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13930
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13998 =
       let uu____14001 = FStar_ST.op_Bang stack  in env :: uu____14001  in
     FStar_ST.op_Colon_Equals stack uu____13998);
    (let uu___399_14050 = env  in
     let uu____14051 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14054 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14057 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14064 =
       let uu____14079 =
         let uu____14083 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14083  in
       let uu____14115 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14079, uu____14115)  in
     let uu____14164 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14167 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14170 =
       let uu____14173 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14173  in
     let uu____14193 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___399_14050.solver);
       range = (uu___399_14050.range);
       curmodule = (uu___399_14050.curmodule);
       gamma = (uu___399_14050.gamma);
       gamma_sig = (uu___399_14050.gamma_sig);
       gamma_cache = uu____14051;
       modules = (uu___399_14050.modules);
       expected_typ = (uu___399_14050.expected_typ);
       sigtab = uu____14054;
       attrtab = uu____14057;
       is_pattern = (uu___399_14050.is_pattern);
       instantiate_imp = (uu___399_14050.instantiate_imp);
       effects = (uu___399_14050.effects);
       generalize = (uu___399_14050.generalize);
       letrecs = (uu___399_14050.letrecs);
       top_level = (uu___399_14050.top_level);
       check_uvars = (uu___399_14050.check_uvars);
       use_eq = (uu___399_14050.use_eq);
       is_iface = (uu___399_14050.is_iface);
       admit = (uu___399_14050.admit);
       lax = (uu___399_14050.lax);
       lax_universes = (uu___399_14050.lax_universes);
       phase1 = (uu___399_14050.phase1);
       failhard = (uu___399_14050.failhard);
       nosynth = (uu___399_14050.nosynth);
       uvar_subtyping = (uu___399_14050.uvar_subtyping);
       tc_term = (uu___399_14050.tc_term);
       type_of = (uu___399_14050.type_of);
       universe_of = (uu___399_14050.universe_of);
       check_type_of = (uu___399_14050.check_type_of);
       use_bv_sorts = (uu___399_14050.use_bv_sorts);
       qtbl_name_and_index = uu____14064;
       normalized_eff_names = uu____14164;
       fv_delta_depths = uu____14167;
       proof_ns = (uu___399_14050.proof_ns);
       synth_hook = (uu___399_14050.synth_hook);
       try_solve_implicits_hook = (uu___399_14050.try_solve_implicits_hook);
       splice = (uu___399_14050.splice);
       postprocess = (uu___399_14050.postprocess);
       is_native_tactic = (uu___399_14050.is_native_tactic);
       identifier_info = uu____14170;
       tc_hooks = (uu___399_14050.tc_hooks);
       dsenv = (uu___399_14050.dsenv);
       nbe = (uu___399_14050.nbe);
       strict_args_tab = uu____14193
     })
  
let (pop_stack : unit -> env) =
  fun uu____14211  ->
    let uu____14212 = FStar_ST.op_Bang stack  in
    match uu____14212 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14266 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14356  ->
           let uu____14357 = snapshot_stack env  in
           match uu____14357 with
           | (stack_depth,env1) ->
               let uu____14391 = snapshot_query_indices ()  in
               (match uu____14391 with
                | (query_indices_depth,()) ->
                    let uu____14424 = (env1.solver).snapshot msg  in
                    (match uu____14424 with
                     | (solver_depth,()) ->
                         let uu____14481 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14481 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___424_14548 = env1  in
                                 {
                                   solver = (uu___424_14548.solver);
                                   range = (uu___424_14548.range);
                                   curmodule = (uu___424_14548.curmodule);
                                   gamma = (uu___424_14548.gamma);
                                   gamma_sig = (uu___424_14548.gamma_sig);
                                   gamma_cache = (uu___424_14548.gamma_cache);
                                   modules = (uu___424_14548.modules);
                                   expected_typ =
                                     (uu___424_14548.expected_typ);
                                   sigtab = (uu___424_14548.sigtab);
                                   attrtab = (uu___424_14548.attrtab);
                                   is_pattern = (uu___424_14548.is_pattern);
                                   instantiate_imp =
                                     (uu___424_14548.instantiate_imp);
                                   effects = (uu___424_14548.effects);
                                   generalize = (uu___424_14548.generalize);
                                   letrecs = (uu___424_14548.letrecs);
                                   top_level = (uu___424_14548.top_level);
                                   check_uvars = (uu___424_14548.check_uvars);
                                   use_eq = (uu___424_14548.use_eq);
                                   is_iface = (uu___424_14548.is_iface);
                                   admit = (uu___424_14548.admit);
                                   lax = (uu___424_14548.lax);
                                   lax_universes =
                                     (uu___424_14548.lax_universes);
                                   phase1 = (uu___424_14548.phase1);
                                   failhard = (uu___424_14548.failhard);
                                   nosynth = (uu___424_14548.nosynth);
                                   uvar_subtyping =
                                     (uu___424_14548.uvar_subtyping);
                                   tc_term = (uu___424_14548.tc_term);
                                   type_of = (uu___424_14548.type_of);
                                   universe_of = (uu___424_14548.universe_of);
                                   check_type_of =
                                     (uu___424_14548.check_type_of);
                                   use_bv_sorts =
                                     (uu___424_14548.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___424_14548.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___424_14548.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___424_14548.fv_delta_depths);
                                   proof_ns = (uu___424_14548.proof_ns);
                                   synth_hook = (uu___424_14548.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___424_14548.try_solve_implicits_hook);
                                   splice = (uu___424_14548.splice);
                                   postprocess = (uu___424_14548.postprocess);
                                   is_native_tactic =
                                     (uu___424_14548.is_native_tactic);
                                   identifier_info =
                                     (uu___424_14548.identifier_info);
                                   tc_hooks = (uu___424_14548.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___424_14548.nbe);
                                   strict_args_tab =
                                     (uu___424_14548.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14582  ->
             let uu____14583 =
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
             match uu____14583 with
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
                             ((let uu____14763 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14763
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14779 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14779
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14811,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14853 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14883  ->
                  match uu____14883 with
                  | (m,uu____14891) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14853 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___469_14906 = env  in
               {
                 solver = (uu___469_14906.solver);
                 range = (uu___469_14906.range);
                 curmodule = (uu___469_14906.curmodule);
                 gamma = (uu___469_14906.gamma);
                 gamma_sig = (uu___469_14906.gamma_sig);
                 gamma_cache = (uu___469_14906.gamma_cache);
                 modules = (uu___469_14906.modules);
                 expected_typ = (uu___469_14906.expected_typ);
                 sigtab = (uu___469_14906.sigtab);
                 attrtab = (uu___469_14906.attrtab);
                 is_pattern = (uu___469_14906.is_pattern);
                 instantiate_imp = (uu___469_14906.instantiate_imp);
                 effects = (uu___469_14906.effects);
                 generalize = (uu___469_14906.generalize);
                 letrecs = (uu___469_14906.letrecs);
                 top_level = (uu___469_14906.top_level);
                 check_uvars = (uu___469_14906.check_uvars);
                 use_eq = (uu___469_14906.use_eq);
                 is_iface = (uu___469_14906.is_iface);
                 admit = (uu___469_14906.admit);
                 lax = (uu___469_14906.lax);
                 lax_universes = (uu___469_14906.lax_universes);
                 phase1 = (uu___469_14906.phase1);
                 failhard = (uu___469_14906.failhard);
                 nosynth = (uu___469_14906.nosynth);
                 uvar_subtyping = (uu___469_14906.uvar_subtyping);
                 tc_term = (uu___469_14906.tc_term);
                 type_of = (uu___469_14906.type_of);
                 universe_of = (uu___469_14906.universe_of);
                 check_type_of = (uu___469_14906.check_type_of);
                 use_bv_sorts = (uu___469_14906.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___469_14906.normalized_eff_names);
                 fv_delta_depths = (uu___469_14906.fv_delta_depths);
                 proof_ns = (uu___469_14906.proof_ns);
                 synth_hook = (uu___469_14906.synth_hook);
                 try_solve_implicits_hook =
                   (uu___469_14906.try_solve_implicits_hook);
                 splice = (uu___469_14906.splice);
                 postprocess = (uu___469_14906.postprocess);
                 is_native_tactic = (uu___469_14906.is_native_tactic);
                 identifier_info = (uu___469_14906.identifier_info);
                 tc_hooks = (uu___469_14906.tc_hooks);
                 dsenv = (uu___469_14906.dsenv);
                 nbe = (uu___469_14906.nbe);
                 strict_args_tab = (uu___469_14906.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14923,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___478_14939 = env  in
               {
                 solver = (uu___478_14939.solver);
                 range = (uu___478_14939.range);
                 curmodule = (uu___478_14939.curmodule);
                 gamma = (uu___478_14939.gamma);
                 gamma_sig = (uu___478_14939.gamma_sig);
                 gamma_cache = (uu___478_14939.gamma_cache);
                 modules = (uu___478_14939.modules);
                 expected_typ = (uu___478_14939.expected_typ);
                 sigtab = (uu___478_14939.sigtab);
                 attrtab = (uu___478_14939.attrtab);
                 is_pattern = (uu___478_14939.is_pattern);
                 instantiate_imp = (uu___478_14939.instantiate_imp);
                 effects = (uu___478_14939.effects);
                 generalize = (uu___478_14939.generalize);
                 letrecs = (uu___478_14939.letrecs);
                 top_level = (uu___478_14939.top_level);
                 check_uvars = (uu___478_14939.check_uvars);
                 use_eq = (uu___478_14939.use_eq);
                 is_iface = (uu___478_14939.is_iface);
                 admit = (uu___478_14939.admit);
                 lax = (uu___478_14939.lax);
                 lax_universes = (uu___478_14939.lax_universes);
                 phase1 = (uu___478_14939.phase1);
                 failhard = (uu___478_14939.failhard);
                 nosynth = (uu___478_14939.nosynth);
                 uvar_subtyping = (uu___478_14939.uvar_subtyping);
                 tc_term = (uu___478_14939.tc_term);
                 type_of = (uu___478_14939.type_of);
                 universe_of = (uu___478_14939.universe_of);
                 check_type_of = (uu___478_14939.check_type_of);
                 use_bv_sorts = (uu___478_14939.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___478_14939.normalized_eff_names);
                 fv_delta_depths = (uu___478_14939.fv_delta_depths);
                 proof_ns = (uu___478_14939.proof_ns);
                 synth_hook = (uu___478_14939.synth_hook);
                 try_solve_implicits_hook =
                   (uu___478_14939.try_solve_implicits_hook);
                 splice = (uu___478_14939.splice);
                 postprocess = (uu___478_14939.postprocess);
                 is_native_tactic = (uu___478_14939.is_native_tactic);
                 identifier_info = (uu___478_14939.identifier_info);
                 tc_hooks = (uu___478_14939.tc_hooks);
                 dsenv = (uu___478_14939.dsenv);
                 nbe = (uu___478_14939.nbe);
                 strict_args_tab = (uu___478_14939.strict_args_tab)
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
        (let uu___485_14982 = e  in
         {
           solver = (uu___485_14982.solver);
           range = r;
           curmodule = (uu___485_14982.curmodule);
           gamma = (uu___485_14982.gamma);
           gamma_sig = (uu___485_14982.gamma_sig);
           gamma_cache = (uu___485_14982.gamma_cache);
           modules = (uu___485_14982.modules);
           expected_typ = (uu___485_14982.expected_typ);
           sigtab = (uu___485_14982.sigtab);
           attrtab = (uu___485_14982.attrtab);
           is_pattern = (uu___485_14982.is_pattern);
           instantiate_imp = (uu___485_14982.instantiate_imp);
           effects = (uu___485_14982.effects);
           generalize = (uu___485_14982.generalize);
           letrecs = (uu___485_14982.letrecs);
           top_level = (uu___485_14982.top_level);
           check_uvars = (uu___485_14982.check_uvars);
           use_eq = (uu___485_14982.use_eq);
           is_iface = (uu___485_14982.is_iface);
           admit = (uu___485_14982.admit);
           lax = (uu___485_14982.lax);
           lax_universes = (uu___485_14982.lax_universes);
           phase1 = (uu___485_14982.phase1);
           failhard = (uu___485_14982.failhard);
           nosynth = (uu___485_14982.nosynth);
           uvar_subtyping = (uu___485_14982.uvar_subtyping);
           tc_term = (uu___485_14982.tc_term);
           type_of = (uu___485_14982.type_of);
           universe_of = (uu___485_14982.universe_of);
           check_type_of = (uu___485_14982.check_type_of);
           use_bv_sorts = (uu___485_14982.use_bv_sorts);
           qtbl_name_and_index = (uu___485_14982.qtbl_name_and_index);
           normalized_eff_names = (uu___485_14982.normalized_eff_names);
           fv_delta_depths = (uu___485_14982.fv_delta_depths);
           proof_ns = (uu___485_14982.proof_ns);
           synth_hook = (uu___485_14982.synth_hook);
           try_solve_implicits_hook =
             (uu___485_14982.try_solve_implicits_hook);
           splice = (uu___485_14982.splice);
           postprocess = (uu___485_14982.postprocess);
           is_native_tactic = (uu___485_14982.is_native_tactic);
           identifier_info = (uu___485_14982.identifier_info);
           tc_hooks = (uu___485_14982.tc_hooks);
           dsenv = (uu___485_14982.dsenv);
           nbe = (uu___485_14982.nbe);
           strict_args_tab = (uu___485_14982.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15002 =
        let uu____15003 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15003 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15002
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15058 =
          let uu____15059 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15059 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15058
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15114 =
          let uu____15115 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15115 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15114
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15170 =
        let uu____15171 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15171 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15170
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___502_15235 = env  in
      {
        solver = (uu___502_15235.solver);
        range = (uu___502_15235.range);
        curmodule = lid;
        gamma = (uu___502_15235.gamma);
        gamma_sig = (uu___502_15235.gamma_sig);
        gamma_cache = (uu___502_15235.gamma_cache);
        modules = (uu___502_15235.modules);
        expected_typ = (uu___502_15235.expected_typ);
        sigtab = (uu___502_15235.sigtab);
        attrtab = (uu___502_15235.attrtab);
        is_pattern = (uu___502_15235.is_pattern);
        instantiate_imp = (uu___502_15235.instantiate_imp);
        effects = (uu___502_15235.effects);
        generalize = (uu___502_15235.generalize);
        letrecs = (uu___502_15235.letrecs);
        top_level = (uu___502_15235.top_level);
        check_uvars = (uu___502_15235.check_uvars);
        use_eq = (uu___502_15235.use_eq);
        is_iface = (uu___502_15235.is_iface);
        admit = (uu___502_15235.admit);
        lax = (uu___502_15235.lax);
        lax_universes = (uu___502_15235.lax_universes);
        phase1 = (uu___502_15235.phase1);
        failhard = (uu___502_15235.failhard);
        nosynth = (uu___502_15235.nosynth);
        uvar_subtyping = (uu___502_15235.uvar_subtyping);
        tc_term = (uu___502_15235.tc_term);
        type_of = (uu___502_15235.type_of);
        universe_of = (uu___502_15235.universe_of);
        check_type_of = (uu___502_15235.check_type_of);
        use_bv_sorts = (uu___502_15235.use_bv_sorts);
        qtbl_name_and_index = (uu___502_15235.qtbl_name_and_index);
        normalized_eff_names = (uu___502_15235.normalized_eff_names);
        fv_delta_depths = (uu___502_15235.fv_delta_depths);
        proof_ns = (uu___502_15235.proof_ns);
        synth_hook = (uu___502_15235.synth_hook);
        try_solve_implicits_hook = (uu___502_15235.try_solve_implicits_hook);
        splice = (uu___502_15235.splice);
        postprocess = (uu___502_15235.postprocess);
        is_native_tactic = (uu___502_15235.is_native_tactic);
        identifier_info = (uu___502_15235.identifier_info);
        tc_hooks = (uu___502_15235.tc_hooks);
        dsenv = (uu___502_15235.dsenv);
        nbe = (uu___502_15235.nbe);
        strict_args_tab = (uu___502_15235.strict_args_tab)
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
      let uu____15266 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15266
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15279 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15279)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15294 =
      let uu____15296 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15296  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15294)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15305  ->
    let uu____15306 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15306
  
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
      | ((formals,t),uu____15406) ->
          let vs = mk_univ_subst formals us  in
          let uu____15430 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15430)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15447  ->
    match uu___1_15447 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15473  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15493 = inst_tscheme t  in
      match uu____15493 with
      | (us,t1) ->
          let uu____15504 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15504)
  
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
          let uu____15529 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15531 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15529 uu____15531
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
        fun uu____15558  ->
          match uu____15558 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15572 =
                    let uu____15574 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15578 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15582 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15584 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15574 uu____15578 uu____15582 uu____15584
                     in
                  failwith uu____15572)
               else ();
               (let uu____15589 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15589))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15607 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15618 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15629 -> false
  
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
             | ([],uu____15677) -> Maybe
             | (uu____15684,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15704 -> No  in
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
          let uu____15798 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15798 with
          | FStar_Pervasives_Native.None  ->
              let uu____15821 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15865  ->
                     match uu___2_15865 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15904 = FStar_Ident.lid_equals lid l  in
                         if uu____15904
                         then
                           let uu____15927 =
                             let uu____15946 =
                               let uu____15961 = inst_tscheme t  in
                               FStar_Util.Inl uu____15961  in
                             let uu____15976 = FStar_Ident.range_of_lid l  in
                             (uu____15946, uu____15976)  in
                           FStar_Pervasives_Native.Some uu____15927
                         else FStar_Pervasives_Native.None
                     | uu____16029 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15821
                (fun uu____16067  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16076  ->
                        match uu___3_16076 with
                        | (uu____16079,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16081);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16082;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16083;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16084;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16085;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16105 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16105
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
                                  uu____16157 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16164 -> cache t  in
                            let uu____16165 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16165 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16171 =
                                   let uu____16172 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16172)
                                    in
                                 maybe_cache uu____16171)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16243 = find_in_sigtab env lid  in
         match uu____16243 with
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
      let uu____16324 = lookup_qname env lid  in
      match uu____16324 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16345,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16459 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16459 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16504 =
          let uu____16507 = lookup_attr env1 attr  in se1 :: uu____16507  in
        FStar_Util.smap_add (attrtab env1) attr uu____16504  in
      FStar_List.iter
        (fun attr  ->
           let uu____16517 =
             let uu____16518 = FStar_Syntax_Subst.compress attr  in
             uu____16518.FStar_Syntax_Syntax.n  in
           match uu____16517 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16522 =
                 let uu____16524 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16524.FStar_Ident.str  in
               add_one1 env se uu____16522
           | uu____16525 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16548) ->
          add_sigelts env ses
      | uu____16557 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se)

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
        (fun uu___4_16595  ->
           match uu___4_16595 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16613 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16675,lb::[]),uu____16677) ->
            let uu____16686 =
              let uu____16695 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16704 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16695, uu____16704)  in
            FStar_Pervasives_Native.Some uu____16686
        | FStar_Syntax_Syntax.Sig_let ((uu____16717,lbs),uu____16719) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16751 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16764 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16764
                     then
                       let uu____16777 =
                         let uu____16786 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16795 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16786, uu____16795)  in
                       FStar_Pervasives_Native.Some uu____16777
                     else FStar_Pervasives_Native.None)
        | uu____16818 -> FStar_Pervasives_Native.None
  
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
                    let uu____16910 =
                      let uu____16912 =
                        let uu____16914 =
                          let uu____16916 =
                            let uu____16918 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16924 =
                              let uu____16926 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16926  in
                            Prims.op_Hat uu____16918 uu____16924  in
                          Prims.op_Hat ", expected " uu____16916  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16914
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16912
                       in
                    failwith uu____16910
                  else ());
             (let uu____16933 =
                let uu____16942 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16942, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16933))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16962,uu____16963) ->
            let uu____16968 =
              let uu____16977 =
                let uu____16982 =
                  let uu____16983 =
                    let uu____16986 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16986  in
                  (us, uu____16983)  in
                inst_ts us_opt uu____16982  in
              (uu____16977, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16968
        | uu____17005 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17094 =
          match uu____17094 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17190,uvs,t,uu____17193,uu____17194,uu____17195);
                      FStar_Syntax_Syntax.sigrng = uu____17196;
                      FStar_Syntax_Syntax.sigquals = uu____17197;
                      FStar_Syntax_Syntax.sigmeta = uu____17198;
                      FStar_Syntax_Syntax.sigattrs = uu____17199;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17222 =
                     let uu____17231 = inst_tscheme1 (uvs, t)  in
                     (uu____17231, rng)  in
                   FStar_Pervasives_Native.Some uu____17222
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17255;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17257;
                      FStar_Syntax_Syntax.sigattrs = uu____17258;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17275 =
                     let uu____17277 = in_cur_mod env l  in uu____17277 = Yes
                      in
                   if uu____17275
                   then
                     let uu____17289 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17289
                      then
                        let uu____17305 =
                          let uu____17314 = inst_tscheme1 (uvs, t)  in
                          (uu____17314, rng)  in
                        FStar_Pervasives_Native.Some uu____17305
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17347 =
                        let uu____17356 = inst_tscheme1 (uvs, t)  in
                        (uu____17356, rng)  in
                      FStar_Pervasives_Native.Some uu____17347)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17381,uu____17382);
                      FStar_Syntax_Syntax.sigrng = uu____17383;
                      FStar_Syntax_Syntax.sigquals = uu____17384;
                      FStar_Syntax_Syntax.sigmeta = uu____17385;
                      FStar_Syntax_Syntax.sigattrs = uu____17386;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17427 =
                          let uu____17436 = inst_tscheme1 (uvs, k)  in
                          (uu____17436, rng)  in
                        FStar_Pervasives_Native.Some uu____17427
                    | uu____17457 ->
                        let uu____17458 =
                          let uu____17467 =
                            let uu____17472 =
                              let uu____17473 =
                                let uu____17476 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17476
                                 in
                              (uvs, uu____17473)  in
                            inst_tscheme1 uu____17472  in
                          (uu____17467, rng)  in
                        FStar_Pervasives_Native.Some uu____17458)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17499,uu____17500);
                      FStar_Syntax_Syntax.sigrng = uu____17501;
                      FStar_Syntax_Syntax.sigquals = uu____17502;
                      FStar_Syntax_Syntax.sigmeta = uu____17503;
                      FStar_Syntax_Syntax.sigattrs = uu____17504;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17546 =
                          let uu____17555 = inst_tscheme_with (uvs, k) us  in
                          (uu____17555, rng)  in
                        FStar_Pervasives_Native.Some uu____17546
                    | uu____17576 ->
                        let uu____17577 =
                          let uu____17586 =
                            let uu____17591 =
                              let uu____17592 =
                                let uu____17595 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17595
                                 in
                              (uvs, uu____17592)  in
                            inst_tscheme_with uu____17591 us  in
                          (uu____17586, rng)  in
                        FStar_Pervasives_Native.Some uu____17577)
               | FStar_Util.Inr se ->
                   let uu____17631 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17652;
                          FStar_Syntax_Syntax.sigrng = uu____17653;
                          FStar_Syntax_Syntax.sigquals = uu____17654;
                          FStar_Syntax_Syntax.sigmeta = uu____17655;
                          FStar_Syntax_Syntax.sigattrs = uu____17656;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17671 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17631
                     (FStar_Util.map_option
                        (fun uu____17719  ->
                           match uu____17719 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17750 =
          let uu____17761 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17761 mapper  in
        match uu____17750 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17835 =
              let uu____17846 =
                let uu____17853 =
                  let uu___833_17856 = t  in
                  let uu____17857 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___833_17856.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17857;
                    FStar_Syntax_Syntax.vars =
                      (uu___833_17856.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17853)  in
              (uu____17846, r)  in
            FStar_Pervasives_Native.Some uu____17835
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17906 = lookup_qname env l  in
      match uu____17906 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17927 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17981 = try_lookup_bv env bv  in
      match uu____17981 with
      | FStar_Pervasives_Native.None  ->
          let uu____17996 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17996 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18012 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18013 =
            let uu____18014 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18014  in
          (uu____18012, uu____18013)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18036 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18036 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18102 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18102  in
          let uu____18103 =
            let uu____18112 =
              let uu____18117 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18117)  in
            (uu____18112, r1)  in
          FStar_Pervasives_Native.Some uu____18103
  
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
        let uu____18152 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18152 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18185,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18210 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18210  in
            let uu____18211 =
              let uu____18216 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18216, r1)  in
            FStar_Pervasives_Native.Some uu____18211
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18240 = try_lookup_lid env l  in
      match uu____18240 with
      | FStar_Pervasives_Native.None  ->
          let uu____18267 = name_not_found l  in
          let uu____18273 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18267 uu____18273
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18316  ->
              match uu___5_18316 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18320 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18341 = lookup_qname env lid  in
      match uu____18341 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18350,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18353;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18355;
              FStar_Syntax_Syntax.sigattrs = uu____18356;_},FStar_Pervasives_Native.None
            ),uu____18357)
          ->
          let uu____18406 =
            let uu____18413 =
              let uu____18414 =
                let uu____18417 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18417 t  in
              (uvs, uu____18414)  in
            (uu____18413, q)  in
          FStar_Pervasives_Native.Some uu____18406
      | uu____18430 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18452 = lookup_qname env lid  in
      match uu____18452 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18457,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18460;
              FStar_Syntax_Syntax.sigquals = uu____18461;
              FStar_Syntax_Syntax.sigmeta = uu____18462;
              FStar_Syntax_Syntax.sigattrs = uu____18463;_},FStar_Pervasives_Native.None
            ),uu____18464)
          ->
          let uu____18513 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18513 (uvs, t)
      | uu____18518 ->
          let uu____18519 = name_not_found lid  in
          let uu____18525 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18519 uu____18525
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18545 = lookup_qname env lid  in
      match uu____18545 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18550,uvs,t,uu____18553,uu____18554,uu____18555);
              FStar_Syntax_Syntax.sigrng = uu____18556;
              FStar_Syntax_Syntax.sigquals = uu____18557;
              FStar_Syntax_Syntax.sigmeta = uu____18558;
              FStar_Syntax_Syntax.sigattrs = uu____18559;_},FStar_Pervasives_Native.None
            ),uu____18560)
          ->
          let uu____18615 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18615 (uvs, t)
      | uu____18620 ->
          let uu____18621 = name_not_found lid  in
          let uu____18627 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18621 uu____18627
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18650 = lookup_qname env lid  in
      match uu____18650 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18658,uu____18659,uu____18660,uu____18661,uu____18662,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18664;
              FStar_Syntax_Syntax.sigquals = uu____18665;
              FStar_Syntax_Syntax.sigmeta = uu____18666;
              FStar_Syntax_Syntax.sigattrs = uu____18667;_},uu____18668),uu____18669)
          -> (true, dcs)
      | uu____18732 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18748 = lookup_qname env lid  in
      match uu____18748 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18749,uu____18750,uu____18751,l,uu____18753,uu____18754);
              FStar_Syntax_Syntax.sigrng = uu____18755;
              FStar_Syntax_Syntax.sigquals = uu____18756;
              FStar_Syntax_Syntax.sigmeta = uu____18757;
              FStar_Syntax_Syntax.sigattrs = uu____18758;_},uu____18759),uu____18760)
          -> l
      | uu____18817 ->
          let uu____18818 =
            let uu____18820 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18820  in
          failwith uu____18818
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18890)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18947) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18971 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18971
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19006 -> FStar_Pervasives_Native.None)
          | uu____19015 -> FStar_Pervasives_Native.None
  
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
        let uu____19077 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19077
  
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
        let uu____19110 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19110
  
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
             (FStar_Util.Inl uu____19162,uu____19163) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19212),uu____19213) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19262 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19280 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19290 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19307 ->
                  let uu____19314 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19314
              | FStar_Syntax_Syntax.Sig_let ((uu____19315,lbs),uu____19317)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19333 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19333
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19340 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19348 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19349 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19356 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19357 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19358 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19359 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19372 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19390 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19390
           (fun d_opt  ->
              let uu____19403 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19403
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19413 =
                   let uu____19416 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19416  in
                 match uu____19413 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19417 =
                       let uu____19419 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19419
                        in
                     failwith uu____19417
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19424 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19424
                       then
                         let uu____19427 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19429 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19431 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19427 uu____19429 uu____19431
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
        (FStar_Util.Inr (se,uu____19456),uu____19457) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19506 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19528),uu____19529) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19578 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19600 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19600
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19623 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19623 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19647 =
                      let uu____19648 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19648.FStar_Syntax_Syntax.n  in
                    match uu____19647 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19653 -> false))
  
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
        let uu____19690 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19690.FStar_Ident.str  in
      let uu____19691 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19691 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19719 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19719  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____19747 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____19747)
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
      let uu____19797 = lookup_qname env ftv  in
      match uu____19797 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19801) ->
          let uu____19846 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19846 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19867,t),r) ->
               let uu____19882 =
                 let uu____19883 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19883 t  in
               FStar_Pervasives_Native.Some uu____19882)
      | uu____19884 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19896 = try_lookup_effect_lid env ftv  in
      match uu____19896 with
      | FStar_Pervasives_Native.None  ->
          let uu____19899 = name_not_found ftv  in
          let uu____19905 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19899 uu____19905
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
        let uu____19929 = lookup_qname env lid0  in
        match uu____19929 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19940);
                FStar_Syntax_Syntax.sigrng = uu____19941;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19943;
                FStar_Syntax_Syntax.sigattrs = uu____19944;_},FStar_Pervasives_Native.None
              ),uu____19945)
            ->
            let lid1 =
              let uu____19999 =
                let uu____20000 = FStar_Ident.range_of_lid lid  in
                let uu____20001 =
                  let uu____20002 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20002  in
                FStar_Range.set_use_range uu____20000 uu____20001  in
              FStar_Ident.set_lid_range lid uu____19999  in
            let uu____20003 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20009  ->
                      match uu___6_20009 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20012 -> false))
               in
            if uu____20003
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20031 =
                      let uu____20033 =
                        let uu____20035 = get_range env  in
                        FStar_Range.string_of_range uu____20035  in
                      let uu____20036 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20038 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20033 uu____20036 uu____20038
                       in
                    failwith uu____20031)
                  in
               match (binders, univs1) with
               | ([],uu____20059) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20085,uu____20086::uu____20087::uu____20088) ->
                   let uu____20109 =
                     let uu____20111 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20113 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20111 uu____20113
                      in
                   failwith uu____20109
               | uu____20124 ->
                   let uu____20139 =
                     let uu____20144 =
                       let uu____20145 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20145)  in
                     inst_tscheme_with uu____20144 insts  in
                   (match uu____20139 with
                    | (uu____20158,t) ->
                        let t1 =
                          let uu____20161 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20161 t  in
                        let uu____20162 =
                          let uu____20163 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20163.FStar_Syntax_Syntax.n  in
                        (match uu____20162 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20198 -> failwith "Impossible")))
        | uu____20206 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20230 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20230 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20243,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20250 = find1 l2  in
            (match uu____20250 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20257 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20257 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20261 = find1 l  in
            (match uu____20261 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20266 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20266
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____20287 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____20287 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____20293) ->
            FStar_List.length bs
        | uu____20332 ->
            let uu____20333 =
              let uu____20339 =
                let uu____20341 = FStar_Ident.string_of_lid name  in
                let uu____20343 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20341 uu____20343
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20339)
               in
            FStar_Errors.raise_error uu____20333 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20362 = lookup_qname env l1  in
      match uu____20362 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20365;
              FStar_Syntax_Syntax.sigrng = uu____20366;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20368;
              FStar_Syntax_Syntax.sigattrs = uu____20369;_},uu____20370),uu____20371)
          -> q
      | uu____20422 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20446 =
          let uu____20447 =
            let uu____20449 = FStar_Util.string_of_int i  in
            let uu____20451 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20449 uu____20451
             in
          failwith uu____20447  in
        let uu____20454 = lookup_datacon env lid  in
        match uu____20454 with
        | (uu____20459,t) ->
            let uu____20461 =
              let uu____20462 = FStar_Syntax_Subst.compress t  in
              uu____20462.FStar_Syntax_Syntax.n  in
            (match uu____20461 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20466) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20510 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20510
                      FStar_Pervasives_Native.fst)
             | uu____20521 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20535 = lookup_qname env l  in
      match uu____20535 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20537,uu____20538,uu____20539);
              FStar_Syntax_Syntax.sigrng = uu____20540;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20542;
              FStar_Syntax_Syntax.sigattrs = uu____20543;_},uu____20544),uu____20545)
          ->
          FStar_Util.for_some
            (fun uu___7_20598  ->
               match uu___7_20598 with
               | FStar_Syntax_Syntax.Projector uu____20600 -> true
               | uu____20606 -> false) quals
      | uu____20608 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20622 = lookup_qname env lid  in
      match uu____20622 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20624,uu____20625,uu____20626,uu____20627,uu____20628,uu____20629);
              FStar_Syntax_Syntax.sigrng = uu____20630;
              FStar_Syntax_Syntax.sigquals = uu____20631;
              FStar_Syntax_Syntax.sigmeta = uu____20632;
              FStar_Syntax_Syntax.sigattrs = uu____20633;_},uu____20634),uu____20635)
          -> true
      | uu____20693 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20707 = lookup_qname env lid  in
      match uu____20707 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20709,uu____20710,uu____20711,uu____20712,uu____20713,uu____20714);
              FStar_Syntax_Syntax.sigrng = uu____20715;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20717;
              FStar_Syntax_Syntax.sigattrs = uu____20718;_},uu____20719),uu____20720)
          ->
          FStar_Util.for_some
            (fun uu___8_20781  ->
               match uu___8_20781 with
               | FStar_Syntax_Syntax.RecordType uu____20783 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20793 -> true
               | uu____20803 -> false) quals
      | uu____20805 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20815,uu____20816);
            FStar_Syntax_Syntax.sigrng = uu____20817;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20819;
            FStar_Syntax_Syntax.sigattrs = uu____20820;_},uu____20821),uu____20822)
        ->
        FStar_Util.for_some
          (fun uu___9_20879  ->
             match uu___9_20879 with
             | FStar_Syntax_Syntax.Action uu____20881 -> true
             | uu____20883 -> false) quals
    | uu____20885 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20899 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20899
  
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
      let uu____20916 =
        let uu____20917 = FStar_Syntax_Util.un_uinst head1  in
        uu____20917.FStar_Syntax_Syntax.n  in
      match uu____20916 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20923 ->
               true
           | uu____20926 -> false)
      | uu____20928 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20942 = lookup_qname env l  in
      match uu____20942 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20945),uu____20946) ->
          FStar_Util.for_some
            (fun uu___10_20994  ->
               match uu___10_20994 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20997 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20999 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21075 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21093) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21111 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21119 ->
                 FStar_Pervasives_Native.Some true
             | uu____21138 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21141 =
        let uu____21145 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21145 mapper  in
      match uu____21141 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21205 = lookup_qname env lid  in
      match uu____21205 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21209,uu____21210,tps,uu____21212,uu____21213,uu____21214);
              FStar_Syntax_Syntax.sigrng = uu____21215;
              FStar_Syntax_Syntax.sigquals = uu____21216;
              FStar_Syntax_Syntax.sigmeta = uu____21217;
              FStar_Syntax_Syntax.sigattrs = uu____21218;_},uu____21219),uu____21220)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21286 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21332  ->
              match uu____21332 with
              | (d,uu____21341) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21357 = effect_decl_opt env l  in
      match uu____21357 with
      | FStar_Pervasives_Native.None  ->
          let uu____21372 = name_not_found l  in
          let uu____21378 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21372 uu____21378
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21406 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____21406
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____21415  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21433  ->
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
        let uu____21465 = FStar_Ident.lid_equals l1 l2  in
        if uu____21465
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21476 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21476
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21487 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21540  ->
                        match uu____21540 with
                        | (m1,m2,uu____21554,uu____21555,uu____21556) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21487 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21573 =
                    let uu____21579 =
                      let uu____21581 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21583 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21581
                        uu____21583
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21579)
                     in
                  FStar_Errors.raise_error uu____21573 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21593,uu____21594,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21628 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21628
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
  'Auu____21648 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21648) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21677 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21703  ->
                match uu____21703 with
                | (d,uu____21710) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21677 with
      | FStar_Pervasives_Native.None  ->
          let uu____21721 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21721
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21736 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21736 with
           | (uu____21747,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21765)::(wp,uu____21767)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21823 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
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
        | uu____21888 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21901 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21901 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21918 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21918 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21943 =
                     let uu____21949 =
                       let uu____21951 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____21959 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____21970 =
                         let uu____21972 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____21972  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21951 uu____21959 uu____21970
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21949)
                      in
                   FStar_Errors.raise_error uu____21943
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____21980 =
                     let uu____21991 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____21991 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22028  ->
                        fun uu____22029  ->
                          match (uu____22028, uu____22029) with
                          | ((x,uu____22059),(t,uu____22061)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21980
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22092 =
                     let uu___1534_22093 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1534_22093.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1534_22093.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1534_22093.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1534_22093.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22092
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22105 .
    'Auu____22105 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_res  ->
          let check_partial_application eff_name args =
            let r = get_range env  in
            let uu____22146 =
              let uu____22153 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____22153)  in
            match uu____22146 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____22177 = FStar_Ident.string_of_lid eff_name  in
                     let uu____22179 = FStar_Util.string_of_int given  in
                     let uu____22181 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____22177 uu____22179 uu____22181
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____22186 = effect_decl_opt env effect_name  in
          match uu____22186 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____22208) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22229 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr =
                     inst_effect_fun_with [u_res] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____22236 =
                       let uu____22239 = get_range env  in
                       let uu____22240 =
                         let uu____22247 =
                           let uu____22248 =
                             let uu____22265 =
                               let uu____22276 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____22276 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____22265)  in
                           FStar_Syntax_Syntax.Tm_app uu____22248  in
                         FStar_Syntax_Syntax.mk uu____22247  in
                       uu____22240 FStar_Pervasives_Native.None uu____22239
                        in
                     FStar_Pervasives_Native.Some uu____22236)))
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_res  -> effect_repr_aux false env c u_res 
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
      | uu____22412 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22427 =
        let uu____22428 = FStar_Syntax_Subst.compress t  in
        uu____22428.FStar_Syntax_Syntax.n  in
      match uu____22427 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22432,c) ->
          is_reifiable_comp env c
      | uu____22454 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22474 =
           let uu____22476 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22476  in
         if uu____22474
         then
           let uu____22479 =
             let uu____22485 =
               let uu____22487 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22487
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22485)  in
           let uu____22491 = get_range env  in
           FStar_Errors.raise_error uu____22479 uu____22491
         else ());
        (let uu____22494 = effect_repr_aux true env c u_c  in
         match uu____22494 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1602_22530 = env  in
        {
          solver = (uu___1602_22530.solver);
          range = (uu___1602_22530.range);
          curmodule = (uu___1602_22530.curmodule);
          gamma = (uu___1602_22530.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1602_22530.gamma_cache);
          modules = (uu___1602_22530.modules);
          expected_typ = (uu___1602_22530.expected_typ);
          sigtab = (uu___1602_22530.sigtab);
          attrtab = (uu___1602_22530.attrtab);
          is_pattern = (uu___1602_22530.is_pattern);
          instantiate_imp = (uu___1602_22530.instantiate_imp);
          effects = (uu___1602_22530.effects);
          generalize = (uu___1602_22530.generalize);
          letrecs = (uu___1602_22530.letrecs);
          top_level = (uu___1602_22530.top_level);
          check_uvars = (uu___1602_22530.check_uvars);
          use_eq = (uu___1602_22530.use_eq);
          is_iface = (uu___1602_22530.is_iface);
          admit = (uu___1602_22530.admit);
          lax = (uu___1602_22530.lax);
          lax_universes = (uu___1602_22530.lax_universes);
          phase1 = (uu___1602_22530.phase1);
          failhard = (uu___1602_22530.failhard);
          nosynth = (uu___1602_22530.nosynth);
          uvar_subtyping = (uu___1602_22530.uvar_subtyping);
          tc_term = (uu___1602_22530.tc_term);
          type_of = (uu___1602_22530.type_of);
          universe_of = (uu___1602_22530.universe_of);
          check_type_of = (uu___1602_22530.check_type_of);
          use_bv_sorts = (uu___1602_22530.use_bv_sorts);
          qtbl_name_and_index = (uu___1602_22530.qtbl_name_and_index);
          normalized_eff_names = (uu___1602_22530.normalized_eff_names);
          fv_delta_depths = (uu___1602_22530.fv_delta_depths);
          proof_ns = (uu___1602_22530.proof_ns);
          synth_hook = (uu___1602_22530.synth_hook);
          try_solve_implicits_hook =
            (uu___1602_22530.try_solve_implicits_hook);
          splice = (uu___1602_22530.splice);
          postprocess = (uu___1602_22530.postprocess);
          is_native_tactic = (uu___1602_22530.is_native_tactic);
          identifier_info = (uu___1602_22530.identifier_info);
          tc_hooks = (uu___1602_22530.tc_hooks);
          dsenv = (uu___1602_22530.dsenv);
          nbe = (uu___1602_22530.nbe);
          strict_args_tab = (uu___1602_22530.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      env1
  
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env  ->
    fun uu____22549  ->
      match uu____22549 with
      | (ed,quals) ->
          let effects =
            let uu___1611_22563 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1611_22563.order);
              joins = (uu___1611_22563.joins)
            }  in
          let uu___1614_22572 = env  in
          {
            solver = (uu___1614_22572.solver);
            range = (uu___1614_22572.range);
            curmodule = (uu___1614_22572.curmodule);
            gamma = (uu___1614_22572.gamma);
            gamma_sig = (uu___1614_22572.gamma_sig);
            gamma_cache = (uu___1614_22572.gamma_cache);
            modules = (uu___1614_22572.modules);
            expected_typ = (uu___1614_22572.expected_typ);
            sigtab = (uu___1614_22572.sigtab);
            attrtab = (uu___1614_22572.attrtab);
            is_pattern = (uu___1614_22572.is_pattern);
            instantiate_imp = (uu___1614_22572.instantiate_imp);
            effects;
            generalize = (uu___1614_22572.generalize);
            letrecs = (uu___1614_22572.letrecs);
            top_level = (uu___1614_22572.top_level);
            check_uvars = (uu___1614_22572.check_uvars);
            use_eq = (uu___1614_22572.use_eq);
            is_iface = (uu___1614_22572.is_iface);
            admit = (uu___1614_22572.admit);
            lax = (uu___1614_22572.lax);
            lax_universes = (uu___1614_22572.lax_universes);
            phase1 = (uu___1614_22572.phase1);
            failhard = (uu___1614_22572.failhard);
            nosynth = (uu___1614_22572.nosynth);
            uvar_subtyping = (uu___1614_22572.uvar_subtyping);
            tc_term = (uu___1614_22572.tc_term);
            type_of = (uu___1614_22572.type_of);
            universe_of = (uu___1614_22572.universe_of);
            check_type_of = (uu___1614_22572.check_type_of);
            use_bv_sorts = (uu___1614_22572.use_bv_sorts);
            qtbl_name_and_index = (uu___1614_22572.qtbl_name_and_index);
            normalized_eff_names = (uu___1614_22572.normalized_eff_names);
            fv_delta_depths = (uu___1614_22572.fv_delta_depths);
            proof_ns = (uu___1614_22572.proof_ns);
            synth_hook = (uu___1614_22572.synth_hook);
            try_solve_implicits_hook =
              (uu___1614_22572.try_solve_implicits_hook);
            splice = (uu___1614_22572.splice);
            postprocess = (uu___1614_22572.postprocess);
            is_native_tactic = (uu___1614_22572.is_native_tactic);
            identifier_info = (uu___1614_22572.identifier_info);
            tc_hooks = (uu___1614_22572.tc_hooks);
            dsenv = (uu___1614_22572.dsenv);
            nbe = (uu___1614_22572.nbe);
            strict_args_tab = (uu___1614_22572.strict_args_tab)
          }
  
let (update_effect_lattice :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sub_eff,lift_comp_t) FStar_Util.either -> env)
  =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun sub_or_lift_t  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____22633 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____22633
                  (fun uu____22654  ->
                     match uu____22654 with
                     | (c1,g1) ->
                         let uu____22665 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____22665
                           (fun uu____22686  ->
                              match uu____22686 with
                              | (c2,g2) ->
                                  let uu____22697 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____22697)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____22854 = l1 u t wp e  in
                                l2 u t FStar_Syntax_Syntax.tun uu____22854))
                | uu____22855 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_ts env1 c =
            let ct = unfold_effect_abbrev env1 c  in
            let uu____22921 =
              inst_tscheme_with lift_ts ct.FStar_Syntax_Syntax.comp_univs  in
            match uu____22921 with
            | (uu____22930,lift_t) ->
                let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
                let uu____22949 =
                  let uu____22950 =
                    let uu___1655_22951 = ct  in
                    let uu____22952 =
                      let uu____22963 =
                        let uu____22972 =
                          let uu____22973 =
                            let uu____22980 =
                              let uu____22981 =
                                let uu____22998 =
                                  let uu____23009 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ
                                     in
                                  [uu____23009; wp]  in
                                (lift_t, uu____22998)  in
                              FStar_Syntax_Syntax.Tm_app uu____22981  in
                            FStar_Syntax_Syntax.mk uu____22980  in
                          uu____22973 FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                           in
                        FStar_All.pipe_right uu____22972
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____22963]  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___1655_22951.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = tgt;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___1655_22951.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args = uu____22952;
                      FStar_Syntax_Syntax.flags =
                        (uu___1655_22951.FStar_Syntax_Syntax.flags)
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____22950  in
                (uu____22949, FStar_TypeChecker_Common.trivial_guard)
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____23114 = inst_tscheme_with lift_t [u]  in
            match uu____23114 with
            | (uu____23121,lift_t1) ->
                let uu____23123 =
                  let uu____23130 =
                    let uu____23131 =
                      let uu____23148 =
                        let uu____23159 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____23168 =
                          let uu____23179 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____23188 =
                            let uu____23199 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____23199]  in
                          uu____23179 :: uu____23188  in
                        uu____23159 :: uu____23168  in
                      (lift_t1, uu____23148)  in
                    FStar_Syntax_Syntax.Tm_app uu____23131  in
                  FStar_Syntax_Syntax.mk uu____23130  in
                uu____23123 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub_or_lift_t with
            | FStar_Util.Inl sub1 ->
                (match sub1.FStar_Syntax_Syntax.lift_wp with
                 | FStar_Pervasives_Native.Some sub_lift_wp ->
                     mk_mlift_wp sub_lift_wp
                 | FStar_Pervasives_Native.None  ->
                     failwith
                       "sub effect should've been elaborated at this stage")
            | FStar_Util.Inr t -> t  in
          let sub_mlift_term =
            match sub_or_lift_t with
            | FStar_Util.Inl sub1 ->
                FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift
                  mk_mlift_term
            | uu____23349 -> FStar_Pervasives_Native.None  in
          let edge =
            {
              msource = src;
              mtarget = tgt;
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift }  in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____23400  ->
                    match uu____23400 with
                    | (e,uu____23408) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____23431 =
            match uu____23431 with
            | (i,j) ->
                let uu____23442 = FStar_Ident.lid_equals i j  in
                if uu____23442
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _23449  -> FStar_Pervasives_Native.Some _23449)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____23478 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____23488 = FStar_Ident.lid_equals i k  in
                        if uu____23488
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____23502 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____23502
                                  then []
                                  else
                                    (let uu____23509 =
                                       let uu____23518 =
                                         find_edge order1 (i, k)  in
                                       let uu____23521 =
                                         find_edge order1 (k, j)  in
                                       (uu____23518, uu____23521)  in
                                     match uu____23509 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____23536 =
                                           compose_edges e1 e2  in
                                         [uu____23536]
                                     | uu____23537 -> [])))))
                 in
              FStar_List.append order1 uu____23478  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          FStar_All.pipe_right order2
            (FStar_List.iter
               (fun edge1  ->
                  let uu____23567 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____23570 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____23570
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____23567
                  then
                    let uu____23577 =
                      let uu____23583 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____23583)
                       in
                    let uu____23587 = get_range env  in
                    FStar_Errors.raise_error uu____23577 uu____23587
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt =
                               let uu____23665 = FStar_Ident.lid_equals i j
                                  in
                               if uu____23665
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____23717 =
                                             let uu____23726 =
                                               find_edge order2 (i, k)  in
                                             let uu____23729 =
                                               find_edge order2 (j, k)  in
                                             (uu____23726, uu____23729)  in
                                           match uu____23717 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____23771,uu____23772)
                                                    ->
                                                    let uu____23779 =
                                                      let uu____23786 =
                                                        let uu____23788 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23788
                                                         in
                                                      let uu____23791 =
                                                        let uu____23793 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23793
                                                         in
                                                      (uu____23786,
                                                        uu____23791)
                                                       in
                                                    (match uu____23779 with
                                                     | (true ,true ) ->
                                                         let uu____23810 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____23810
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
                                                     | (false ,true ) -> bopt))
                                           | uu____23853 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1752_23926 = env.effects  in
             { decls = (uu___1752_23926.decls); order = order2; joins }  in
           let uu___1755_23927 = env  in
           {
             solver = (uu___1755_23927.solver);
             range = (uu___1755_23927.range);
             curmodule = (uu___1755_23927.curmodule);
             gamma = (uu___1755_23927.gamma);
             gamma_sig = (uu___1755_23927.gamma_sig);
             gamma_cache = (uu___1755_23927.gamma_cache);
             modules = (uu___1755_23927.modules);
             expected_typ = (uu___1755_23927.expected_typ);
             sigtab = (uu___1755_23927.sigtab);
             attrtab = (uu___1755_23927.attrtab);
             is_pattern = (uu___1755_23927.is_pattern);
             instantiate_imp = (uu___1755_23927.instantiate_imp);
             effects;
             generalize = (uu___1755_23927.generalize);
             letrecs = (uu___1755_23927.letrecs);
             top_level = (uu___1755_23927.top_level);
             check_uvars = (uu___1755_23927.check_uvars);
             use_eq = (uu___1755_23927.use_eq);
             is_iface = (uu___1755_23927.is_iface);
             admit = (uu___1755_23927.admit);
             lax = (uu___1755_23927.lax);
             lax_universes = (uu___1755_23927.lax_universes);
             phase1 = (uu___1755_23927.phase1);
             failhard = (uu___1755_23927.failhard);
             nosynth = (uu___1755_23927.nosynth);
             uvar_subtyping = (uu___1755_23927.uvar_subtyping);
             tc_term = (uu___1755_23927.tc_term);
             type_of = (uu___1755_23927.type_of);
             universe_of = (uu___1755_23927.universe_of);
             check_type_of = (uu___1755_23927.check_type_of);
             use_bv_sorts = (uu___1755_23927.use_bv_sorts);
             qtbl_name_and_index = (uu___1755_23927.qtbl_name_and_index);
             normalized_eff_names = (uu___1755_23927.normalized_eff_names);
             fv_delta_depths = (uu___1755_23927.fv_delta_depths);
             proof_ns = (uu___1755_23927.proof_ns);
             synth_hook = (uu___1755_23927.synth_hook);
             try_solve_implicits_hook =
               (uu___1755_23927.try_solve_implicits_hook);
             splice = (uu___1755_23927.splice);
             postprocess = (uu___1755_23927.postprocess);
             is_native_tactic = (uu___1755_23927.is_native_tactic);
             identifier_info = (uu___1755_23927.identifier_info);
             tc_hooks = (uu___1755_23927.tc_hooks);
             dsenv = (uu___1755_23927.dsenv);
             nbe = (uu___1755_23927.nbe);
             strict_args_tab = (uu___1755_23927.strict_args_tab)
           })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1759_23939 = env  in
      {
        solver = (uu___1759_23939.solver);
        range = (uu___1759_23939.range);
        curmodule = (uu___1759_23939.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1759_23939.gamma_sig);
        gamma_cache = (uu___1759_23939.gamma_cache);
        modules = (uu___1759_23939.modules);
        expected_typ = (uu___1759_23939.expected_typ);
        sigtab = (uu___1759_23939.sigtab);
        attrtab = (uu___1759_23939.attrtab);
        is_pattern = (uu___1759_23939.is_pattern);
        instantiate_imp = (uu___1759_23939.instantiate_imp);
        effects = (uu___1759_23939.effects);
        generalize = (uu___1759_23939.generalize);
        letrecs = (uu___1759_23939.letrecs);
        top_level = (uu___1759_23939.top_level);
        check_uvars = (uu___1759_23939.check_uvars);
        use_eq = (uu___1759_23939.use_eq);
        is_iface = (uu___1759_23939.is_iface);
        admit = (uu___1759_23939.admit);
        lax = (uu___1759_23939.lax);
        lax_universes = (uu___1759_23939.lax_universes);
        phase1 = (uu___1759_23939.phase1);
        failhard = (uu___1759_23939.failhard);
        nosynth = (uu___1759_23939.nosynth);
        uvar_subtyping = (uu___1759_23939.uvar_subtyping);
        tc_term = (uu___1759_23939.tc_term);
        type_of = (uu___1759_23939.type_of);
        universe_of = (uu___1759_23939.universe_of);
        check_type_of = (uu___1759_23939.check_type_of);
        use_bv_sorts = (uu___1759_23939.use_bv_sorts);
        qtbl_name_and_index = (uu___1759_23939.qtbl_name_and_index);
        normalized_eff_names = (uu___1759_23939.normalized_eff_names);
        fv_delta_depths = (uu___1759_23939.fv_delta_depths);
        proof_ns = (uu___1759_23939.proof_ns);
        synth_hook = (uu___1759_23939.synth_hook);
        try_solve_implicits_hook = (uu___1759_23939.try_solve_implicits_hook);
        splice = (uu___1759_23939.splice);
        postprocess = (uu___1759_23939.postprocess);
        is_native_tactic = (uu___1759_23939.is_native_tactic);
        identifier_info = (uu___1759_23939.identifier_info);
        tc_hooks = (uu___1759_23939.tc_hooks);
        dsenv = (uu___1759_23939.dsenv);
        nbe = (uu___1759_23939.nbe);
        strict_args_tab = (uu___1759_23939.strict_args_tab)
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
            (let uu___1772_23997 = env  in
             {
               solver = (uu___1772_23997.solver);
               range = (uu___1772_23997.range);
               curmodule = (uu___1772_23997.curmodule);
               gamma = rest;
               gamma_sig = (uu___1772_23997.gamma_sig);
               gamma_cache = (uu___1772_23997.gamma_cache);
               modules = (uu___1772_23997.modules);
               expected_typ = (uu___1772_23997.expected_typ);
               sigtab = (uu___1772_23997.sigtab);
               attrtab = (uu___1772_23997.attrtab);
               is_pattern = (uu___1772_23997.is_pattern);
               instantiate_imp = (uu___1772_23997.instantiate_imp);
               effects = (uu___1772_23997.effects);
               generalize = (uu___1772_23997.generalize);
               letrecs = (uu___1772_23997.letrecs);
               top_level = (uu___1772_23997.top_level);
               check_uvars = (uu___1772_23997.check_uvars);
               use_eq = (uu___1772_23997.use_eq);
               is_iface = (uu___1772_23997.is_iface);
               admit = (uu___1772_23997.admit);
               lax = (uu___1772_23997.lax);
               lax_universes = (uu___1772_23997.lax_universes);
               phase1 = (uu___1772_23997.phase1);
               failhard = (uu___1772_23997.failhard);
               nosynth = (uu___1772_23997.nosynth);
               uvar_subtyping = (uu___1772_23997.uvar_subtyping);
               tc_term = (uu___1772_23997.tc_term);
               type_of = (uu___1772_23997.type_of);
               universe_of = (uu___1772_23997.universe_of);
               check_type_of = (uu___1772_23997.check_type_of);
               use_bv_sorts = (uu___1772_23997.use_bv_sorts);
               qtbl_name_and_index = (uu___1772_23997.qtbl_name_and_index);
               normalized_eff_names = (uu___1772_23997.normalized_eff_names);
               fv_delta_depths = (uu___1772_23997.fv_delta_depths);
               proof_ns = (uu___1772_23997.proof_ns);
               synth_hook = (uu___1772_23997.synth_hook);
               try_solve_implicits_hook =
                 (uu___1772_23997.try_solve_implicits_hook);
               splice = (uu___1772_23997.splice);
               postprocess = (uu___1772_23997.postprocess);
               is_native_tactic = (uu___1772_23997.is_native_tactic);
               identifier_info = (uu___1772_23997.identifier_info);
               tc_hooks = (uu___1772_23997.tc_hooks);
               dsenv = (uu___1772_23997.dsenv);
               nbe = (uu___1772_23997.nbe);
               strict_args_tab = (uu___1772_23997.strict_args_tab)
             }))
    | uu____23998 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24027  ->
             match uu____24027 with | (x,uu____24035) -> push_bv env1 x) env
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
            let uu___1786_24070 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1786_24070.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1786_24070.FStar_Syntax_Syntax.index);
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
        let uu____24143 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24143 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24171 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24171)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1807_24187 = env  in
      {
        solver = (uu___1807_24187.solver);
        range = (uu___1807_24187.range);
        curmodule = (uu___1807_24187.curmodule);
        gamma = (uu___1807_24187.gamma);
        gamma_sig = (uu___1807_24187.gamma_sig);
        gamma_cache = (uu___1807_24187.gamma_cache);
        modules = (uu___1807_24187.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1807_24187.sigtab);
        attrtab = (uu___1807_24187.attrtab);
        is_pattern = (uu___1807_24187.is_pattern);
        instantiate_imp = (uu___1807_24187.instantiate_imp);
        effects = (uu___1807_24187.effects);
        generalize = (uu___1807_24187.generalize);
        letrecs = (uu___1807_24187.letrecs);
        top_level = (uu___1807_24187.top_level);
        check_uvars = (uu___1807_24187.check_uvars);
        use_eq = false;
        is_iface = (uu___1807_24187.is_iface);
        admit = (uu___1807_24187.admit);
        lax = (uu___1807_24187.lax);
        lax_universes = (uu___1807_24187.lax_universes);
        phase1 = (uu___1807_24187.phase1);
        failhard = (uu___1807_24187.failhard);
        nosynth = (uu___1807_24187.nosynth);
        uvar_subtyping = (uu___1807_24187.uvar_subtyping);
        tc_term = (uu___1807_24187.tc_term);
        type_of = (uu___1807_24187.type_of);
        universe_of = (uu___1807_24187.universe_of);
        check_type_of = (uu___1807_24187.check_type_of);
        use_bv_sorts = (uu___1807_24187.use_bv_sorts);
        qtbl_name_and_index = (uu___1807_24187.qtbl_name_and_index);
        normalized_eff_names = (uu___1807_24187.normalized_eff_names);
        fv_delta_depths = (uu___1807_24187.fv_delta_depths);
        proof_ns = (uu___1807_24187.proof_ns);
        synth_hook = (uu___1807_24187.synth_hook);
        try_solve_implicits_hook = (uu___1807_24187.try_solve_implicits_hook);
        splice = (uu___1807_24187.splice);
        postprocess = (uu___1807_24187.postprocess);
        is_native_tactic = (uu___1807_24187.is_native_tactic);
        identifier_info = (uu___1807_24187.identifier_info);
        tc_hooks = (uu___1807_24187.tc_hooks);
        dsenv = (uu___1807_24187.dsenv);
        nbe = (uu___1807_24187.nbe);
        strict_args_tab = (uu___1807_24187.strict_args_tab)
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
    let uu____24218 = expected_typ env_  in
    ((let uu___1814_24224 = env_  in
      {
        solver = (uu___1814_24224.solver);
        range = (uu___1814_24224.range);
        curmodule = (uu___1814_24224.curmodule);
        gamma = (uu___1814_24224.gamma);
        gamma_sig = (uu___1814_24224.gamma_sig);
        gamma_cache = (uu___1814_24224.gamma_cache);
        modules = (uu___1814_24224.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1814_24224.sigtab);
        attrtab = (uu___1814_24224.attrtab);
        is_pattern = (uu___1814_24224.is_pattern);
        instantiate_imp = (uu___1814_24224.instantiate_imp);
        effects = (uu___1814_24224.effects);
        generalize = (uu___1814_24224.generalize);
        letrecs = (uu___1814_24224.letrecs);
        top_level = (uu___1814_24224.top_level);
        check_uvars = (uu___1814_24224.check_uvars);
        use_eq = false;
        is_iface = (uu___1814_24224.is_iface);
        admit = (uu___1814_24224.admit);
        lax = (uu___1814_24224.lax);
        lax_universes = (uu___1814_24224.lax_universes);
        phase1 = (uu___1814_24224.phase1);
        failhard = (uu___1814_24224.failhard);
        nosynth = (uu___1814_24224.nosynth);
        uvar_subtyping = (uu___1814_24224.uvar_subtyping);
        tc_term = (uu___1814_24224.tc_term);
        type_of = (uu___1814_24224.type_of);
        universe_of = (uu___1814_24224.universe_of);
        check_type_of = (uu___1814_24224.check_type_of);
        use_bv_sorts = (uu___1814_24224.use_bv_sorts);
        qtbl_name_and_index = (uu___1814_24224.qtbl_name_and_index);
        normalized_eff_names = (uu___1814_24224.normalized_eff_names);
        fv_delta_depths = (uu___1814_24224.fv_delta_depths);
        proof_ns = (uu___1814_24224.proof_ns);
        synth_hook = (uu___1814_24224.synth_hook);
        try_solve_implicits_hook = (uu___1814_24224.try_solve_implicits_hook);
        splice = (uu___1814_24224.splice);
        postprocess = (uu___1814_24224.postprocess);
        is_native_tactic = (uu___1814_24224.is_native_tactic);
        identifier_info = (uu___1814_24224.identifier_info);
        tc_hooks = (uu___1814_24224.tc_hooks);
        dsenv = (uu___1814_24224.dsenv);
        nbe = (uu___1814_24224.nbe);
        strict_args_tab = (uu___1814_24224.strict_args_tab)
      }), uu____24218)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24236 =
      let uu____24239 = FStar_Ident.id_of_text ""  in [uu____24239]  in
    FStar_Ident.lid_of_ids uu____24236  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24246 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24246
        then
          let uu____24251 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24251 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1822_24279 = env  in
       {
         solver = (uu___1822_24279.solver);
         range = (uu___1822_24279.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1822_24279.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1822_24279.expected_typ);
         sigtab = (uu___1822_24279.sigtab);
         attrtab = (uu___1822_24279.attrtab);
         is_pattern = (uu___1822_24279.is_pattern);
         instantiate_imp = (uu___1822_24279.instantiate_imp);
         effects = (uu___1822_24279.effects);
         generalize = (uu___1822_24279.generalize);
         letrecs = (uu___1822_24279.letrecs);
         top_level = (uu___1822_24279.top_level);
         check_uvars = (uu___1822_24279.check_uvars);
         use_eq = (uu___1822_24279.use_eq);
         is_iface = (uu___1822_24279.is_iface);
         admit = (uu___1822_24279.admit);
         lax = (uu___1822_24279.lax);
         lax_universes = (uu___1822_24279.lax_universes);
         phase1 = (uu___1822_24279.phase1);
         failhard = (uu___1822_24279.failhard);
         nosynth = (uu___1822_24279.nosynth);
         uvar_subtyping = (uu___1822_24279.uvar_subtyping);
         tc_term = (uu___1822_24279.tc_term);
         type_of = (uu___1822_24279.type_of);
         universe_of = (uu___1822_24279.universe_of);
         check_type_of = (uu___1822_24279.check_type_of);
         use_bv_sorts = (uu___1822_24279.use_bv_sorts);
         qtbl_name_and_index = (uu___1822_24279.qtbl_name_and_index);
         normalized_eff_names = (uu___1822_24279.normalized_eff_names);
         fv_delta_depths = (uu___1822_24279.fv_delta_depths);
         proof_ns = (uu___1822_24279.proof_ns);
         synth_hook = (uu___1822_24279.synth_hook);
         try_solve_implicits_hook =
           (uu___1822_24279.try_solve_implicits_hook);
         splice = (uu___1822_24279.splice);
         postprocess = (uu___1822_24279.postprocess);
         is_native_tactic = (uu___1822_24279.is_native_tactic);
         identifier_info = (uu___1822_24279.identifier_info);
         tc_hooks = (uu___1822_24279.tc_hooks);
         dsenv = (uu___1822_24279.dsenv);
         nbe = (uu___1822_24279.nbe);
         strict_args_tab = (uu___1822_24279.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24331)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24335,(uu____24336,t)))::tl1
          ->
          let uu____24357 =
            let uu____24360 = FStar_Syntax_Free.uvars t  in
            ext out uu____24360  in
          aux uu____24357 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24363;
            FStar_Syntax_Syntax.index = uu____24364;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24372 =
            let uu____24375 = FStar_Syntax_Free.uvars t  in
            ext out uu____24375  in
          aux uu____24372 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24433)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24437,(uu____24438,t)))::tl1
          ->
          let uu____24459 =
            let uu____24462 = FStar_Syntax_Free.univs t  in
            ext out uu____24462  in
          aux uu____24459 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24465;
            FStar_Syntax_Syntax.index = uu____24466;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24474 =
            let uu____24477 = FStar_Syntax_Free.univs t  in
            ext out uu____24477  in
          aux uu____24474 tl1
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
          let uu____24539 = FStar_Util.set_add uname out  in
          aux uu____24539 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24542,(uu____24543,t)))::tl1
          ->
          let uu____24564 =
            let uu____24567 = FStar_Syntax_Free.univnames t  in
            ext out uu____24567  in
          aux uu____24564 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24570;
            FStar_Syntax_Syntax.index = uu____24571;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24579 =
            let uu____24582 = FStar_Syntax_Free.univnames t  in
            ext out uu____24582  in
          aux uu____24579 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24603  ->
            match uu___11_24603 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24607 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24620 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24631 =
      let uu____24640 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24640
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24631 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24688 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24701  ->
              match uu___12_24701 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24704 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24704
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24710) ->
                  let uu____24727 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24727))
       in
    FStar_All.pipe_right uu____24688 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24741  ->
    match uu___13_24741 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24747 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24747
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24770  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24825) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24858,uu____24859) -> false  in
      let uu____24873 =
        FStar_List.tryFind
          (fun uu____24895  ->
             match uu____24895 with | (p,uu____24906) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24873 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24925,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24955 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24955
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1965_24977 = e  in
        {
          solver = (uu___1965_24977.solver);
          range = (uu___1965_24977.range);
          curmodule = (uu___1965_24977.curmodule);
          gamma = (uu___1965_24977.gamma);
          gamma_sig = (uu___1965_24977.gamma_sig);
          gamma_cache = (uu___1965_24977.gamma_cache);
          modules = (uu___1965_24977.modules);
          expected_typ = (uu___1965_24977.expected_typ);
          sigtab = (uu___1965_24977.sigtab);
          attrtab = (uu___1965_24977.attrtab);
          is_pattern = (uu___1965_24977.is_pattern);
          instantiate_imp = (uu___1965_24977.instantiate_imp);
          effects = (uu___1965_24977.effects);
          generalize = (uu___1965_24977.generalize);
          letrecs = (uu___1965_24977.letrecs);
          top_level = (uu___1965_24977.top_level);
          check_uvars = (uu___1965_24977.check_uvars);
          use_eq = (uu___1965_24977.use_eq);
          is_iface = (uu___1965_24977.is_iface);
          admit = (uu___1965_24977.admit);
          lax = (uu___1965_24977.lax);
          lax_universes = (uu___1965_24977.lax_universes);
          phase1 = (uu___1965_24977.phase1);
          failhard = (uu___1965_24977.failhard);
          nosynth = (uu___1965_24977.nosynth);
          uvar_subtyping = (uu___1965_24977.uvar_subtyping);
          tc_term = (uu___1965_24977.tc_term);
          type_of = (uu___1965_24977.type_of);
          universe_of = (uu___1965_24977.universe_of);
          check_type_of = (uu___1965_24977.check_type_of);
          use_bv_sorts = (uu___1965_24977.use_bv_sorts);
          qtbl_name_and_index = (uu___1965_24977.qtbl_name_and_index);
          normalized_eff_names = (uu___1965_24977.normalized_eff_names);
          fv_delta_depths = (uu___1965_24977.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1965_24977.synth_hook);
          try_solve_implicits_hook =
            (uu___1965_24977.try_solve_implicits_hook);
          splice = (uu___1965_24977.splice);
          postprocess = (uu___1965_24977.postprocess);
          is_native_tactic = (uu___1965_24977.is_native_tactic);
          identifier_info = (uu___1965_24977.identifier_info);
          tc_hooks = (uu___1965_24977.tc_hooks);
          dsenv = (uu___1965_24977.dsenv);
          nbe = (uu___1965_24977.nbe);
          strict_args_tab = (uu___1965_24977.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1974_25025 = e  in
      {
        solver = (uu___1974_25025.solver);
        range = (uu___1974_25025.range);
        curmodule = (uu___1974_25025.curmodule);
        gamma = (uu___1974_25025.gamma);
        gamma_sig = (uu___1974_25025.gamma_sig);
        gamma_cache = (uu___1974_25025.gamma_cache);
        modules = (uu___1974_25025.modules);
        expected_typ = (uu___1974_25025.expected_typ);
        sigtab = (uu___1974_25025.sigtab);
        attrtab = (uu___1974_25025.attrtab);
        is_pattern = (uu___1974_25025.is_pattern);
        instantiate_imp = (uu___1974_25025.instantiate_imp);
        effects = (uu___1974_25025.effects);
        generalize = (uu___1974_25025.generalize);
        letrecs = (uu___1974_25025.letrecs);
        top_level = (uu___1974_25025.top_level);
        check_uvars = (uu___1974_25025.check_uvars);
        use_eq = (uu___1974_25025.use_eq);
        is_iface = (uu___1974_25025.is_iface);
        admit = (uu___1974_25025.admit);
        lax = (uu___1974_25025.lax);
        lax_universes = (uu___1974_25025.lax_universes);
        phase1 = (uu___1974_25025.phase1);
        failhard = (uu___1974_25025.failhard);
        nosynth = (uu___1974_25025.nosynth);
        uvar_subtyping = (uu___1974_25025.uvar_subtyping);
        tc_term = (uu___1974_25025.tc_term);
        type_of = (uu___1974_25025.type_of);
        universe_of = (uu___1974_25025.universe_of);
        check_type_of = (uu___1974_25025.check_type_of);
        use_bv_sorts = (uu___1974_25025.use_bv_sorts);
        qtbl_name_and_index = (uu___1974_25025.qtbl_name_and_index);
        normalized_eff_names = (uu___1974_25025.normalized_eff_names);
        fv_delta_depths = (uu___1974_25025.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1974_25025.synth_hook);
        try_solve_implicits_hook = (uu___1974_25025.try_solve_implicits_hook);
        splice = (uu___1974_25025.splice);
        postprocess = (uu___1974_25025.postprocess);
        is_native_tactic = (uu___1974_25025.is_native_tactic);
        identifier_info = (uu___1974_25025.identifier_info);
        tc_hooks = (uu___1974_25025.tc_hooks);
        dsenv = (uu___1974_25025.dsenv);
        nbe = (uu___1974_25025.nbe);
        strict_args_tab = (uu___1974_25025.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25041 = FStar_Syntax_Free.names t  in
      let uu____25044 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25041 uu____25044
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25067 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25067
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25077 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25077
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25098 =
      match uu____25098 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25118 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25118)
       in
    let uu____25126 =
      let uu____25130 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25130 FStar_List.rev  in
    FStar_All.pipe_right uu____25126 (FStar_String.concat " ")
  
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
                  (let uu____25198 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25198 with
                   | FStar_Pervasives_Native.Some uu____25202 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25205 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25215;
        FStar_TypeChecker_Common.univ_ineqs = uu____25216;
        FStar_TypeChecker_Common.implicits = uu____25217;_} -> true
    | uu____25227 -> false
  
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
          let uu___2018_25249 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2018_25249.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2018_25249.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2018_25249.FStar_TypeChecker_Common.implicits)
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
          let uu____25288 = FStar_Options.defensive ()  in
          if uu____25288
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25294 =
              let uu____25296 =
                let uu____25298 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25298  in
              Prims.op_Negation uu____25296  in
            (if uu____25294
             then
               let uu____25305 =
                 let uu____25311 =
                   let uu____25313 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25315 =
                     let uu____25317 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25317
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25313 uu____25315
                    in
                 (FStar_Errors.Warning_Defensive, uu____25311)  in
               FStar_Errors.log_issue rng uu____25305
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
          let uu____25357 =
            let uu____25359 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25359  in
          if uu____25357
          then ()
          else
            (let uu____25364 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25364 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25390 =
            let uu____25392 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25392  in
          if uu____25390
          then ()
          else
            (let uu____25397 = bound_vars e  in
             def_check_closed_in rng msg uu____25397 t)
  
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
          let uu___2055_25436 = g  in
          let uu____25437 =
            let uu____25438 =
              let uu____25439 =
                let uu____25446 =
                  let uu____25447 =
                    let uu____25464 =
                      let uu____25475 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25475]  in
                    (f, uu____25464)  in
                  FStar_Syntax_Syntax.Tm_app uu____25447  in
                FStar_Syntax_Syntax.mk uu____25446  in
              uu____25439 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25512  -> FStar_TypeChecker_Common.NonTrivial _25512)
              uu____25438
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____25437;
            FStar_TypeChecker_Common.deferred =
              (uu___2055_25436.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2055_25436.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2055_25436.FStar_TypeChecker_Common.implicits)
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
          let uu___2062_25530 = g  in
          let uu____25531 =
            let uu____25532 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25532  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25531;
            FStar_TypeChecker_Common.deferred =
              (uu___2062_25530.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2062_25530.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2062_25530.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2067_25549 = g  in
          let uu____25550 =
            let uu____25551 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25551  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25550;
            FStar_TypeChecker_Common.deferred =
              (uu___2067_25549.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2067_25549.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2067_25549.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2071_25553 = g  in
          let uu____25554 =
            let uu____25555 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25555  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25554;
            FStar_TypeChecker_Common.deferred =
              (uu___2071_25553.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2071_25553.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2071_25553.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25562 ->
        failwith "impossible"
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  -> FStar_TypeChecker_Common.check_trivial t 
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> FStar_TypeChecker_Common.conj_guard g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_TypeChecker_Common.conj_guards gs 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> FStar_TypeChecker_Common.imp_guard g1 g2 
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
                       let uu____25639 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25639
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2094_25646 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2094_25646.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2094_25646.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2094_25646.FStar_TypeChecker_Common.implicits)
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
               let uu____25680 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25680
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
            let uu___2109_25707 = g  in
            let uu____25708 =
              let uu____25709 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25709  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25708;
              FStar_TypeChecker_Common.deferred =
                (uu___2109_25707.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2109_25707.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2109_25707.FStar_TypeChecker_Common.implicits)
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
              let uu____25767 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25767 with
              | FStar_Pervasives_Native.Some
                  (uu____25792::(tm,uu____25794)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25858 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25876 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25876;
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
                      let uu___2131_25908 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2131_25908.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2131_25908.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2131_25908.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (uvars_for_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.subst_t ->
        (FStar_Syntax_Syntax.binder -> Prims.string) ->
          FStar_Range.range ->
            (FStar_Syntax_Syntax.term Prims.list * guard_t))
  =
  fun env  ->
    fun bs  ->
      fun substs  ->
        fun reason  ->
          fun r  ->
            let uu____25962 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____26019  ->
                      fun b  ->
                        match uu____26019 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____26061 =
                              let uu____26074 = reason b  in
                              new_implicit_var_aux uu____26074 r env sort
                                FStar_Syntax_Syntax.Strict
                                FStar_Pervasives_Native.None
                               in
                            (match uu____26061 with
                             | (t,uu____26091,g_t) ->
                                 let uu____26105 =
                                   let uu____26108 =
                                     let uu____26111 =
                                       let uu____26112 =
                                         let uu____26119 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26119, t)  in
                                       FStar_Syntax_Syntax.NT uu____26112  in
                                     [uu____26111]  in
                                   FStar_List.append substs1 uu____26108  in
                                 let uu____26130 = conj_guard g g_t  in
                                 (uu____26105,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26130))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____25962
              (fun uu____26159  ->
                 match uu____26159 with
                 | (uu____26176,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26192  -> ());
    push = (fun uu____26194  -> ());
    pop = (fun uu____26197  -> ());
    snapshot =
      (fun uu____26200  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26219  -> fun uu____26220  -> ());
    encode_sig = (fun uu____26235  -> fun uu____26236  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26242 =
             let uu____26249 = FStar_Options.peek ()  in (e, g, uu____26249)
              in
           [uu____26242]);
    solve = (fun uu____26265  -> fun uu____26266  -> fun uu____26267  -> ());
    finish = (fun uu____26274  -> ());
    refresh = (fun uu____26276  -> ())
  } 