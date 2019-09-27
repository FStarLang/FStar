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
  fun projectee  -> match projectee with | Beta  -> true | uu____104 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____115 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____126 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____138 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____156 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____167 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____178 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____189 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____200 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____211 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____223 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____244 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____271 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____298 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____322 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____333 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____344 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____355 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____366 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____377 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____388 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____399 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____410 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____421 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____432 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____443 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____454 -> false
  
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
      | uu____514 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____540 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____551 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____562 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____574 -> false
  
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
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap ;
  erasable_types_tab: Prims.bool FStar_Util.smap }
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
        strict_args_tab; erasable_types_tab;_} -> solver
  
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
        strict_args_tab; erasable_types_tab;_} -> range
  
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
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
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
        strict_args_tab; erasable_types_tab;_} -> gamma
  
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
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
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
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
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
        strict_args_tab; erasable_types_tab;_} -> modules
  
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
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
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
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
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
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
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
        strict_args_tab; erasable_types_tab;_} -> is_pattern
  
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
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
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
        strict_args_tab; erasable_types_tab;_} -> effects
  
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
        strict_args_tab; erasable_types_tab;_} -> generalize
  
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
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
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
        strict_args_tab; erasable_types_tab;_} -> top_level
  
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
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
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
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
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
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
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
        strict_args_tab; erasable_types_tab;_} -> admit1
  
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
        strict_args_tab; erasable_types_tab;_} -> lax1
  
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
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
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
        strict_args_tab; erasable_types_tab;_} -> phase1
  
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
        strict_args_tab; erasable_types_tab;_} -> failhard
  
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
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
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
        strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
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
        strict_args_tab; erasable_types_tab;_} -> tc_term
  
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
        strict_args_tab; erasable_types_tab;_} -> type_of
  
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
        strict_args_tab; erasable_types_tab;_} -> universe_of
  
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
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
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
        strict_args_tab; erasable_types_tab;_} -> use_bv_sorts
  
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
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
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
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
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
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
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
        strict_args_tab; erasable_types_tab;_} -> proof_ns
  
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
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
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
        strict_args_tab; erasable_types_tab;_} -> try_solve_implicits_hook
  
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
        strict_args_tab; erasable_types_tab;_} -> splice1
  
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
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
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
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
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
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
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
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
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
        strict_args_tab; erasable_types_tab;_} -> dsenv
  
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
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
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
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
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
        strict_args_tab; erasable_types_tab;_} -> erasable_types_tab
  
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
           (fun uu___0_13266  ->
              match uu___0_13266 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13269 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13269  in
                  let uu____13270 =
                    let uu____13271 = FStar_Syntax_Subst.compress y  in
                    uu____13271.FStar_Syntax_Syntax.n  in
                  (match uu____13270 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13275 =
                         let uu___315_13276 = y1  in
                         let uu____13277 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___315_13276.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___315_13276.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13277
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13275
                   | uu____13280 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___321_13294 = env  in
      let uu____13295 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___321_13294.solver);
        range = (uu___321_13294.range);
        curmodule = (uu___321_13294.curmodule);
        gamma = uu____13295;
        gamma_sig = (uu___321_13294.gamma_sig);
        gamma_cache = (uu___321_13294.gamma_cache);
        modules = (uu___321_13294.modules);
        expected_typ = (uu___321_13294.expected_typ);
        sigtab = (uu___321_13294.sigtab);
        attrtab = (uu___321_13294.attrtab);
        is_pattern = (uu___321_13294.is_pattern);
        instantiate_imp = (uu___321_13294.instantiate_imp);
        effects = (uu___321_13294.effects);
        generalize = (uu___321_13294.generalize);
        letrecs = (uu___321_13294.letrecs);
        top_level = (uu___321_13294.top_level);
        check_uvars = (uu___321_13294.check_uvars);
        use_eq = (uu___321_13294.use_eq);
        is_iface = (uu___321_13294.is_iface);
        admit = (uu___321_13294.admit);
        lax = (uu___321_13294.lax);
        lax_universes = (uu___321_13294.lax_universes);
        phase1 = (uu___321_13294.phase1);
        failhard = (uu___321_13294.failhard);
        nosynth = (uu___321_13294.nosynth);
        uvar_subtyping = (uu___321_13294.uvar_subtyping);
        tc_term = (uu___321_13294.tc_term);
        type_of = (uu___321_13294.type_of);
        universe_of = (uu___321_13294.universe_of);
        check_type_of = (uu___321_13294.check_type_of);
        use_bv_sorts = (uu___321_13294.use_bv_sorts);
        qtbl_name_and_index = (uu___321_13294.qtbl_name_and_index);
        normalized_eff_names = (uu___321_13294.normalized_eff_names);
        fv_delta_depths = (uu___321_13294.fv_delta_depths);
        proof_ns = (uu___321_13294.proof_ns);
        synth_hook = (uu___321_13294.synth_hook);
        try_solve_implicits_hook = (uu___321_13294.try_solve_implicits_hook);
        splice = (uu___321_13294.splice);
        postprocess = (uu___321_13294.postprocess);
        is_native_tactic = (uu___321_13294.is_native_tactic);
        identifier_info = (uu___321_13294.identifier_info);
        tc_hooks = (uu___321_13294.tc_hooks);
        dsenv = (uu___321_13294.dsenv);
        nbe = (uu___321_13294.nbe);
        strict_args_tab = (uu___321_13294.strict_args_tab);
        erasable_types_tab = (uu___321_13294.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13303  -> fun uu____13304  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___328_13326 = env  in
      {
        solver = (uu___328_13326.solver);
        range = (uu___328_13326.range);
        curmodule = (uu___328_13326.curmodule);
        gamma = (uu___328_13326.gamma);
        gamma_sig = (uu___328_13326.gamma_sig);
        gamma_cache = (uu___328_13326.gamma_cache);
        modules = (uu___328_13326.modules);
        expected_typ = (uu___328_13326.expected_typ);
        sigtab = (uu___328_13326.sigtab);
        attrtab = (uu___328_13326.attrtab);
        is_pattern = (uu___328_13326.is_pattern);
        instantiate_imp = (uu___328_13326.instantiate_imp);
        effects = (uu___328_13326.effects);
        generalize = (uu___328_13326.generalize);
        letrecs = (uu___328_13326.letrecs);
        top_level = (uu___328_13326.top_level);
        check_uvars = (uu___328_13326.check_uvars);
        use_eq = (uu___328_13326.use_eq);
        is_iface = (uu___328_13326.is_iface);
        admit = (uu___328_13326.admit);
        lax = (uu___328_13326.lax);
        lax_universes = (uu___328_13326.lax_universes);
        phase1 = (uu___328_13326.phase1);
        failhard = (uu___328_13326.failhard);
        nosynth = (uu___328_13326.nosynth);
        uvar_subtyping = (uu___328_13326.uvar_subtyping);
        tc_term = (uu___328_13326.tc_term);
        type_of = (uu___328_13326.type_of);
        universe_of = (uu___328_13326.universe_of);
        check_type_of = (uu___328_13326.check_type_of);
        use_bv_sorts = (uu___328_13326.use_bv_sorts);
        qtbl_name_and_index = (uu___328_13326.qtbl_name_and_index);
        normalized_eff_names = (uu___328_13326.normalized_eff_names);
        fv_delta_depths = (uu___328_13326.fv_delta_depths);
        proof_ns = (uu___328_13326.proof_ns);
        synth_hook = (uu___328_13326.synth_hook);
        try_solve_implicits_hook = (uu___328_13326.try_solve_implicits_hook);
        splice = (uu___328_13326.splice);
        postprocess = (uu___328_13326.postprocess);
        is_native_tactic = (uu___328_13326.is_native_tactic);
        identifier_info = (uu___328_13326.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___328_13326.dsenv);
        nbe = (uu___328_13326.nbe);
        strict_args_tab = (uu___328_13326.strict_args_tab);
        erasable_types_tab = (uu___328_13326.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___332_13338 = e  in
      let uu____13339 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___332_13338.solver);
        range = (uu___332_13338.range);
        curmodule = (uu___332_13338.curmodule);
        gamma = (uu___332_13338.gamma);
        gamma_sig = (uu___332_13338.gamma_sig);
        gamma_cache = (uu___332_13338.gamma_cache);
        modules = (uu___332_13338.modules);
        expected_typ = (uu___332_13338.expected_typ);
        sigtab = (uu___332_13338.sigtab);
        attrtab = (uu___332_13338.attrtab);
        is_pattern = (uu___332_13338.is_pattern);
        instantiate_imp = (uu___332_13338.instantiate_imp);
        effects = (uu___332_13338.effects);
        generalize = (uu___332_13338.generalize);
        letrecs = (uu___332_13338.letrecs);
        top_level = (uu___332_13338.top_level);
        check_uvars = (uu___332_13338.check_uvars);
        use_eq = (uu___332_13338.use_eq);
        is_iface = (uu___332_13338.is_iface);
        admit = (uu___332_13338.admit);
        lax = (uu___332_13338.lax);
        lax_universes = (uu___332_13338.lax_universes);
        phase1 = (uu___332_13338.phase1);
        failhard = (uu___332_13338.failhard);
        nosynth = (uu___332_13338.nosynth);
        uvar_subtyping = (uu___332_13338.uvar_subtyping);
        tc_term = (uu___332_13338.tc_term);
        type_of = (uu___332_13338.type_of);
        universe_of = (uu___332_13338.universe_of);
        check_type_of = (uu___332_13338.check_type_of);
        use_bv_sorts = (uu___332_13338.use_bv_sorts);
        qtbl_name_and_index = (uu___332_13338.qtbl_name_and_index);
        normalized_eff_names = (uu___332_13338.normalized_eff_names);
        fv_delta_depths = (uu___332_13338.fv_delta_depths);
        proof_ns = (uu___332_13338.proof_ns);
        synth_hook = (uu___332_13338.synth_hook);
        try_solve_implicits_hook = (uu___332_13338.try_solve_implicits_hook);
        splice = (uu___332_13338.splice);
        postprocess = (uu___332_13338.postprocess);
        is_native_tactic = (uu___332_13338.is_native_tactic);
        identifier_info = (uu___332_13338.identifier_info);
        tc_hooks = (uu___332_13338.tc_hooks);
        dsenv = uu____13339;
        nbe = (uu___332_13338.nbe);
        strict_args_tab = (uu___332_13338.strict_args_tab);
        erasable_types_tab = (uu___332_13338.erasable_types_tab)
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
      | (NoDelta ,uu____13368) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13371,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13373,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13376 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13390 . unit -> 'Auu____13390 FStar_Util.smap =
  fun uu____13397  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13403 . unit -> 'Auu____13403 FStar_Util.smap =
  fun uu____13410  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13548 = new_gamma_cache ()  in
                  let uu____13551 = new_sigtab ()  in
                  let uu____13554 = new_sigtab ()  in
                  let uu____13561 =
                    let uu____13576 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13576, FStar_Pervasives_Native.None)  in
                  let uu____13597 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13601 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13605 = FStar_Options.using_facts_from ()  in
                  let uu____13606 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13609 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13610 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13624 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13548;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13551;
                    attrtab = uu____13554;
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
                    qtbl_name_and_index = uu____13561;
                    normalized_eff_names = uu____13597;
                    fv_delta_depths = uu____13601;
                    proof_ns = uu____13605;
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
                    is_native_tactic = (fun uu____13698  -> false);
                    identifier_info = uu____13606;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13609;
                    nbe = nbe1;
                    strict_args_tab = uu____13610;
                    erasable_types_tab = uu____13624
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
  fun uu____13777  ->
    let uu____13778 = FStar_ST.op_Bang query_indices  in
    match uu____13778 with
    | [] -> failwith "Empty query indices!"
    | uu____13833 ->
        let uu____13843 =
          let uu____13853 =
            let uu____13861 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13861  in
          let uu____13915 = FStar_ST.op_Bang query_indices  in uu____13853 ::
            uu____13915
           in
        FStar_ST.op_Colon_Equals query_indices uu____13843
  
let (pop_query_indices : unit -> unit) =
  fun uu____14011  ->
    let uu____14012 = FStar_ST.op_Bang query_indices  in
    match uu____14012 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14139  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14176  ->
    match uu____14176 with
    | (l,n1) ->
        let uu____14186 = FStar_ST.op_Bang query_indices  in
        (match uu____14186 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14308 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14331  ->
    let uu____14332 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14332
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14400 =
       let uu____14403 = FStar_ST.op_Bang stack  in env :: uu____14403  in
     FStar_ST.op_Colon_Equals stack uu____14400);
    (let uu___403_14452 = env  in
     let uu____14453 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14456 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14459 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14466 =
       let uu____14481 =
         let uu____14485 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14485  in
       let uu____14517 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14481, uu____14517)  in
     let uu____14566 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14569 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14572 =
       let uu____14575 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14575  in
     let uu____14595 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14608 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___403_14452.solver);
       range = (uu___403_14452.range);
       curmodule = (uu___403_14452.curmodule);
       gamma = (uu___403_14452.gamma);
       gamma_sig = (uu___403_14452.gamma_sig);
       gamma_cache = uu____14453;
       modules = (uu___403_14452.modules);
       expected_typ = (uu___403_14452.expected_typ);
       sigtab = uu____14456;
       attrtab = uu____14459;
       is_pattern = (uu___403_14452.is_pattern);
       instantiate_imp = (uu___403_14452.instantiate_imp);
       effects = (uu___403_14452.effects);
       generalize = (uu___403_14452.generalize);
       letrecs = (uu___403_14452.letrecs);
       top_level = (uu___403_14452.top_level);
       check_uvars = (uu___403_14452.check_uvars);
       use_eq = (uu___403_14452.use_eq);
       is_iface = (uu___403_14452.is_iface);
       admit = (uu___403_14452.admit);
       lax = (uu___403_14452.lax);
       lax_universes = (uu___403_14452.lax_universes);
       phase1 = (uu___403_14452.phase1);
       failhard = (uu___403_14452.failhard);
       nosynth = (uu___403_14452.nosynth);
       uvar_subtyping = (uu___403_14452.uvar_subtyping);
       tc_term = (uu___403_14452.tc_term);
       type_of = (uu___403_14452.type_of);
       universe_of = (uu___403_14452.universe_of);
       check_type_of = (uu___403_14452.check_type_of);
       use_bv_sorts = (uu___403_14452.use_bv_sorts);
       qtbl_name_and_index = uu____14466;
       normalized_eff_names = uu____14566;
       fv_delta_depths = uu____14569;
       proof_ns = (uu___403_14452.proof_ns);
       synth_hook = (uu___403_14452.synth_hook);
       try_solve_implicits_hook = (uu___403_14452.try_solve_implicits_hook);
       splice = (uu___403_14452.splice);
       postprocess = (uu___403_14452.postprocess);
       is_native_tactic = (uu___403_14452.is_native_tactic);
       identifier_info = uu____14572;
       tc_hooks = (uu___403_14452.tc_hooks);
       dsenv = (uu___403_14452.dsenv);
       nbe = (uu___403_14452.nbe);
       strict_args_tab = uu____14595;
       erasable_types_tab = uu____14608
     })
  
let (pop_stack : unit -> env) =
  fun uu____14618  ->
    let uu____14619 = FStar_ST.op_Bang stack  in
    match uu____14619 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14673 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14763  ->
           let uu____14764 = snapshot_stack env  in
           match uu____14764 with
           | (stack_depth,env1) ->
               let uu____14798 = snapshot_query_indices ()  in
               (match uu____14798 with
                | (query_indices_depth,()) ->
                    let uu____14831 = (env1.solver).snapshot msg  in
                    (match uu____14831 with
                     | (solver_depth,()) ->
                         let uu____14888 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14888 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___428_14955 = env1  in
                                 {
                                   solver = (uu___428_14955.solver);
                                   range = (uu___428_14955.range);
                                   curmodule = (uu___428_14955.curmodule);
                                   gamma = (uu___428_14955.gamma);
                                   gamma_sig = (uu___428_14955.gamma_sig);
                                   gamma_cache = (uu___428_14955.gamma_cache);
                                   modules = (uu___428_14955.modules);
                                   expected_typ =
                                     (uu___428_14955.expected_typ);
                                   sigtab = (uu___428_14955.sigtab);
                                   attrtab = (uu___428_14955.attrtab);
                                   is_pattern = (uu___428_14955.is_pattern);
                                   instantiate_imp =
                                     (uu___428_14955.instantiate_imp);
                                   effects = (uu___428_14955.effects);
                                   generalize = (uu___428_14955.generalize);
                                   letrecs = (uu___428_14955.letrecs);
                                   top_level = (uu___428_14955.top_level);
                                   check_uvars = (uu___428_14955.check_uvars);
                                   use_eq = (uu___428_14955.use_eq);
                                   is_iface = (uu___428_14955.is_iface);
                                   admit = (uu___428_14955.admit);
                                   lax = (uu___428_14955.lax);
                                   lax_universes =
                                     (uu___428_14955.lax_universes);
                                   phase1 = (uu___428_14955.phase1);
                                   failhard = (uu___428_14955.failhard);
                                   nosynth = (uu___428_14955.nosynth);
                                   uvar_subtyping =
                                     (uu___428_14955.uvar_subtyping);
                                   tc_term = (uu___428_14955.tc_term);
                                   type_of = (uu___428_14955.type_of);
                                   universe_of = (uu___428_14955.universe_of);
                                   check_type_of =
                                     (uu___428_14955.check_type_of);
                                   use_bv_sorts =
                                     (uu___428_14955.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___428_14955.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___428_14955.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___428_14955.fv_delta_depths);
                                   proof_ns = (uu___428_14955.proof_ns);
                                   synth_hook = (uu___428_14955.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___428_14955.try_solve_implicits_hook);
                                   splice = (uu___428_14955.splice);
                                   postprocess = (uu___428_14955.postprocess);
                                   is_native_tactic =
                                     (uu___428_14955.is_native_tactic);
                                   identifier_info =
                                     (uu___428_14955.identifier_info);
                                   tc_hooks = (uu___428_14955.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___428_14955.nbe);
                                   strict_args_tab =
                                     (uu___428_14955.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___428_14955.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14989  ->
             let uu____14990 =
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
             match uu____14990 with
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
                             ((let uu____15170 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15170
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15186 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15186
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15218,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15260 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15290  ->
                  match uu____15290 with
                  | (m,uu____15298) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15260 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___473_15313 = env  in
               {
                 solver = (uu___473_15313.solver);
                 range = (uu___473_15313.range);
                 curmodule = (uu___473_15313.curmodule);
                 gamma = (uu___473_15313.gamma);
                 gamma_sig = (uu___473_15313.gamma_sig);
                 gamma_cache = (uu___473_15313.gamma_cache);
                 modules = (uu___473_15313.modules);
                 expected_typ = (uu___473_15313.expected_typ);
                 sigtab = (uu___473_15313.sigtab);
                 attrtab = (uu___473_15313.attrtab);
                 is_pattern = (uu___473_15313.is_pattern);
                 instantiate_imp = (uu___473_15313.instantiate_imp);
                 effects = (uu___473_15313.effects);
                 generalize = (uu___473_15313.generalize);
                 letrecs = (uu___473_15313.letrecs);
                 top_level = (uu___473_15313.top_level);
                 check_uvars = (uu___473_15313.check_uvars);
                 use_eq = (uu___473_15313.use_eq);
                 is_iface = (uu___473_15313.is_iface);
                 admit = (uu___473_15313.admit);
                 lax = (uu___473_15313.lax);
                 lax_universes = (uu___473_15313.lax_universes);
                 phase1 = (uu___473_15313.phase1);
                 failhard = (uu___473_15313.failhard);
                 nosynth = (uu___473_15313.nosynth);
                 uvar_subtyping = (uu___473_15313.uvar_subtyping);
                 tc_term = (uu___473_15313.tc_term);
                 type_of = (uu___473_15313.type_of);
                 universe_of = (uu___473_15313.universe_of);
                 check_type_of = (uu___473_15313.check_type_of);
                 use_bv_sorts = (uu___473_15313.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___473_15313.normalized_eff_names);
                 fv_delta_depths = (uu___473_15313.fv_delta_depths);
                 proof_ns = (uu___473_15313.proof_ns);
                 synth_hook = (uu___473_15313.synth_hook);
                 try_solve_implicits_hook =
                   (uu___473_15313.try_solve_implicits_hook);
                 splice = (uu___473_15313.splice);
                 postprocess = (uu___473_15313.postprocess);
                 is_native_tactic = (uu___473_15313.is_native_tactic);
                 identifier_info = (uu___473_15313.identifier_info);
                 tc_hooks = (uu___473_15313.tc_hooks);
                 dsenv = (uu___473_15313.dsenv);
                 nbe = (uu___473_15313.nbe);
                 strict_args_tab = (uu___473_15313.strict_args_tab);
                 erasable_types_tab = (uu___473_15313.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15330,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___482_15346 = env  in
               {
                 solver = (uu___482_15346.solver);
                 range = (uu___482_15346.range);
                 curmodule = (uu___482_15346.curmodule);
                 gamma = (uu___482_15346.gamma);
                 gamma_sig = (uu___482_15346.gamma_sig);
                 gamma_cache = (uu___482_15346.gamma_cache);
                 modules = (uu___482_15346.modules);
                 expected_typ = (uu___482_15346.expected_typ);
                 sigtab = (uu___482_15346.sigtab);
                 attrtab = (uu___482_15346.attrtab);
                 is_pattern = (uu___482_15346.is_pattern);
                 instantiate_imp = (uu___482_15346.instantiate_imp);
                 effects = (uu___482_15346.effects);
                 generalize = (uu___482_15346.generalize);
                 letrecs = (uu___482_15346.letrecs);
                 top_level = (uu___482_15346.top_level);
                 check_uvars = (uu___482_15346.check_uvars);
                 use_eq = (uu___482_15346.use_eq);
                 is_iface = (uu___482_15346.is_iface);
                 admit = (uu___482_15346.admit);
                 lax = (uu___482_15346.lax);
                 lax_universes = (uu___482_15346.lax_universes);
                 phase1 = (uu___482_15346.phase1);
                 failhard = (uu___482_15346.failhard);
                 nosynth = (uu___482_15346.nosynth);
                 uvar_subtyping = (uu___482_15346.uvar_subtyping);
                 tc_term = (uu___482_15346.tc_term);
                 type_of = (uu___482_15346.type_of);
                 universe_of = (uu___482_15346.universe_of);
                 check_type_of = (uu___482_15346.check_type_of);
                 use_bv_sorts = (uu___482_15346.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___482_15346.normalized_eff_names);
                 fv_delta_depths = (uu___482_15346.fv_delta_depths);
                 proof_ns = (uu___482_15346.proof_ns);
                 synth_hook = (uu___482_15346.synth_hook);
                 try_solve_implicits_hook =
                   (uu___482_15346.try_solve_implicits_hook);
                 splice = (uu___482_15346.splice);
                 postprocess = (uu___482_15346.postprocess);
                 is_native_tactic = (uu___482_15346.is_native_tactic);
                 identifier_info = (uu___482_15346.identifier_info);
                 tc_hooks = (uu___482_15346.tc_hooks);
                 dsenv = (uu___482_15346.dsenv);
                 nbe = (uu___482_15346.nbe);
                 strict_args_tab = (uu___482_15346.strict_args_tab);
                 erasable_types_tab = (uu___482_15346.erasable_types_tab)
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
        (let uu___489_15389 = e  in
         {
           solver = (uu___489_15389.solver);
           range = r;
           curmodule = (uu___489_15389.curmodule);
           gamma = (uu___489_15389.gamma);
           gamma_sig = (uu___489_15389.gamma_sig);
           gamma_cache = (uu___489_15389.gamma_cache);
           modules = (uu___489_15389.modules);
           expected_typ = (uu___489_15389.expected_typ);
           sigtab = (uu___489_15389.sigtab);
           attrtab = (uu___489_15389.attrtab);
           is_pattern = (uu___489_15389.is_pattern);
           instantiate_imp = (uu___489_15389.instantiate_imp);
           effects = (uu___489_15389.effects);
           generalize = (uu___489_15389.generalize);
           letrecs = (uu___489_15389.letrecs);
           top_level = (uu___489_15389.top_level);
           check_uvars = (uu___489_15389.check_uvars);
           use_eq = (uu___489_15389.use_eq);
           is_iface = (uu___489_15389.is_iface);
           admit = (uu___489_15389.admit);
           lax = (uu___489_15389.lax);
           lax_universes = (uu___489_15389.lax_universes);
           phase1 = (uu___489_15389.phase1);
           failhard = (uu___489_15389.failhard);
           nosynth = (uu___489_15389.nosynth);
           uvar_subtyping = (uu___489_15389.uvar_subtyping);
           tc_term = (uu___489_15389.tc_term);
           type_of = (uu___489_15389.type_of);
           universe_of = (uu___489_15389.universe_of);
           check_type_of = (uu___489_15389.check_type_of);
           use_bv_sorts = (uu___489_15389.use_bv_sorts);
           qtbl_name_and_index = (uu___489_15389.qtbl_name_and_index);
           normalized_eff_names = (uu___489_15389.normalized_eff_names);
           fv_delta_depths = (uu___489_15389.fv_delta_depths);
           proof_ns = (uu___489_15389.proof_ns);
           synth_hook = (uu___489_15389.synth_hook);
           try_solve_implicits_hook =
             (uu___489_15389.try_solve_implicits_hook);
           splice = (uu___489_15389.splice);
           postprocess = (uu___489_15389.postprocess);
           is_native_tactic = (uu___489_15389.is_native_tactic);
           identifier_info = (uu___489_15389.identifier_info);
           tc_hooks = (uu___489_15389.tc_hooks);
           dsenv = (uu___489_15389.dsenv);
           nbe = (uu___489_15389.nbe);
           strict_args_tab = (uu___489_15389.strict_args_tab);
           erasable_types_tab = (uu___489_15389.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15409 =
        let uu____15410 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15410 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15409
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15465 =
          let uu____15466 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15466 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15465
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15521 =
          let uu____15522 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15522 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15521
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15577 =
        let uu____15578 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15578 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15577
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___506_15642 = env  in
      {
        solver = (uu___506_15642.solver);
        range = (uu___506_15642.range);
        curmodule = lid;
        gamma = (uu___506_15642.gamma);
        gamma_sig = (uu___506_15642.gamma_sig);
        gamma_cache = (uu___506_15642.gamma_cache);
        modules = (uu___506_15642.modules);
        expected_typ = (uu___506_15642.expected_typ);
        sigtab = (uu___506_15642.sigtab);
        attrtab = (uu___506_15642.attrtab);
        is_pattern = (uu___506_15642.is_pattern);
        instantiate_imp = (uu___506_15642.instantiate_imp);
        effects = (uu___506_15642.effects);
        generalize = (uu___506_15642.generalize);
        letrecs = (uu___506_15642.letrecs);
        top_level = (uu___506_15642.top_level);
        check_uvars = (uu___506_15642.check_uvars);
        use_eq = (uu___506_15642.use_eq);
        is_iface = (uu___506_15642.is_iface);
        admit = (uu___506_15642.admit);
        lax = (uu___506_15642.lax);
        lax_universes = (uu___506_15642.lax_universes);
        phase1 = (uu___506_15642.phase1);
        failhard = (uu___506_15642.failhard);
        nosynth = (uu___506_15642.nosynth);
        uvar_subtyping = (uu___506_15642.uvar_subtyping);
        tc_term = (uu___506_15642.tc_term);
        type_of = (uu___506_15642.type_of);
        universe_of = (uu___506_15642.universe_of);
        check_type_of = (uu___506_15642.check_type_of);
        use_bv_sorts = (uu___506_15642.use_bv_sorts);
        qtbl_name_and_index = (uu___506_15642.qtbl_name_and_index);
        normalized_eff_names = (uu___506_15642.normalized_eff_names);
        fv_delta_depths = (uu___506_15642.fv_delta_depths);
        proof_ns = (uu___506_15642.proof_ns);
        synth_hook = (uu___506_15642.synth_hook);
        try_solve_implicits_hook = (uu___506_15642.try_solve_implicits_hook);
        splice = (uu___506_15642.splice);
        postprocess = (uu___506_15642.postprocess);
        is_native_tactic = (uu___506_15642.is_native_tactic);
        identifier_info = (uu___506_15642.identifier_info);
        tc_hooks = (uu___506_15642.tc_hooks);
        dsenv = (uu___506_15642.dsenv);
        nbe = (uu___506_15642.nbe);
        strict_args_tab = (uu___506_15642.strict_args_tab);
        erasable_types_tab = (uu___506_15642.erasable_types_tab)
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
      let uu____15673 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15673
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15686 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15686)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15701 =
      let uu____15703 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15703  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15701)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15712  ->
    let uu____15713 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15713
  
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
      | ((formals,t),uu____15813) ->
          let vs = mk_univ_subst formals us  in
          let uu____15837 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15837)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15854  ->
    match uu___1_15854 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15880  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15900 = inst_tscheme t  in
      match uu____15900 with
      | (us,t1) ->
          let uu____15911 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15911)
  
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
          let uu____15936 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15938 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15936 uu____15938
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
        fun uu____15965  ->
          match uu____15965 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15979 =
                    let uu____15981 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15985 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15989 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15991 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15981 uu____15985 uu____15989 uu____15991
                     in
                  failwith uu____15979)
               else ();
               (let uu____15996 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15996))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16014 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16025 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16036 -> false
  
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
             | ([],uu____16084) -> Maybe
             | (uu____16091,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16111 -> No  in
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
          let uu____16205 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16205 with
          | FStar_Pervasives_Native.None  ->
              let uu____16228 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16272  ->
                     match uu___2_16272 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16311 = FStar_Ident.lid_equals lid l  in
                         if uu____16311
                         then
                           let uu____16334 =
                             let uu____16353 =
                               let uu____16368 = inst_tscheme t  in
                               FStar_Util.Inl uu____16368  in
                             let uu____16383 = FStar_Ident.range_of_lid l  in
                             (uu____16353, uu____16383)  in
                           FStar_Pervasives_Native.Some uu____16334
                         else FStar_Pervasives_Native.None
                     | uu____16436 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16228
                (fun uu____16474  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16483  ->
                        match uu___3_16483 with
                        | (uu____16486,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16488);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16489;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16490;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16491;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16492;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16512 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16512
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
                                  uu____16564 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16571 -> cache t  in
                            let uu____16572 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16572 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16578 =
                                   let uu____16579 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16579)
                                    in
                                 maybe_cache uu____16578)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16650 = find_in_sigtab env lid  in
         match uu____16650 with
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
      let uu____16731 = lookup_qname env lid  in
      match uu____16731 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16752,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16866 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16866 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16911 =
          let uu____16914 = lookup_attr env1 attr  in se1 :: uu____16914  in
        FStar_Util.smap_add (attrtab env1) attr uu____16911  in
      FStar_List.iter
        (fun attr  ->
           let uu____16924 =
             let uu____16925 = FStar_Syntax_Subst.compress attr  in
             uu____16925.FStar_Syntax_Syntax.n  in
           match uu____16924 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16929 =
                 let uu____16931 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16931.FStar_Ident.str  in
               add_one1 env se uu____16929
           | uu____16932 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16955) ->
          add_sigelts env ses
      | uu____16964 ->
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
        (fun uu___4_17002  ->
           match uu___4_17002 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17020 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17082,lb::[]),uu____17084) ->
            let uu____17093 =
              let uu____17102 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17111 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17102, uu____17111)  in
            FStar_Pervasives_Native.Some uu____17093
        | FStar_Syntax_Syntax.Sig_let ((uu____17124,lbs),uu____17126) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17158 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17171 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17171
                     then
                       let uu____17184 =
                         let uu____17193 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17202 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17193, uu____17202)  in
                       FStar_Pervasives_Native.Some uu____17184
                     else FStar_Pervasives_Native.None)
        | uu____17225 -> FStar_Pervasives_Native.None
  
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
                    let uu____17317 =
                      let uu____17319 =
                        let uu____17321 =
                          let uu____17323 =
                            let uu____17325 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17331 =
                              let uu____17333 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17333  in
                            Prims.op_Hat uu____17325 uu____17331  in
                          Prims.op_Hat ", expected " uu____17323  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17321
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17319
                       in
                    failwith uu____17317
                  else ());
             (let uu____17340 =
                let uu____17349 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17349, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17340))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17369,uu____17370) ->
            let uu____17375 =
              let uu____17384 =
                let uu____17389 =
                  let uu____17390 =
                    let uu____17393 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17393  in
                  (us, uu____17390)  in
                inst_ts us_opt uu____17389  in
              (uu____17384, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17375
        | uu____17412 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17501 =
          match uu____17501 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17597,uvs,t,uu____17600,uu____17601,uu____17602);
                      FStar_Syntax_Syntax.sigrng = uu____17603;
                      FStar_Syntax_Syntax.sigquals = uu____17604;
                      FStar_Syntax_Syntax.sigmeta = uu____17605;
                      FStar_Syntax_Syntax.sigattrs = uu____17606;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17629 =
                     let uu____17638 = inst_tscheme1 (uvs, t)  in
                     (uu____17638, rng)  in
                   FStar_Pervasives_Native.Some uu____17629
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17662;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17664;
                      FStar_Syntax_Syntax.sigattrs = uu____17665;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17682 =
                     let uu____17684 = in_cur_mod env l  in uu____17684 = Yes
                      in
                   if uu____17682
                   then
                     let uu____17696 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17696
                      then
                        let uu____17712 =
                          let uu____17721 = inst_tscheme1 (uvs, t)  in
                          (uu____17721, rng)  in
                        FStar_Pervasives_Native.Some uu____17712
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17754 =
                        let uu____17763 = inst_tscheme1 (uvs, t)  in
                        (uu____17763, rng)  in
                      FStar_Pervasives_Native.Some uu____17754)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17788,uu____17789);
                      FStar_Syntax_Syntax.sigrng = uu____17790;
                      FStar_Syntax_Syntax.sigquals = uu____17791;
                      FStar_Syntax_Syntax.sigmeta = uu____17792;
                      FStar_Syntax_Syntax.sigattrs = uu____17793;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17834 =
                          let uu____17843 = inst_tscheme1 (uvs, k)  in
                          (uu____17843, rng)  in
                        FStar_Pervasives_Native.Some uu____17834
                    | uu____17864 ->
                        let uu____17865 =
                          let uu____17874 =
                            let uu____17879 =
                              let uu____17880 =
                                let uu____17883 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17883
                                 in
                              (uvs, uu____17880)  in
                            inst_tscheme1 uu____17879  in
                          (uu____17874, rng)  in
                        FStar_Pervasives_Native.Some uu____17865)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17906,uu____17907);
                      FStar_Syntax_Syntax.sigrng = uu____17908;
                      FStar_Syntax_Syntax.sigquals = uu____17909;
                      FStar_Syntax_Syntax.sigmeta = uu____17910;
                      FStar_Syntax_Syntax.sigattrs = uu____17911;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17953 =
                          let uu____17962 = inst_tscheme_with (uvs, k) us  in
                          (uu____17962, rng)  in
                        FStar_Pervasives_Native.Some uu____17953
                    | uu____17983 ->
                        let uu____17984 =
                          let uu____17993 =
                            let uu____17998 =
                              let uu____17999 =
                                let uu____18002 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18002
                                 in
                              (uvs, uu____17999)  in
                            inst_tscheme_with uu____17998 us  in
                          (uu____17993, rng)  in
                        FStar_Pervasives_Native.Some uu____17984)
               | FStar_Util.Inr se ->
                   let uu____18038 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18059;
                          FStar_Syntax_Syntax.sigrng = uu____18060;
                          FStar_Syntax_Syntax.sigquals = uu____18061;
                          FStar_Syntax_Syntax.sigmeta = uu____18062;
                          FStar_Syntax_Syntax.sigattrs = uu____18063;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18078 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18038
                     (FStar_Util.map_option
                        (fun uu____18126  ->
                           match uu____18126 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18157 =
          let uu____18168 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18168 mapper  in
        match uu____18157 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18242 =
              let uu____18253 =
                let uu____18260 =
                  let uu___837_18263 = t  in
                  let uu____18264 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___837_18263.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18264;
                    FStar_Syntax_Syntax.vars =
                      (uu___837_18263.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18260)  in
              (uu____18253, r)  in
            FStar_Pervasives_Native.Some uu____18242
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18313 = lookup_qname env l  in
      match uu____18313 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18334 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18388 = try_lookup_bv env bv  in
      match uu____18388 with
      | FStar_Pervasives_Native.None  ->
          let uu____18403 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18403 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18419 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18420 =
            let uu____18421 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18421  in
          (uu____18419, uu____18420)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18443 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18443 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18509 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18509  in
          let uu____18510 =
            let uu____18519 =
              let uu____18524 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18524)  in
            (uu____18519, r1)  in
          FStar_Pervasives_Native.Some uu____18510
  
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
        let uu____18559 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18559 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18592,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18617 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18617  in
            let uu____18618 =
              let uu____18623 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18623, r1)  in
            FStar_Pervasives_Native.Some uu____18618
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18647 = try_lookup_lid env l  in
      match uu____18647 with
      | FStar_Pervasives_Native.None  ->
          let uu____18674 = name_not_found l  in
          let uu____18680 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18674 uu____18680
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18723  ->
              match uu___5_18723 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18727 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18748 = lookup_qname env lid  in
      match uu____18748 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18757,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18760;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18762;
              FStar_Syntax_Syntax.sigattrs = uu____18763;_},FStar_Pervasives_Native.None
            ),uu____18764)
          ->
          let uu____18813 =
            let uu____18820 =
              let uu____18821 =
                let uu____18824 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18824 t  in
              (uvs, uu____18821)  in
            (uu____18820, q)  in
          FStar_Pervasives_Native.Some uu____18813
      | uu____18837 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18859 = lookup_qname env lid  in
      match uu____18859 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18864,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18867;
              FStar_Syntax_Syntax.sigquals = uu____18868;
              FStar_Syntax_Syntax.sigmeta = uu____18869;
              FStar_Syntax_Syntax.sigattrs = uu____18870;_},FStar_Pervasives_Native.None
            ),uu____18871)
          ->
          let uu____18920 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18920 (uvs, t)
      | uu____18925 ->
          let uu____18926 = name_not_found lid  in
          let uu____18932 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18926 uu____18932
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18952 = lookup_qname env lid  in
      match uu____18952 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18957,uvs,t,uu____18960,uu____18961,uu____18962);
              FStar_Syntax_Syntax.sigrng = uu____18963;
              FStar_Syntax_Syntax.sigquals = uu____18964;
              FStar_Syntax_Syntax.sigmeta = uu____18965;
              FStar_Syntax_Syntax.sigattrs = uu____18966;_},FStar_Pervasives_Native.None
            ),uu____18967)
          ->
          let uu____19022 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19022 (uvs, t)
      | uu____19027 ->
          let uu____19028 = name_not_found lid  in
          let uu____19034 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19028 uu____19034
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19057 = lookup_qname env lid  in
      match uu____19057 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19065,uu____19066,uu____19067,uu____19068,uu____19069,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19071;
              FStar_Syntax_Syntax.sigquals = uu____19072;
              FStar_Syntax_Syntax.sigmeta = uu____19073;
              FStar_Syntax_Syntax.sigattrs = uu____19074;_},uu____19075),uu____19076)
          -> (true, dcs)
      | uu____19139 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19155 = lookup_qname env lid  in
      match uu____19155 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19156,uu____19157,uu____19158,l,uu____19160,uu____19161);
              FStar_Syntax_Syntax.sigrng = uu____19162;
              FStar_Syntax_Syntax.sigquals = uu____19163;
              FStar_Syntax_Syntax.sigmeta = uu____19164;
              FStar_Syntax_Syntax.sigattrs = uu____19165;_},uu____19166),uu____19167)
          -> l
      | uu____19224 ->
          let uu____19225 =
            let uu____19227 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19227  in
          failwith uu____19225
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19297)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19354) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19378 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19378
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19413 -> FStar_Pervasives_Native.None)
          | uu____19422 -> FStar_Pervasives_Native.None
  
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
        let uu____19484 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19484
  
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
        let uu____19517 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19517
  
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
             (FStar_Util.Inl uu____19569,uu____19570) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19619),uu____19620) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19669 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19687 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19697 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19714 ->
                  let uu____19721 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19721
              | FStar_Syntax_Syntax.Sig_let ((uu____19722,lbs),uu____19724)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19740 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19740
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19747 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19755 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19756 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19763 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19764 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19765 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19766 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19779 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19797 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19797
           (fun d_opt  ->
              let uu____19810 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19810
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19820 =
                   let uu____19823 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19823  in
                 match uu____19820 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19824 =
                       let uu____19826 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19826
                        in
                     failwith uu____19824
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19831 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19831
                       then
                         let uu____19834 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19836 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19838 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19834 uu____19836 uu____19838
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
        (FStar_Util.Inr (se,uu____19863),uu____19864) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19913 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19935),uu____19936) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19985 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20007 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20007
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20040 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20040 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20062 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20071 =
                        let uu____20072 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20072.FStar_Syntax_Syntax.n  in
                      match uu____20071 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20077 -> false))
               in
            (true, uu____20062)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20100 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20100
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let cache_in_fv_tab :
  'a .
    'a FStar_Util.smap ->
      FStar_Syntax_Syntax.fv -> (unit -> (Prims.bool * 'a)) -> 'a
  =
  fun tab  ->
    fun fv  ->
      fun f  ->
        let s =
          let uu____20172 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20172.FStar_Ident.str  in
        let uu____20173 = FStar_Util.smap_try_find tab s  in
        match uu____20173 with
        | FStar_Pervasives_Native.None  ->
            let uu____20176 = f ()  in
            (match uu____20176 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20214 =
        let uu____20215 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20215 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20249 =
        let uu____20250 = FStar_Syntax_Util.unrefine t  in
        uu____20250.FStar_Syntax_Syntax.n  in
      match uu____20249 with
      | FStar_Syntax_Syntax.Tm_type uu____20254 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20258) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20284) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20289,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20311 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20344 =
        let attrs =
          let uu____20350 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20350  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20390 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20390)
               in
            (true, res)
         in
      cache_in_fv_tab env.strict_args_tab fv f
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____20435 = lookup_qname env ftv  in
      match uu____20435 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20439) ->
          let uu____20484 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20484 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20505,t),r) ->
               let uu____20520 =
                 let uu____20521 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20521 t  in
               FStar_Pervasives_Native.Some uu____20520)
      | uu____20522 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20534 = try_lookup_effect_lid env ftv  in
      match uu____20534 with
      | FStar_Pervasives_Native.None  ->
          let uu____20537 = name_not_found ftv  in
          let uu____20543 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20537 uu____20543
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
        let uu____20567 = lookup_qname env lid0  in
        match uu____20567 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20578);
                FStar_Syntax_Syntax.sigrng = uu____20579;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20581;
                FStar_Syntax_Syntax.sigattrs = uu____20582;_},FStar_Pervasives_Native.None
              ),uu____20583)
            ->
            let lid1 =
              let uu____20637 =
                let uu____20638 = FStar_Ident.range_of_lid lid  in
                let uu____20639 =
                  let uu____20640 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20640  in
                FStar_Range.set_use_range uu____20638 uu____20639  in
              FStar_Ident.set_lid_range lid uu____20637  in
            let uu____20641 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20647  ->
                      match uu___6_20647 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20650 -> false))
               in
            if uu____20641
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20669 =
                      let uu____20671 =
                        let uu____20673 = get_range env  in
                        FStar_Range.string_of_range uu____20673  in
                      let uu____20674 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20676 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20671 uu____20674 uu____20676
                       in
                    failwith uu____20669)
                  in
               match (binders, univs1) with
               | ([],uu____20697) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20723,uu____20724::uu____20725::uu____20726) ->
                   let uu____20747 =
                     let uu____20749 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20751 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20749 uu____20751
                      in
                   failwith uu____20747
               | uu____20762 ->
                   let uu____20777 =
                     let uu____20782 =
                       let uu____20783 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20783)  in
                     inst_tscheme_with uu____20782 insts  in
                   (match uu____20777 with
                    | (uu____20796,t) ->
                        let t1 =
                          let uu____20799 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20799 t  in
                        let uu____20800 =
                          let uu____20801 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20801.FStar_Syntax_Syntax.n  in
                        (match uu____20800 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20836 -> failwith "Impossible")))
        | uu____20844 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20868 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20868 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20881,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20888 = find1 l2  in
            (match uu____20888 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20895 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20895 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20899 = find1 l  in
            (match uu____20899 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20904 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20904
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____20925 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____20925 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____20931) ->
            FStar_List.length bs
        | uu____20970 ->
            let uu____20971 =
              let uu____20977 =
                let uu____20979 = FStar_Ident.string_of_lid name  in
                let uu____20981 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20979 uu____20981
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20977)
               in
            FStar_Errors.raise_error uu____20971 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21000 = lookup_qname env l1  in
      match uu____21000 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21003;
              FStar_Syntax_Syntax.sigrng = uu____21004;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21006;
              FStar_Syntax_Syntax.sigattrs = uu____21007;_},uu____21008),uu____21009)
          -> q
      | uu____21060 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21084 =
          let uu____21085 =
            let uu____21087 = FStar_Util.string_of_int i  in
            let uu____21089 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21087 uu____21089
             in
          failwith uu____21085  in
        let uu____21092 = lookup_datacon env lid  in
        match uu____21092 with
        | (uu____21097,t) ->
            let uu____21099 =
              let uu____21100 = FStar_Syntax_Subst.compress t  in
              uu____21100.FStar_Syntax_Syntax.n  in
            (match uu____21099 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21104) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21148 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21148
                      FStar_Pervasives_Native.fst)
             | uu____21159 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21173 = lookup_qname env l  in
      match uu____21173 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21175,uu____21176,uu____21177);
              FStar_Syntax_Syntax.sigrng = uu____21178;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21180;
              FStar_Syntax_Syntax.sigattrs = uu____21181;_},uu____21182),uu____21183)
          ->
          FStar_Util.for_some
            (fun uu___7_21236  ->
               match uu___7_21236 with
               | FStar_Syntax_Syntax.Projector uu____21238 -> true
               | uu____21244 -> false) quals
      | uu____21246 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21260 = lookup_qname env lid  in
      match uu____21260 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21262,uu____21263,uu____21264,uu____21265,uu____21266,uu____21267);
              FStar_Syntax_Syntax.sigrng = uu____21268;
              FStar_Syntax_Syntax.sigquals = uu____21269;
              FStar_Syntax_Syntax.sigmeta = uu____21270;
              FStar_Syntax_Syntax.sigattrs = uu____21271;_},uu____21272),uu____21273)
          -> true
      | uu____21331 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21345 = lookup_qname env lid  in
      match uu____21345 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21347,uu____21348,uu____21349,uu____21350,uu____21351,uu____21352);
              FStar_Syntax_Syntax.sigrng = uu____21353;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21355;
              FStar_Syntax_Syntax.sigattrs = uu____21356;_},uu____21357),uu____21358)
          ->
          FStar_Util.for_some
            (fun uu___8_21419  ->
               match uu___8_21419 with
               | FStar_Syntax_Syntax.RecordType uu____21421 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21431 -> true
               | uu____21441 -> false) quals
      | uu____21443 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21453,uu____21454);
            FStar_Syntax_Syntax.sigrng = uu____21455;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21457;
            FStar_Syntax_Syntax.sigattrs = uu____21458;_},uu____21459),uu____21460)
        ->
        FStar_Util.for_some
          (fun uu___9_21517  ->
             match uu___9_21517 with
             | FStar_Syntax_Syntax.Action uu____21519 -> true
             | uu____21521 -> false) quals
    | uu____21523 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21537 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21537
  
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
      let uu____21554 =
        let uu____21555 = FStar_Syntax_Util.un_uinst head1  in
        uu____21555.FStar_Syntax_Syntax.n  in
      match uu____21554 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21561 ->
               true
           | uu____21564 -> false)
      | uu____21566 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21580 = lookup_qname env l  in
      match uu____21580 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21583),uu____21584) ->
          FStar_Util.for_some
            (fun uu___10_21632  ->
               match uu___10_21632 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21635 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21637 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21713 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21731) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21749 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21757 ->
                 FStar_Pervasives_Native.Some true
             | uu____21776 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21779 =
        let uu____21783 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21783 mapper  in
      match uu____21779 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21843 = lookup_qname env lid  in
      match uu____21843 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21847,uu____21848,tps,uu____21850,uu____21851,uu____21852);
              FStar_Syntax_Syntax.sigrng = uu____21853;
              FStar_Syntax_Syntax.sigquals = uu____21854;
              FStar_Syntax_Syntax.sigmeta = uu____21855;
              FStar_Syntax_Syntax.sigattrs = uu____21856;_},uu____21857),uu____21858)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21924 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21970  ->
              match uu____21970 with
              | (d,uu____21979) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21995 = effect_decl_opt env l  in
      match uu____21995 with
      | FStar_Pervasives_Native.None  ->
          let uu____22010 = name_not_found l  in
          let uu____22016 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22010 uu____22016
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22044 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____22044
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22053  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22067  ->
            fun uu____22068  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22098 = FStar_Ident.lid_equals l1 l2  in
        if uu____22098
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____22109 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22109
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____22120 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22173  ->
                        match uu____22173 with
                        | (m1,m2,uu____22187,uu____22188,uu____22189) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22120 with
              | FStar_Pervasives_Native.None  ->
                  let uu____22206 =
                    let uu____22212 =
                      let uu____22214 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____22216 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____22214
                        uu____22216
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22212)
                     in
                  FStar_Errors.raise_error uu____22206 env.range
              | FStar_Pervasives_Native.Some
                  (uu____22226,uu____22227,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22261 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22261
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
  'Auu____22281 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22281) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22310 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22336  ->
                match uu____22336 with
                | (d,uu____22343) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22310 with
      | FStar_Pervasives_Native.None  ->
          let uu____22354 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22354
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22369 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22369 with
           | (uu____22380,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22398)::(wp,uu____22400)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22456 -> failwith "Impossible"))
  
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
        | uu____22521 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22534 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22534 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22551 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22551 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22576 =
                     let uu____22582 =
                       let uu____22584 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22592 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22603 =
                         let uu____22605 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22605  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22584 uu____22592 uu____22603
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22582)
                      in
                   FStar_Errors.raise_error uu____22576
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22613 =
                     let uu____22624 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22624 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22661  ->
                        fun uu____22662  ->
                          match (uu____22661, uu____22662) with
                          | ((x,uu____22692),(t,uu____22694)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22613
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22725 =
                     let uu___1574_22726 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1574_22726.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1574_22726.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1574_22726.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1574_22726.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22725
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22738 .
    'Auu____22738 ->
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
            let uu____22779 =
              let uu____22786 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____22786)  in
            match uu____22779 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____22810 = FStar_Ident.string_of_lid eff_name  in
                     let uu____22812 = FStar_Util.string_of_int given  in
                     let uu____22814 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____22810 uu____22812 uu____22814
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____22819 = effect_decl_opt env effect_name  in
          match uu____22819 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____22841) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22862 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr =
                     inst_effect_fun_with [u_res] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____22869 =
                       let uu____22872 = get_range env  in
                       let uu____22873 =
                         let uu____22880 =
                           let uu____22881 =
                             let uu____22898 =
                               let uu____22909 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____22909 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____22898)  in
                           FStar_Syntax_Syntax.Tm_app uu____22881  in
                         FStar_Syntax_Syntax.mk uu____22880  in
                       uu____22873 FStar_Pervasives_Native.None uu____22872
                        in
                     FStar_Pervasives_Native.Some uu____22869)))
  
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
  
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_All.pipe_right quals
        (FStar_List.existsb
           (fun uu___11_23009  ->
              match uu___11_23009 with
              | FStar_Syntax_Syntax.Reflectable uu____23011 -> true
              | uu____23013 -> false))
  
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
      | uu____23073 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23088 =
        let uu____23089 = FStar_Syntax_Subst.compress t  in
        uu____23089.FStar_Syntax_Syntax.n  in
      match uu____23088 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23093,c) ->
          is_reifiable_comp env c
      | uu____23115 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23135 =
           let uu____23137 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23137  in
         if uu____23135
         then
           let uu____23140 =
             let uu____23146 =
               let uu____23148 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23148
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23146)  in
           let uu____23152 = get_range env  in
           FStar_Errors.raise_error uu____23140 uu____23152
         else ());
        (let uu____23155 = effect_repr_aux true env c u_c  in
         match uu____23155 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1650_23191 = env  in
        {
          solver = (uu___1650_23191.solver);
          range = (uu___1650_23191.range);
          curmodule = (uu___1650_23191.curmodule);
          gamma = (uu___1650_23191.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1650_23191.gamma_cache);
          modules = (uu___1650_23191.modules);
          expected_typ = (uu___1650_23191.expected_typ);
          sigtab = (uu___1650_23191.sigtab);
          attrtab = (uu___1650_23191.attrtab);
          is_pattern = (uu___1650_23191.is_pattern);
          instantiate_imp = (uu___1650_23191.instantiate_imp);
          effects = (uu___1650_23191.effects);
          generalize = (uu___1650_23191.generalize);
          letrecs = (uu___1650_23191.letrecs);
          top_level = (uu___1650_23191.top_level);
          check_uvars = (uu___1650_23191.check_uvars);
          use_eq = (uu___1650_23191.use_eq);
          is_iface = (uu___1650_23191.is_iface);
          admit = (uu___1650_23191.admit);
          lax = (uu___1650_23191.lax);
          lax_universes = (uu___1650_23191.lax_universes);
          phase1 = (uu___1650_23191.phase1);
          failhard = (uu___1650_23191.failhard);
          nosynth = (uu___1650_23191.nosynth);
          uvar_subtyping = (uu___1650_23191.uvar_subtyping);
          tc_term = (uu___1650_23191.tc_term);
          type_of = (uu___1650_23191.type_of);
          universe_of = (uu___1650_23191.universe_of);
          check_type_of = (uu___1650_23191.check_type_of);
          use_bv_sorts = (uu___1650_23191.use_bv_sorts);
          qtbl_name_and_index = (uu___1650_23191.qtbl_name_and_index);
          normalized_eff_names = (uu___1650_23191.normalized_eff_names);
          fv_delta_depths = (uu___1650_23191.fv_delta_depths);
          proof_ns = (uu___1650_23191.proof_ns);
          synth_hook = (uu___1650_23191.synth_hook);
          try_solve_implicits_hook =
            (uu___1650_23191.try_solve_implicits_hook);
          splice = (uu___1650_23191.splice);
          postprocess = (uu___1650_23191.postprocess);
          is_native_tactic = (uu___1650_23191.is_native_tactic);
          identifier_info = (uu___1650_23191.identifier_info);
          tc_hooks = (uu___1650_23191.tc_hooks);
          dsenv = (uu___1650_23191.dsenv);
          nbe = (uu___1650_23191.nbe);
          strict_args_tab = (uu___1650_23191.strict_args_tab);
          erasable_types_tab = (uu___1650_23191.erasable_types_tab)
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
    fun uu____23210  ->
      match uu____23210 with
      | (ed,quals) ->
          let effects =
            let uu___1659_23224 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1659_23224.order);
              joins = (uu___1659_23224.joins)
            }  in
          let uu___1662_23233 = env  in
          {
            solver = (uu___1662_23233.solver);
            range = (uu___1662_23233.range);
            curmodule = (uu___1662_23233.curmodule);
            gamma = (uu___1662_23233.gamma);
            gamma_sig = (uu___1662_23233.gamma_sig);
            gamma_cache = (uu___1662_23233.gamma_cache);
            modules = (uu___1662_23233.modules);
            expected_typ = (uu___1662_23233.expected_typ);
            sigtab = (uu___1662_23233.sigtab);
            attrtab = (uu___1662_23233.attrtab);
            is_pattern = (uu___1662_23233.is_pattern);
            instantiate_imp = (uu___1662_23233.instantiate_imp);
            effects;
            generalize = (uu___1662_23233.generalize);
            letrecs = (uu___1662_23233.letrecs);
            top_level = (uu___1662_23233.top_level);
            check_uvars = (uu___1662_23233.check_uvars);
            use_eq = (uu___1662_23233.use_eq);
            is_iface = (uu___1662_23233.is_iface);
            admit = (uu___1662_23233.admit);
            lax = (uu___1662_23233.lax);
            lax_universes = (uu___1662_23233.lax_universes);
            phase1 = (uu___1662_23233.phase1);
            failhard = (uu___1662_23233.failhard);
            nosynth = (uu___1662_23233.nosynth);
            uvar_subtyping = (uu___1662_23233.uvar_subtyping);
            tc_term = (uu___1662_23233.tc_term);
            type_of = (uu___1662_23233.type_of);
            universe_of = (uu___1662_23233.universe_of);
            check_type_of = (uu___1662_23233.check_type_of);
            use_bv_sorts = (uu___1662_23233.use_bv_sorts);
            qtbl_name_and_index = (uu___1662_23233.qtbl_name_and_index);
            normalized_eff_names = (uu___1662_23233.normalized_eff_names);
            fv_delta_depths = (uu___1662_23233.fv_delta_depths);
            proof_ns = (uu___1662_23233.proof_ns);
            synth_hook = (uu___1662_23233.synth_hook);
            try_solve_implicits_hook =
              (uu___1662_23233.try_solve_implicits_hook);
            splice = (uu___1662_23233.splice);
            postprocess = (uu___1662_23233.postprocess);
            is_native_tactic = (uu___1662_23233.is_native_tactic);
            identifier_info = (uu___1662_23233.identifier_info);
            tc_hooks = (uu___1662_23233.tc_hooks);
            dsenv = (uu___1662_23233.dsenv);
            nbe = (uu___1662_23233.nbe);
            strict_args_tab = (uu___1662_23233.strict_args_tab);
            erasable_types_tab = (uu___1662_23233.erasable_types_tab)
          }
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____23282 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____23282
                  (fun uu____23303  ->
                     match uu____23303 with
                     | (c1,g1) ->
                         let uu____23314 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____23314
                           (fun uu____23335  ->
                              match uu____23335 with
                              | (c2,g2) ->
                                  let uu____23346 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____23346)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____23468 = l1 u t e  in
                              l2 u t uu____23468))
                | uu____23469 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let edge = { msource = src; mtarget = tgt; mlift = st_mlift }  in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift }  in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____23537  ->
                    match uu____23537 with
                    | (e,uu____23545) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____23568 =
            match uu____23568 with
            | (i,j) ->
                let uu____23579 = FStar_Ident.lid_equals i j  in
                if uu____23579
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _23586  -> FStar_Pervasives_Native.Some _23586)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____23615 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____23625 = FStar_Ident.lid_equals i k  in
                        if uu____23625
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____23639 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____23639
                                  then []
                                  else
                                    (let uu____23646 =
                                       let uu____23655 =
                                         find_edge order1 (i, k)  in
                                       let uu____23658 =
                                         find_edge order1 (k, j)  in
                                       (uu____23655, uu____23658)  in
                                     match uu____23646 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____23673 =
                                           compose_edges e1 e2  in
                                         [uu____23673]
                                     | uu____23674 -> [])))))
                 in
              FStar_List.append order1 uu____23615  in
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
                  let uu____23704 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____23707 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____23707
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____23704
                  then
                    let uu____23714 =
                      let uu____23720 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____23720)
                       in
                    let uu____23724 = get_range env  in
                    FStar_Errors.raise_error uu____23714 uu____23724
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt =
                               let uu____23802 = FStar_Ident.lid_equals i j
                                  in
                               if uu____23802
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____23854 =
                                             let uu____23863 =
                                               find_edge order2 (i, k)  in
                                             let uu____23866 =
                                               find_edge order2 (j, k)  in
                                             (uu____23863, uu____23866)  in
                                           match uu____23854 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____23908,uu____23909)
                                                    ->
                                                    let uu____23916 =
                                                      let uu____23923 =
                                                        let uu____23925 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23925
                                                         in
                                                      let uu____23928 =
                                                        let uu____23930 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23930
                                                         in
                                                      (uu____23923,
                                                        uu____23928)
                                                       in
                                                    (match uu____23916 with
                                                     | (true ,true ) ->
                                                         let uu____23947 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____23947
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
                                           | uu____23990 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1767_24063 = env.effects  in
             { decls = (uu___1767_24063.decls); order = order2; joins }  in
           let uu___1770_24064 = env  in
           {
             solver = (uu___1770_24064.solver);
             range = (uu___1770_24064.range);
             curmodule = (uu___1770_24064.curmodule);
             gamma = (uu___1770_24064.gamma);
             gamma_sig = (uu___1770_24064.gamma_sig);
             gamma_cache = (uu___1770_24064.gamma_cache);
             modules = (uu___1770_24064.modules);
             expected_typ = (uu___1770_24064.expected_typ);
             sigtab = (uu___1770_24064.sigtab);
             attrtab = (uu___1770_24064.attrtab);
             is_pattern = (uu___1770_24064.is_pattern);
             instantiate_imp = (uu___1770_24064.instantiate_imp);
             effects;
             generalize = (uu___1770_24064.generalize);
             letrecs = (uu___1770_24064.letrecs);
             top_level = (uu___1770_24064.top_level);
             check_uvars = (uu___1770_24064.check_uvars);
             use_eq = (uu___1770_24064.use_eq);
             is_iface = (uu___1770_24064.is_iface);
             admit = (uu___1770_24064.admit);
             lax = (uu___1770_24064.lax);
             lax_universes = (uu___1770_24064.lax_universes);
             phase1 = (uu___1770_24064.phase1);
             failhard = (uu___1770_24064.failhard);
             nosynth = (uu___1770_24064.nosynth);
             uvar_subtyping = (uu___1770_24064.uvar_subtyping);
             tc_term = (uu___1770_24064.tc_term);
             type_of = (uu___1770_24064.type_of);
             universe_of = (uu___1770_24064.universe_of);
             check_type_of = (uu___1770_24064.check_type_of);
             use_bv_sorts = (uu___1770_24064.use_bv_sorts);
             qtbl_name_and_index = (uu___1770_24064.qtbl_name_and_index);
             normalized_eff_names = (uu___1770_24064.normalized_eff_names);
             fv_delta_depths = (uu___1770_24064.fv_delta_depths);
             proof_ns = (uu___1770_24064.proof_ns);
             synth_hook = (uu___1770_24064.synth_hook);
             try_solve_implicits_hook =
               (uu___1770_24064.try_solve_implicits_hook);
             splice = (uu___1770_24064.splice);
             postprocess = (uu___1770_24064.postprocess);
             is_native_tactic = (uu___1770_24064.is_native_tactic);
             identifier_info = (uu___1770_24064.identifier_info);
             tc_hooks = (uu___1770_24064.tc_hooks);
             dsenv = (uu___1770_24064.dsenv);
             nbe = (uu___1770_24064.nbe);
             strict_args_tab = (uu___1770_24064.strict_args_tab);
             erasable_types_tab = (uu___1770_24064.erasable_types_tab)
           })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1774_24076 = env  in
      {
        solver = (uu___1774_24076.solver);
        range = (uu___1774_24076.range);
        curmodule = (uu___1774_24076.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1774_24076.gamma_sig);
        gamma_cache = (uu___1774_24076.gamma_cache);
        modules = (uu___1774_24076.modules);
        expected_typ = (uu___1774_24076.expected_typ);
        sigtab = (uu___1774_24076.sigtab);
        attrtab = (uu___1774_24076.attrtab);
        is_pattern = (uu___1774_24076.is_pattern);
        instantiate_imp = (uu___1774_24076.instantiate_imp);
        effects = (uu___1774_24076.effects);
        generalize = (uu___1774_24076.generalize);
        letrecs = (uu___1774_24076.letrecs);
        top_level = (uu___1774_24076.top_level);
        check_uvars = (uu___1774_24076.check_uvars);
        use_eq = (uu___1774_24076.use_eq);
        is_iface = (uu___1774_24076.is_iface);
        admit = (uu___1774_24076.admit);
        lax = (uu___1774_24076.lax);
        lax_universes = (uu___1774_24076.lax_universes);
        phase1 = (uu___1774_24076.phase1);
        failhard = (uu___1774_24076.failhard);
        nosynth = (uu___1774_24076.nosynth);
        uvar_subtyping = (uu___1774_24076.uvar_subtyping);
        tc_term = (uu___1774_24076.tc_term);
        type_of = (uu___1774_24076.type_of);
        universe_of = (uu___1774_24076.universe_of);
        check_type_of = (uu___1774_24076.check_type_of);
        use_bv_sorts = (uu___1774_24076.use_bv_sorts);
        qtbl_name_and_index = (uu___1774_24076.qtbl_name_and_index);
        normalized_eff_names = (uu___1774_24076.normalized_eff_names);
        fv_delta_depths = (uu___1774_24076.fv_delta_depths);
        proof_ns = (uu___1774_24076.proof_ns);
        synth_hook = (uu___1774_24076.synth_hook);
        try_solve_implicits_hook = (uu___1774_24076.try_solve_implicits_hook);
        splice = (uu___1774_24076.splice);
        postprocess = (uu___1774_24076.postprocess);
        is_native_tactic = (uu___1774_24076.is_native_tactic);
        identifier_info = (uu___1774_24076.identifier_info);
        tc_hooks = (uu___1774_24076.tc_hooks);
        dsenv = (uu___1774_24076.dsenv);
        nbe = (uu___1774_24076.nbe);
        strict_args_tab = (uu___1774_24076.strict_args_tab);
        erasable_types_tab = (uu___1774_24076.erasable_types_tab)
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
            (let uu___1787_24134 = env  in
             {
               solver = (uu___1787_24134.solver);
               range = (uu___1787_24134.range);
               curmodule = (uu___1787_24134.curmodule);
               gamma = rest;
               gamma_sig = (uu___1787_24134.gamma_sig);
               gamma_cache = (uu___1787_24134.gamma_cache);
               modules = (uu___1787_24134.modules);
               expected_typ = (uu___1787_24134.expected_typ);
               sigtab = (uu___1787_24134.sigtab);
               attrtab = (uu___1787_24134.attrtab);
               is_pattern = (uu___1787_24134.is_pattern);
               instantiate_imp = (uu___1787_24134.instantiate_imp);
               effects = (uu___1787_24134.effects);
               generalize = (uu___1787_24134.generalize);
               letrecs = (uu___1787_24134.letrecs);
               top_level = (uu___1787_24134.top_level);
               check_uvars = (uu___1787_24134.check_uvars);
               use_eq = (uu___1787_24134.use_eq);
               is_iface = (uu___1787_24134.is_iface);
               admit = (uu___1787_24134.admit);
               lax = (uu___1787_24134.lax);
               lax_universes = (uu___1787_24134.lax_universes);
               phase1 = (uu___1787_24134.phase1);
               failhard = (uu___1787_24134.failhard);
               nosynth = (uu___1787_24134.nosynth);
               uvar_subtyping = (uu___1787_24134.uvar_subtyping);
               tc_term = (uu___1787_24134.tc_term);
               type_of = (uu___1787_24134.type_of);
               universe_of = (uu___1787_24134.universe_of);
               check_type_of = (uu___1787_24134.check_type_of);
               use_bv_sorts = (uu___1787_24134.use_bv_sorts);
               qtbl_name_and_index = (uu___1787_24134.qtbl_name_and_index);
               normalized_eff_names = (uu___1787_24134.normalized_eff_names);
               fv_delta_depths = (uu___1787_24134.fv_delta_depths);
               proof_ns = (uu___1787_24134.proof_ns);
               synth_hook = (uu___1787_24134.synth_hook);
               try_solve_implicits_hook =
                 (uu___1787_24134.try_solve_implicits_hook);
               splice = (uu___1787_24134.splice);
               postprocess = (uu___1787_24134.postprocess);
               is_native_tactic = (uu___1787_24134.is_native_tactic);
               identifier_info = (uu___1787_24134.identifier_info);
               tc_hooks = (uu___1787_24134.tc_hooks);
               dsenv = (uu___1787_24134.dsenv);
               nbe = (uu___1787_24134.nbe);
               strict_args_tab = (uu___1787_24134.strict_args_tab);
               erasable_types_tab = (uu___1787_24134.erasable_types_tab)
             }))
    | uu____24135 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24164  ->
             match uu____24164 with | (x,uu____24172) -> push_bv env1 x) env
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
            let uu___1801_24207 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1801_24207.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1801_24207.FStar_Syntax_Syntax.index);
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
        let uu____24280 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24280 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24308 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24308)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1822_24324 = env  in
      {
        solver = (uu___1822_24324.solver);
        range = (uu___1822_24324.range);
        curmodule = (uu___1822_24324.curmodule);
        gamma = (uu___1822_24324.gamma);
        gamma_sig = (uu___1822_24324.gamma_sig);
        gamma_cache = (uu___1822_24324.gamma_cache);
        modules = (uu___1822_24324.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1822_24324.sigtab);
        attrtab = (uu___1822_24324.attrtab);
        is_pattern = (uu___1822_24324.is_pattern);
        instantiate_imp = (uu___1822_24324.instantiate_imp);
        effects = (uu___1822_24324.effects);
        generalize = (uu___1822_24324.generalize);
        letrecs = (uu___1822_24324.letrecs);
        top_level = (uu___1822_24324.top_level);
        check_uvars = (uu___1822_24324.check_uvars);
        use_eq = false;
        is_iface = (uu___1822_24324.is_iface);
        admit = (uu___1822_24324.admit);
        lax = (uu___1822_24324.lax);
        lax_universes = (uu___1822_24324.lax_universes);
        phase1 = (uu___1822_24324.phase1);
        failhard = (uu___1822_24324.failhard);
        nosynth = (uu___1822_24324.nosynth);
        uvar_subtyping = (uu___1822_24324.uvar_subtyping);
        tc_term = (uu___1822_24324.tc_term);
        type_of = (uu___1822_24324.type_of);
        universe_of = (uu___1822_24324.universe_of);
        check_type_of = (uu___1822_24324.check_type_of);
        use_bv_sorts = (uu___1822_24324.use_bv_sorts);
        qtbl_name_and_index = (uu___1822_24324.qtbl_name_and_index);
        normalized_eff_names = (uu___1822_24324.normalized_eff_names);
        fv_delta_depths = (uu___1822_24324.fv_delta_depths);
        proof_ns = (uu___1822_24324.proof_ns);
        synth_hook = (uu___1822_24324.synth_hook);
        try_solve_implicits_hook = (uu___1822_24324.try_solve_implicits_hook);
        splice = (uu___1822_24324.splice);
        postprocess = (uu___1822_24324.postprocess);
        is_native_tactic = (uu___1822_24324.is_native_tactic);
        identifier_info = (uu___1822_24324.identifier_info);
        tc_hooks = (uu___1822_24324.tc_hooks);
        dsenv = (uu___1822_24324.dsenv);
        nbe = (uu___1822_24324.nbe);
        strict_args_tab = (uu___1822_24324.strict_args_tab);
        erasable_types_tab = (uu___1822_24324.erasable_types_tab)
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
    let uu____24355 = expected_typ env_  in
    ((let uu___1829_24361 = env_  in
      {
        solver = (uu___1829_24361.solver);
        range = (uu___1829_24361.range);
        curmodule = (uu___1829_24361.curmodule);
        gamma = (uu___1829_24361.gamma);
        gamma_sig = (uu___1829_24361.gamma_sig);
        gamma_cache = (uu___1829_24361.gamma_cache);
        modules = (uu___1829_24361.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1829_24361.sigtab);
        attrtab = (uu___1829_24361.attrtab);
        is_pattern = (uu___1829_24361.is_pattern);
        instantiate_imp = (uu___1829_24361.instantiate_imp);
        effects = (uu___1829_24361.effects);
        generalize = (uu___1829_24361.generalize);
        letrecs = (uu___1829_24361.letrecs);
        top_level = (uu___1829_24361.top_level);
        check_uvars = (uu___1829_24361.check_uvars);
        use_eq = false;
        is_iface = (uu___1829_24361.is_iface);
        admit = (uu___1829_24361.admit);
        lax = (uu___1829_24361.lax);
        lax_universes = (uu___1829_24361.lax_universes);
        phase1 = (uu___1829_24361.phase1);
        failhard = (uu___1829_24361.failhard);
        nosynth = (uu___1829_24361.nosynth);
        uvar_subtyping = (uu___1829_24361.uvar_subtyping);
        tc_term = (uu___1829_24361.tc_term);
        type_of = (uu___1829_24361.type_of);
        universe_of = (uu___1829_24361.universe_of);
        check_type_of = (uu___1829_24361.check_type_of);
        use_bv_sorts = (uu___1829_24361.use_bv_sorts);
        qtbl_name_and_index = (uu___1829_24361.qtbl_name_and_index);
        normalized_eff_names = (uu___1829_24361.normalized_eff_names);
        fv_delta_depths = (uu___1829_24361.fv_delta_depths);
        proof_ns = (uu___1829_24361.proof_ns);
        synth_hook = (uu___1829_24361.synth_hook);
        try_solve_implicits_hook = (uu___1829_24361.try_solve_implicits_hook);
        splice = (uu___1829_24361.splice);
        postprocess = (uu___1829_24361.postprocess);
        is_native_tactic = (uu___1829_24361.is_native_tactic);
        identifier_info = (uu___1829_24361.identifier_info);
        tc_hooks = (uu___1829_24361.tc_hooks);
        dsenv = (uu___1829_24361.dsenv);
        nbe = (uu___1829_24361.nbe);
        strict_args_tab = (uu___1829_24361.strict_args_tab);
        erasable_types_tab = (uu___1829_24361.erasable_types_tab)
      }), uu____24355)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24373 =
      let uu____24376 = FStar_Ident.id_of_text ""  in [uu____24376]  in
    FStar_Ident.lid_of_ids uu____24373  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24383 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24383
        then
          let uu____24388 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24388 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1837_24416 = env  in
       {
         solver = (uu___1837_24416.solver);
         range = (uu___1837_24416.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1837_24416.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1837_24416.expected_typ);
         sigtab = (uu___1837_24416.sigtab);
         attrtab = (uu___1837_24416.attrtab);
         is_pattern = (uu___1837_24416.is_pattern);
         instantiate_imp = (uu___1837_24416.instantiate_imp);
         effects = (uu___1837_24416.effects);
         generalize = (uu___1837_24416.generalize);
         letrecs = (uu___1837_24416.letrecs);
         top_level = (uu___1837_24416.top_level);
         check_uvars = (uu___1837_24416.check_uvars);
         use_eq = (uu___1837_24416.use_eq);
         is_iface = (uu___1837_24416.is_iface);
         admit = (uu___1837_24416.admit);
         lax = (uu___1837_24416.lax);
         lax_universes = (uu___1837_24416.lax_universes);
         phase1 = (uu___1837_24416.phase1);
         failhard = (uu___1837_24416.failhard);
         nosynth = (uu___1837_24416.nosynth);
         uvar_subtyping = (uu___1837_24416.uvar_subtyping);
         tc_term = (uu___1837_24416.tc_term);
         type_of = (uu___1837_24416.type_of);
         universe_of = (uu___1837_24416.universe_of);
         check_type_of = (uu___1837_24416.check_type_of);
         use_bv_sorts = (uu___1837_24416.use_bv_sorts);
         qtbl_name_and_index = (uu___1837_24416.qtbl_name_and_index);
         normalized_eff_names = (uu___1837_24416.normalized_eff_names);
         fv_delta_depths = (uu___1837_24416.fv_delta_depths);
         proof_ns = (uu___1837_24416.proof_ns);
         synth_hook = (uu___1837_24416.synth_hook);
         try_solve_implicits_hook =
           (uu___1837_24416.try_solve_implicits_hook);
         splice = (uu___1837_24416.splice);
         postprocess = (uu___1837_24416.postprocess);
         is_native_tactic = (uu___1837_24416.is_native_tactic);
         identifier_info = (uu___1837_24416.identifier_info);
         tc_hooks = (uu___1837_24416.tc_hooks);
         dsenv = (uu___1837_24416.dsenv);
         nbe = (uu___1837_24416.nbe);
         strict_args_tab = (uu___1837_24416.strict_args_tab);
         erasable_types_tab = (uu___1837_24416.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24468)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24472,(uu____24473,t)))::tl1
          ->
          let uu____24494 =
            let uu____24497 = FStar_Syntax_Free.uvars t  in
            ext out uu____24497  in
          aux uu____24494 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24500;
            FStar_Syntax_Syntax.index = uu____24501;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24509 =
            let uu____24512 = FStar_Syntax_Free.uvars t  in
            ext out uu____24512  in
          aux uu____24509 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24570)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24574,(uu____24575,t)))::tl1
          ->
          let uu____24596 =
            let uu____24599 = FStar_Syntax_Free.univs t  in
            ext out uu____24599  in
          aux uu____24596 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24602;
            FStar_Syntax_Syntax.index = uu____24603;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24611 =
            let uu____24614 = FStar_Syntax_Free.univs t  in
            ext out uu____24614  in
          aux uu____24611 tl1
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
          let uu____24676 = FStar_Util.set_add uname out  in
          aux uu____24676 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24679,(uu____24680,t)))::tl1
          ->
          let uu____24701 =
            let uu____24704 = FStar_Syntax_Free.univnames t  in
            ext out uu____24704  in
          aux uu____24701 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24707;
            FStar_Syntax_Syntax.index = uu____24708;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24716 =
            let uu____24719 = FStar_Syntax_Free.univnames t  in
            ext out uu____24719  in
          aux uu____24716 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24740  ->
            match uu___12_24740 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24744 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24757 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24768 =
      let uu____24777 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24777
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24768 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24825 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24838  ->
              match uu___13_24838 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24841 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24841
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24847) ->
                  let uu____24864 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24864))
       in
    FStar_All.pipe_right uu____24825 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24878  ->
    match uu___14_24878 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24884 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24884
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24907  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24962) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24995,uu____24996) -> false  in
      let uu____25010 =
        FStar_List.tryFind
          (fun uu____25032  ->
             match uu____25032 with | (p,uu____25043) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25010 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25062,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25092 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25092
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1980_25114 = e  in
        {
          solver = (uu___1980_25114.solver);
          range = (uu___1980_25114.range);
          curmodule = (uu___1980_25114.curmodule);
          gamma = (uu___1980_25114.gamma);
          gamma_sig = (uu___1980_25114.gamma_sig);
          gamma_cache = (uu___1980_25114.gamma_cache);
          modules = (uu___1980_25114.modules);
          expected_typ = (uu___1980_25114.expected_typ);
          sigtab = (uu___1980_25114.sigtab);
          attrtab = (uu___1980_25114.attrtab);
          is_pattern = (uu___1980_25114.is_pattern);
          instantiate_imp = (uu___1980_25114.instantiate_imp);
          effects = (uu___1980_25114.effects);
          generalize = (uu___1980_25114.generalize);
          letrecs = (uu___1980_25114.letrecs);
          top_level = (uu___1980_25114.top_level);
          check_uvars = (uu___1980_25114.check_uvars);
          use_eq = (uu___1980_25114.use_eq);
          is_iface = (uu___1980_25114.is_iface);
          admit = (uu___1980_25114.admit);
          lax = (uu___1980_25114.lax);
          lax_universes = (uu___1980_25114.lax_universes);
          phase1 = (uu___1980_25114.phase1);
          failhard = (uu___1980_25114.failhard);
          nosynth = (uu___1980_25114.nosynth);
          uvar_subtyping = (uu___1980_25114.uvar_subtyping);
          tc_term = (uu___1980_25114.tc_term);
          type_of = (uu___1980_25114.type_of);
          universe_of = (uu___1980_25114.universe_of);
          check_type_of = (uu___1980_25114.check_type_of);
          use_bv_sorts = (uu___1980_25114.use_bv_sorts);
          qtbl_name_and_index = (uu___1980_25114.qtbl_name_and_index);
          normalized_eff_names = (uu___1980_25114.normalized_eff_names);
          fv_delta_depths = (uu___1980_25114.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1980_25114.synth_hook);
          try_solve_implicits_hook =
            (uu___1980_25114.try_solve_implicits_hook);
          splice = (uu___1980_25114.splice);
          postprocess = (uu___1980_25114.postprocess);
          is_native_tactic = (uu___1980_25114.is_native_tactic);
          identifier_info = (uu___1980_25114.identifier_info);
          tc_hooks = (uu___1980_25114.tc_hooks);
          dsenv = (uu___1980_25114.dsenv);
          nbe = (uu___1980_25114.nbe);
          strict_args_tab = (uu___1980_25114.strict_args_tab);
          erasable_types_tab = (uu___1980_25114.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1989_25162 = e  in
      {
        solver = (uu___1989_25162.solver);
        range = (uu___1989_25162.range);
        curmodule = (uu___1989_25162.curmodule);
        gamma = (uu___1989_25162.gamma);
        gamma_sig = (uu___1989_25162.gamma_sig);
        gamma_cache = (uu___1989_25162.gamma_cache);
        modules = (uu___1989_25162.modules);
        expected_typ = (uu___1989_25162.expected_typ);
        sigtab = (uu___1989_25162.sigtab);
        attrtab = (uu___1989_25162.attrtab);
        is_pattern = (uu___1989_25162.is_pattern);
        instantiate_imp = (uu___1989_25162.instantiate_imp);
        effects = (uu___1989_25162.effects);
        generalize = (uu___1989_25162.generalize);
        letrecs = (uu___1989_25162.letrecs);
        top_level = (uu___1989_25162.top_level);
        check_uvars = (uu___1989_25162.check_uvars);
        use_eq = (uu___1989_25162.use_eq);
        is_iface = (uu___1989_25162.is_iface);
        admit = (uu___1989_25162.admit);
        lax = (uu___1989_25162.lax);
        lax_universes = (uu___1989_25162.lax_universes);
        phase1 = (uu___1989_25162.phase1);
        failhard = (uu___1989_25162.failhard);
        nosynth = (uu___1989_25162.nosynth);
        uvar_subtyping = (uu___1989_25162.uvar_subtyping);
        tc_term = (uu___1989_25162.tc_term);
        type_of = (uu___1989_25162.type_of);
        universe_of = (uu___1989_25162.universe_of);
        check_type_of = (uu___1989_25162.check_type_of);
        use_bv_sorts = (uu___1989_25162.use_bv_sorts);
        qtbl_name_and_index = (uu___1989_25162.qtbl_name_and_index);
        normalized_eff_names = (uu___1989_25162.normalized_eff_names);
        fv_delta_depths = (uu___1989_25162.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1989_25162.synth_hook);
        try_solve_implicits_hook = (uu___1989_25162.try_solve_implicits_hook);
        splice = (uu___1989_25162.splice);
        postprocess = (uu___1989_25162.postprocess);
        is_native_tactic = (uu___1989_25162.is_native_tactic);
        identifier_info = (uu___1989_25162.identifier_info);
        tc_hooks = (uu___1989_25162.tc_hooks);
        dsenv = (uu___1989_25162.dsenv);
        nbe = (uu___1989_25162.nbe);
        strict_args_tab = (uu___1989_25162.strict_args_tab);
        erasable_types_tab = (uu___1989_25162.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25178 = FStar_Syntax_Free.names t  in
      let uu____25181 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25178 uu____25181
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25204 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25204
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25214 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25214
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25235 =
      match uu____25235 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25255 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25255)
       in
    let uu____25263 =
      let uu____25267 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25267 FStar_List.rev  in
    FStar_All.pipe_right uu____25263 (FStar_String.concat " ")
  
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
                  (let uu____25335 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25335 with
                   | FStar_Pervasives_Native.Some uu____25339 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25342 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25352;
        FStar_TypeChecker_Common.univ_ineqs = uu____25353;
        FStar_TypeChecker_Common.implicits = uu____25354;_} -> true
    | uu____25364 -> false
  
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
          let uu___2033_25386 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2033_25386.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2033_25386.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2033_25386.FStar_TypeChecker_Common.implicits)
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
          let uu____25425 = FStar_Options.defensive ()  in
          if uu____25425
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25431 =
              let uu____25433 =
                let uu____25435 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25435  in
              Prims.op_Negation uu____25433  in
            (if uu____25431
             then
               let uu____25442 =
                 let uu____25448 =
                   let uu____25450 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25452 =
                     let uu____25454 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25454
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25450 uu____25452
                    in
                 (FStar_Errors.Warning_Defensive, uu____25448)  in
               FStar_Errors.log_issue rng uu____25442
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
          let uu____25494 =
            let uu____25496 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25496  in
          if uu____25494
          then ()
          else
            (let uu____25501 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25501 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25527 =
            let uu____25529 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25529  in
          if uu____25527
          then ()
          else
            (let uu____25534 = bound_vars e  in
             def_check_closed_in rng msg uu____25534 t)
  
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
          let uu___2070_25573 = g  in
          let uu____25574 =
            let uu____25575 =
              let uu____25576 =
                let uu____25583 =
                  let uu____25584 =
                    let uu____25601 =
                      let uu____25612 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25612]  in
                    (f, uu____25601)  in
                  FStar_Syntax_Syntax.Tm_app uu____25584  in
                FStar_Syntax_Syntax.mk uu____25583  in
              uu____25576 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25649  -> FStar_TypeChecker_Common.NonTrivial _25649)
              uu____25575
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____25574;
            FStar_TypeChecker_Common.deferred =
              (uu___2070_25573.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2070_25573.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2070_25573.FStar_TypeChecker_Common.implicits)
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
          let uu___2077_25667 = g  in
          let uu____25668 =
            let uu____25669 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25669  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25668;
            FStar_TypeChecker_Common.deferred =
              (uu___2077_25667.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2077_25667.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2077_25667.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2082_25686 = g  in
          let uu____25687 =
            let uu____25688 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25688  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25687;
            FStar_TypeChecker_Common.deferred =
              (uu___2082_25686.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2082_25686.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2082_25686.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2086_25690 = g  in
          let uu____25691 =
            let uu____25692 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25692  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25691;
            FStar_TypeChecker_Common.deferred =
              (uu___2086_25690.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2086_25690.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2086_25690.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25699 ->
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
                       let uu____25776 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25776
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2109_25783 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2109_25783.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2109_25783.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2109_25783.FStar_TypeChecker_Common.implicits)
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
               let uu____25817 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25817
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
            let uu___2124_25844 = g  in
            let uu____25845 =
              let uu____25846 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25846  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25845;
              FStar_TypeChecker_Common.deferred =
                (uu___2124_25844.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2124_25844.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2124_25844.FStar_TypeChecker_Common.implicits)
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
              let uu____25904 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25904 with
              | FStar_Pervasives_Native.Some
                  (uu____25929::(tm,uu____25931)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25995 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26013 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26013;
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
                      let uu___2146_26045 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2146_26045.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2146_26045.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2146_26045.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____26099 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____26156  ->
                      fun b  ->
                        match uu____26156 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____26198 =
                              let uu____26211 = reason b  in
                              new_implicit_var_aux uu____26211 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____26198 with
                             | (t,uu____26228,g_t) ->
                                 let uu____26242 =
                                   let uu____26245 =
                                     let uu____26248 =
                                       let uu____26249 =
                                         let uu____26256 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26256, t)  in
                                       FStar_Syntax_Syntax.NT uu____26249  in
                                     [uu____26248]  in
                                   FStar_List.append substs1 uu____26245  in
                                 let uu____26267 = conj_guard g g_t  in
                                 (uu____26242,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26267))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____26099
              (fun uu____26296  ->
                 match uu____26296 with
                 | (uu____26313,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26329  -> ());
    push = (fun uu____26331  -> ());
    pop = (fun uu____26334  -> ());
    snapshot =
      (fun uu____26337  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26356  -> fun uu____26357  -> ());
    encode_sig = (fun uu____26372  -> fun uu____26373  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26379 =
             let uu____26386 = FStar_Options.peek ()  in (e, g, uu____26386)
              in
           [uu____26379]);
    solve = (fun uu____26402  -> fun uu____26403  -> fun uu____26404  -> ());
    finish = (fun uu____26411  -> ());
    refresh = (fun uu____26413  -> ())
  } 