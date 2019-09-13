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
           (fun uu___0_13282  ->
              match uu___0_13282 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13285 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13285  in
                  let uu____13286 =
                    let uu____13287 = FStar_Syntax_Subst.compress y  in
                    uu____13287.FStar_Syntax_Syntax.n  in
                  (match uu____13286 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13291 =
                         let uu___314_13292 = y1  in
                         let uu____13293 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___314_13292.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___314_13292.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13293
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13291
                   | uu____13296 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___320_13310 = env  in
      let uu____13311 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___320_13310.solver);
        range = (uu___320_13310.range);
        curmodule = (uu___320_13310.curmodule);
        gamma = uu____13311;
        gamma_sig = (uu___320_13310.gamma_sig);
        gamma_cache = (uu___320_13310.gamma_cache);
        modules = (uu___320_13310.modules);
        expected_typ = (uu___320_13310.expected_typ);
        sigtab = (uu___320_13310.sigtab);
        attrtab = (uu___320_13310.attrtab);
        is_pattern = (uu___320_13310.is_pattern);
        instantiate_imp = (uu___320_13310.instantiate_imp);
        effects = (uu___320_13310.effects);
        generalize = (uu___320_13310.generalize);
        letrecs = (uu___320_13310.letrecs);
        top_level = (uu___320_13310.top_level);
        check_uvars = (uu___320_13310.check_uvars);
        use_eq = (uu___320_13310.use_eq);
        is_iface = (uu___320_13310.is_iface);
        admit = (uu___320_13310.admit);
        lax = (uu___320_13310.lax);
        lax_universes = (uu___320_13310.lax_universes);
        phase1 = (uu___320_13310.phase1);
        failhard = (uu___320_13310.failhard);
        nosynth = (uu___320_13310.nosynth);
        uvar_subtyping = (uu___320_13310.uvar_subtyping);
        tc_term = (uu___320_13310.tc_term);
        type_of = (uu___320_13310.type_of);
        universe_of = (uu___320_13310.universe_of);
        check_type_of = (uu___320_13310.check_type_of);
        use_bv_sorts = (uu___320_13310.use_bv_sorts);
        qtbl_name_and_index = (uu___320_13310.qtbl_name_and_index);
        normalized_eff_names = (uu___320_13310.normalized_eff_names);
        fv_delta_depths = (uu___320_13310.fv_delta_depths);
        proof_ns = (uu___320_13310.proof_ns);
        synth_hook = (uu___320_13310.synth_hook);
        try_solve_implicits_hook = (uu___320_13310.try_solve_implicits_hook);
        splice = (uu___320_13310.splice);
        postprocess = (uu___320_13310.postprocess);
        is_native_tactic = (uu___320_13310.is_native_tactic);
        identifier_info = (uu___320_13310.identifier_info);
        tc_hooks = (uu___320_13310.tc_hooks);
        dsenv = (uu___320_13310.dsenv);
        nbe = (uu___320_13310.nbe);
        strict_args_tab = (uu___320_13310.strict_args_tab);
        erasable_types_tab = (uu___320_13310.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13319  -> fun uu____13320  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___327_13342 = env  in
      {
        solver = (uu___327_13342.solver);
        range = (uu___327_13342.range);
        curmodule = (uu___327_13342.curmodule);
        gamma = (uu___327_13342.gamma);
        gamma_sig = (uu___327_13342.gamma_sig);
        gamma_cache = (uu___327_13342.gamma_cache);
        modules = (uu___327_13342.modules);
        expected_typ = (uu___327_13342.expected_typ);
        sigtab = (uu___327_13342.sigtab);
        attrtab = (uu___327_13342.attrtab);
        is_pattern = (uu___327_13342.is_pattern);
        instantiate_imp = (uu___327_13342.instantiate_imp);
        effects = (uu___327_13342.effects);
        generalize = (uu___327_13342.generalize);
        letrecs = (uu___327_13342.letrecs);
        top_level = (uu___327_13342.top_level);
        check_uvars = (uu___327_13342.check_uvars);
        use_eq = (uu___327_13342.use_eq);
        is_iface = (uu___327_13342.is_iface);
        admit = (uu___327_13342.admit);
        lax = (uu___327_13342.lax);
        lax_universes = (uu___327_13342.lax_universes);
        phase1 = (uu___327_13342.phase1);
        failhard = (uu___327_13342.failhard);
        nosynth = (uu___327_13342.nosynth);
        uvar_subtyping = (uu___327_13342.uvar_subtyping);
        tc_term = (uu___327_13342.tc_term);
        type_of = (uu___327_13342.type_of);
        universe_of = (uu___327_13342.universe_of);
        check_type_of = (uu___327_13342.check_type_of);
        use_bv_sorts = (uu___327_13342.use_bv_sorts);
        qtbl_name_and_index = (uu___327_13342.qtbl_name_and_index);
        normalized_eff_names = (uu___327_13342.normalized_eff_names);
        fv_delta_depths = (uu___327_13342.fv_delta_depths);
        proof_ns = (uu___327_13342.proof_ns);
        synth_hook = (uu___327_13342.synth_hook);
        try_solve_implicits_hook = (uu___327_13342.try_solve_implicits_hook);
        splice = (uu___327_13342.splice);
        postprocess = (uu___327_13342.postprocess);
        is_native_tactic = (uu___327_13342.is_native_tactic);
        identifier_info = (uu___327_13342.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___327_13342.dsenv);
        nbe = (uu___327_13342.nbe);
        strict_args_tab = (uu___327_13342.strict_args_tab);
        erasable_types_tab = (uu___327_13342.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___331_13354 = e  in
      let uu____13355 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___331_13354.solver);
        range = (uu___331_13354.range);
        curmodule = (uu___331_13354.curmodule);
        gamma = (uu___331_13354.gamma);
        gamma_sig = (uu___331_13354.gamma_sig);
        gamma_cache = (uu___331_13354.gamma_cache);
        modules = (uu___331_13354.modules);
        expected_typ = (uu___331_13354.expected_typ);
        sigtab = (uu___331_13354.sigtab);
        attrtab = (uu___331_13354.attrtab);
        is_pattern = (uu___331_13354.is_pattern);
        instantiate_imp = (uu___331_13354.instantiate_imp);
        effects = (uu___331_13354.effects);
        generalize = (uu___331_13354.generalize);
        letrecs = (uu___331_13354.letrecs);
        top_level = (uu___331_13354.top_level);
        check_uvars = (uu___331_13354.check_uvars);
        use_eq = (uu___331_13354.use_eq);
        is_iface = (uu___331_13354.is_iface);
        admit = (uu___331_13354.admit);
        lax = (uu___331_13354.lax);
        lax_universes = (uu___331_13354.lax_universes);
        phase1 = (uu___331_13354.phase1);
        failhard = (uu___331_13354.failhard);
        nosynth = (uu___331_13354.nosynth);
        uvar_subtyping = (uu___331_13354.uvar_subtyping);
        tc_term = (uu___331_13354.tc_term);
        type_of = (uu___331_13354.type_of);
        universe_of = (uu___331_13354.universe_of);
        check_type_of = (uu___331_13354.check_type_of);
        use_bv_sorts = (uu___331_13354.use_bv_sorts);
        qtbl_name_and_index = (uu___331_13354.qtbl_name_and_index);
        normalized_eff_names = (uu___331_13354.normalized_eff_names);
        fv_delta_depths = (uu___331_13354.fv_delta_depths);
        proof_ns = (uu___331_13354.proof_ns);
        synth_hook = (uu___331_13354.synth_hook);
        try_solve_implicits_hook = (uu___331_13354.try_solve_implicits_hook);
        splice = (uu___331_13354.splice);
        postprocess = (uu___331_13354.postprocess);
        is_native_tactic = (uu___331_13354.is_native_tactic);
        identifier_info = (uu___331_13354.identifier_info);
        tc_hooks = (uu___331_13354.tc_hooks);
        dsenv = uu____13355;
        nbe = (uu___331_13354.nbe);
        strict_args_tab = (uu___331_13354.strict_args_tab);
        erasable_types_tab = (uu___331_13354.erasable_types_tab)
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
      | (NoDelta ,uu____13384) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13387,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13389,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13392 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13406 . unit -> 'Auu____13406 FStar_Util.smap =
  fun uu____13413  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13419 . unit -> 'Auu____13419 FStar_Util.smap =
  fun uu____13426  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13564 = new_gamma_cache ()  in
                  let uu____13567 = new_sigtab ()  in
                  let uu____13570 = new_sigtab ()  in
                  let uu____13577 =
                    let uu____13592 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13592, FStar_Pervasives_Native.None)  in
                  let uu____13613 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13617 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13621 = FStar_Options.using_facts_from ()  in
                  let uu____13622 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13625 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13626 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13640 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13564;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13567;
                    attrtab = uu____13570;
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
                    qtbl_name_and_index = uu____13577;
                    normalized_eff_names = uu____13613;
                    fv_delta_depths = uu____13617;
                    proof_ns = uu____13621;
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
                    is_native_tactic = (fun uu____13714  -> false);
                    identifier_info = uu____13622;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13625;
                    nbe = nbe1;
                    strict_args_tab = uu____13626;
                    erasable_types_tab = uu____13640
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
  fun uu____13793  ->
    let uu____13794 = FStar_ST.op_Bang query_indices  in
    match uu____13794 with
    | [] -> failwith "Empty query indices!"
    | uu____13849 ->
        let uu____13859 =
          let uu____13869 =
            let uu____13877 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13877  in
          let uu____13931 = FStar_ST.op_Bang query_indices  in uu____13869 ::
            uu____13931
           in
        FStar_ST.op_Colon_Equals query_indices uu____13859
  
let (pop_query_indices : unit -> unit) =
  fun uu____14027  ->
    let uu____14028 = FStar_ST.op_Bang query_indices  in
    match uu____14028 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14155  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14192  ->
    match uu____14192 with
    | (l,n1) ->
        let uu____14202 = FStar_ST.op_Bang query_indices  in
        (match uu____14202 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14324 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14347  ->
    let uu____14348 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14348
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14416 =
       let uu____14419 = FStar_ST.op_Bang stack  in env :: uu____14419  in
     FStar_ST.op_Colon_Equals stack uu____14416);
    (let uu___402_14468 = env  in
     let uu____14469 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14472 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14475 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14482 =
       let uu____14497 =
         let uu____14501 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14501  in
       let uu____14533 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14497, uu____14533)  in
     let uu____14582 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14585 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14588 =
       let uu____14591 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14591  in
     let uu____14611 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14624 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___402_14468.solver);
       range = (uu___402_14468.range);
       curmodule = (uu___402_14468.curmodule);
       gamma = (uu___402_14468.gamma);
       gamma_sig = (uu___402_14468.gamma_sig);
       gamma_cache = uu____14469;
       modules = (uu___402_14468.modules);
       expected_typ = (uu___402_14468.expected_typ);
       sigtab = uu____14472;
       attrtab = uu____14475;
       is_pattern = (uu___402_14468.is_pattern);
       instantiate_imp = (uu___402_14468.instantiate_imp);
       effects = (uu___402_14468.effects);
       generalize = (uu___402_14468.generalize);
       letrecs = (uu___402_14468.letrecs);
       top_level = (uu___402_14468.top_level);
       check_uvars = (uu___402_14468.check_uvars);
       use_eq = (uu___402_14468.use_eq);
       is_iface = (uu___402_14468.is_iface);
       admit = (uu___402_14468.admit);
       lax = (uu___402_14468.lax);
       lax_universes = (uu___402_14468.lax_universes);
       phase1 = (uu___402_14468.phase1);
       failhard = (uu___402_14468.failhard);
       nosynth = (uu___402_14468.nosynth);
       uvar_subtyping = (uu___402_14468.uvar_subtyping);
       tc_term = (uu___402_14468.tc_term);
       type_of = (uu___402_14468.type_of);
       universe_of = (uu___402_14468.universe_of);
       check_type_of = (uu___402_14468.check_type_of);
       use_bv_sorts = (uu___402_14468.use_bv_sorts);
       qtbl_name_and_index = uu____14482;
       normalized_eff_names = uu____14582;
       fv_delta_depths = uu____14585;
       proof_ns = (uu___402_14468.proof_ns);
       synth_hook = (uu___402_14468.synth_hook);
       try_solve_implicits_hook = (uu___402_14468.try_solve_implicits_hook);
       splice = (uu___402_14468.splice);
       postprocess = (uu___402_14468.postprocess);
       is_native_tactic = (uu___402_14468.is_native_tactic);
       identifier_info = uu____14588;
       tc_hooks = (uu___402_14468.tc_hooks);
       dsenv = (uu___402_14468.dsenv);
       nbe = (uu___402_14468.nbe);
       strict_args_tab = uu____14611;
       erasable_types_tab = uu____14624
     })
  
let (pop_stack : unit -> env) =
  fun uu____14634  ->
    let uu____14635 = FStar_ST.op_Bang stack  in
    match uu____14635 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14689 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14779  ->
           let uu____14780 = snapshot_stack env  in
           match uu____14780 with
           | (stack_depth,env1) ->
               let uu____14814 = snapshot_query_indices ()  in
               (match uu____14814 with
                | (query_indices_depth,()) ->
                    let uu____14847 = (env1.solver).snapshot msg  in
                    (match uu____14847 with
                     | (solver_depth,()) ->
                         let uu____14904 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14904 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___427_14971 = env1  in
                                 {
                                   solver = (uu___427_14971.solver);
                                   range = (uu___427_14971.range);
                                   curmodule = (uu___427_14971.curmodule);
                                   gamma = (uu___427_14971.gamma);
                                   gamma_sig = (uu___427_14971.gamma_sig);
                                   gamma_cache = (uu___427_14971.gamma_cache);
                                   modules = (uu___427_14971.modules);
                                   expected_typ =
                                     (uu___427_14971.expected_typ);
                                   sigtab = (uu___427_14971.sigtab);
                                   attrtab = (uu___427_14971.attrtab);
                                   is_pattern = (uu___427_14971.is_pattern);
                                   instantiate_imp =
                                     (uu___427_14971.instantiate_imp);
                                   effects = (uu___427_14971.effects);
                                   generalize = (uu___427_14971.generalize);
                                   letrecs = (uu___427_14971.letrecs);
                                   top_level = (uu___427_14971.top_level);
                                   check_uvars = (uu___427_14971.check_uvars);
                                   use_eq = (uu___427_14971.use_eq);
                                   is_iface = (uu___427_14971.is_iface);
                                   admit = (uu___427_14971.admit);
                                   lax = (uu___427_14971.lax);
                                   lax_universes =
                                     (uu___427_14971.lax_universes);
                                   phase1 = (uu___427_14971.phase1);
                                   failhard = (uu___427_14971.failhard);
                                   nosynth = (uu___427_14971.nosynth);
                                   uvar_subtyping =
                                     (uu___427_14971.uvar_subtyping);
                                   tc_term = (uu___427_14971.tc_term);
                                   type_of = (uu___427_14971.type_of);
                                   universe_of = (uu___427_14971.universe_of);
                                   check_type_of =
                                     (uu___427_14971.check_type_of);
                                   use_bv_sorts =
                                     (uu___427_14971.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___427_14971.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___427_14971.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___427_14971.fv_delta_depths);
                                   proof_ns = (uu___427_14971.proof_ns);
                                   synth_hook = (uu___427_14971.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___427_14971.try_solve_implicits_hook);
                                   splice = (uu___427_14971.splice);
                                   postprocess = (uu___427_14971.postprocess);
                                   is_native_tactic =
                                     (uu___427_14971.is_native_tactic);
                                   identifier_info =
                                     (uu___427_14971.identifier_info);
                                   tc_hooks = (uu___427_14971.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___427_14971.nbe);
                                   strict_args_tab =
                                     (uu___427_14971.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___427_14971.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15005  ->
             let uu____15006 =
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
             match uu____15006 with
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
                             ((let uu____15186 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15186
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15202 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15202
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15234,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15276 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15306  ->
                  match uu____15306 with
                  | (m,uu____15314) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15276 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___472_15329 = env  in
               {
                 solver = (uu___472_15329.solver);
                 range = (uu___472_15329.range);
                 curmodule = (uu___472_15329.curmodule);
                 gamma = (uu___472_15329.gamma);
                 gamma_sig = (uu___472_15329.gamma_sig);
                 gamma_cache = (uu___472_15329.gamma_cache);
                 modules = (uu___472_15329.modules);
                 expected_typ = (uu___472_15329.expected_typ);
                 sigtab = (uu___472_15329.sigtab);
                 attrtab = (uu___472_15329.attrtab);
                 is_pattern = (uu___472_15329.is_pattern);
                 instantiate_imp = (uu___472_15329.instantiate_imp);
                 effects = (uu___472_15329.effects);
                 generalize = (uu___472_15329.generalize);
                 letrecs = (uu___472_15329.letrecs);
                 top_level = (uu___472_15329.top_level);
                 check_uvars = (uu___472_15329.check_uvars);
                 use_eq = (uu___472_15329.use_eq);
                 is_iface = (uu___472_15329.is_iface);
                 admit = (uu___472_15329.admit);
                 lax = (uu___472_15329.lax);
                 lax_universes = (uu___472_15329.lax_universes);
                 phase1 = (uu___472_15329.phase1);
                 failhard = (uu___472_15329.failhard);
                 nosynth = (uu___472_15329.nosynth);
                 uvar_subtyping = (uu___472_15329.uvar_subtyping);
                 tc_term = (uu___472_15329.tc_term);
                 type_of = (uu___472_15329.type_of);
                 universe_of = (uu___472_15329.universe_of);
                 check_type_of = (uu___472_15329.check_type_of);
                 use_bv_sorts = (uu___472_15329.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___472_15329.normalized_eff_names);
                 fv_delta_depths = (uu___472_15329.fv_delta_depths);
                 proof_ns = (uu___472_15329.proof_ns);
                 synth_hook = (uu___472_15329.synth_hook);
                 try_solve_implicits_hook =
                   (uu___472_15329.try_solve_implicits_hook);
                 splice = (uu___472_15329.splice);
                 postprocess = (uu___472_15329.postprocess);
                 is_native_tactic = (uu___472_15329.is_native_tactic);
                 identifier_info = (uu___472_15329.identifier_info);
                 tc_hooks = (uu___472_15329.tc_hooks);
                 dsenv = (uu___472_15329.dsenv);
                 nbe = (uu___472_15329.nbe);
                 strict_args_tab = (uu___472_15329.strict_args_tab);
                 erasable_types_tab = (uu___472_15329.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15346,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___481_15362 = env  in
               {
                 solver = (uu___481_15362.solver);
                 range = (uu___481_15362.range);
                 curmodule = (uu___481_15362.curmodule);
                 gamma = (uu___481_15362.gamma);
                 gamma_sig = (uu___481_15362.gamma_sig);
                 gamma_cache = (uu___481_15362.gamma_cache);
                 modules = (uu___481_15362.modules);
                 expected_typ = (uu___481_15362.expected_typ);
                 sigtab = (uu___481_15362.sigtab);
                 attrtab = (uu___481_15362.attrtab);
                 is_pattern = (uu___481_15362.is_pattern);
                 instantiate_imp = (uu___481_15362.instantiate_imp);
                 effects = (uu___481_15362.effects);
                 generalize = (uu___481_15362.generalize);
                 letrecs = (uu___481_15362.letrecs);
                 top_level = (uu___481_15362.top_level);
                 check_uvars = (uu___481_15362.check_uvars);
                 use_eq = (uu___481_15362.use_eq);
                 is_iface = (uu___481_15362.is_iface);
                 admit = (uu___481_15362.admit);
                 lax = (uu___481_15362.lax);
                 lax_universes = (uu___481_15362.lax_universes);
                 phase1 = (uu___481_15362.phase1);
                 failhard = (uu___481_15362.failhard);
                 nosynth = (uu___481_15362.nosynth);
                 uvar_subtyping = (uu___481_15362.uvar_subtyping);
                 tc_term = (uu___481_15362.tc_term);
                 type_of = (uu___481_15362.type_of);
                 universe_of = (uu___481_15362.universe_of);
                 check_type_of = (uu___481_15362.check_type_of);
                 use_bv_sorts = (uu___481_15362.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___481_15362.normalized_eff_names);
                 fv_delta_depths = (uu___481_15362.fv_delta_depths);
                 proof_ns = (uu___481_15362.proof_ns);
                 synth_hook = (uu___481_15362.synth_hook);
                 try_solve_implicits_hook =
                   (uu___481_15362.try_solve_implicits_hook);
                 splice = (uu___481_15362.splice);
                 postprocess = (uu___481_15362.postprocess);
                 is_native_tactic = (uu___481_15362.is_native_tactic);
                 identifier_info = (uu___481_15362.identifier_info);
                 tc_hooks = (uu___481_15362.tc_hooks);
                 dsenv = (uu___481_15362.dsenv);
                 nbe = (uu___481_15362.nbe);
                 strict_args_tab = (uu___481_15362.strict_args_tab);
                 erasable_types_tab = (uu___481_15362.erasable_types_tab)
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
        (let uu___488_15405 = e  in
         {
           solver = (uu___488_15405.solver);
           range = r;
           curmodule = (uu___488_15405.curmodule);
           gamma = (uu___488_15405.gamma);
           gamma_sig = (uu___488_15405.gamma_sig);
           gamma_cache = (uu___488_15405.gamma_cache);
           modules = (uu___488_15405.modules);
           expected_typ = (uu___488_15405.expected_typ);
           sigtab = (uu___488_15405.sigtab);
           attrtab = (uu___488_15405.attrtab);
           is_pattern = (uu___488_15405.is_pattern);
           instantiate_imp = (uu___488_15405.instantiate_imp);
           effects = (uu___488_15405.effects);
           generalize = (uu___488_15405.generalize);
           letrecs = (uu___488_15405.letrecs);
           top_level = (uu___488_15405.top_level);
           check_uvars = (uu___488_15405.check_uvars);
           use_eq = (uu___488_15405.use_eq);
           is_iface = (uu___488_15405.is_iface);
           admit = (uu___488_15405.admit);
           lax = (uu___488_15405.lax);
           lax_universes = (uu___488_15405.lax_universes);
           phase1 = (uu___488_15405.phase1);
           failhard = (uu___488_15405.failhard);
           nosynth = (uu___488_15405.nosynth);
           uvar_subtyping = (uu___488_15405.uvar_subtyping);
           tc_term = (uu___488_15405.tc_term);
           type_of = (uu___488_15405.type_of);
           universe_of = (uu___488_15405.universe_of);
           check_type_of = (uu___488_15405.check_type_of);
           use_bv_sorts = (uu___488_15405.use_bv_sorts);
           qtbl_name_and_index = (uu___488_15405.qtbl_name_and_index);
           normalized_eff_names = (uu___488_15405.normalized_eff_names);
           fv_delta_depths = (uu___488_15405.fv_delta_depths);
           proof_ns = (uu___488_15405.proof_ns);
           synth_hook = (uu___488_15405.synth_hook);
           try_solve_implicits_hook =
             (uu___488_15405.try_solve_implicits_hook);
           splice = (uu___488_15405.splice);
           postprocess = (uu___488_15405.postprocess);
           is_native_tactic = (uu___488_15405.is_native_tactic);
           identifier_info = (uu___488_15405.identifier_info);
           tc_hooks = (uu___488_15405.tc_hooks);
           dsenv = (uu___488_15405.dsenv);
           nbe = (uu___488_15405.nbe);
           strict_args_tab = (uu___488_15405.strict_args_tab);
           erasable_types_tab = (uu___488_15405.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15425 =
        let uu____15426 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15426 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15425
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15481 =
          let uu____15482 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15482 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15481
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15537 =
          let uu____15538 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15538 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15537
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15593 =
        let uu____15594 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15594 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15593
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___505_15658 = env  in
      {
        solver = (uu___505_15658.solver);
        range = (uu___505_15658.range);
        curmodule = lid;
        gamma = (uu___505_15658.gamma);
        gamma_sig = (uu___505_15658.gamma_sig);
        gamma_cache = (uu___505_15658.gamma_cache);
        modules = (uu___505_15658.modules);
        expected_typ = (uu___505_15658.expected_typ);
        sigtab = (uu___505_15658.sigtab);
        attrtab = (uu___505_15658.attrtab);
        is_pattern = (uu___505_15658.is_pattern);
        instantiate_imp = (uu___505_15658.instantiate_imp);
        effects = (uu___505_15658.effects);
        generalize = (uu___505_15658.generalize);
        letrecs = (uu___505_15658.letrecs);
        top_level = (uu___505_15658.top_level);
        check_uvars = (uu___505_15658.check_uvars);
        use_eq = (uu___505_15658.use_eq);
        is_iface = (uu___505_15658.is_iface);
        admit = (uu___505_15658.admit);
        lax = (uu___505_15658.lax);
        lax_universes = (uu___505_15658.lax_universes);
        phase1 = (uu___505_15658.phase1);
        failhard = (uu___505_15658.failhard);
        nosynth = (uu___505_15658.nosynth);
        uvar_subtyping = (uu___505_15658.uvar_subtyping);
        tc_term = (uu___505_15658.tc_term);
        type_of = (uu___505_15658.type_of);
        universe_of = (uu___505_15658.universe_of);
        check_type_of = (uu___505_15658.check_type_of);
        use_bv_sorts = (uu___505_15658.use_bv_sorts);
        qtbl_name_and_index = (uu___505_15658.qtbl_name_and_index);
        normalized_eff_names = (uu___505_15658.normalized_eff_names);
        fv_delta_depths = (uu___505_15658.fv_delta_depths);
        proof_ns = (uu___505_15658.proof_ns);
        synth_hook = (uu___505_15658.synth_hook);
        try_solve_implicits_hook = (uu___505_15658.try_solve_implicits_hook);
        splice = (uu___505_15658.splice);
        postprocess = (uu___505_15658.postprocess);
        is_native_tactic = (uu___505_15658.is_native_tactic);
        identifier_info = (uu___505_15658.identifier_info);
        tc_hooks = (uu___505_15658.tc_hooks);
        dsenv = (uu___505_15658.dsenv);
        nbe = (uu___505_15658.nbe);
        strict_args_tab = (uu___505_15658.strict_args_tab);
        erasable_types_tab = (uu___505_15658.erasable_types_tab)
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
      let uu____15689 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15689
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15702 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15702)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15717 =
      let uu____15719 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15719  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15717)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15728  ->
    let uu____15729 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15729
  
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
      | ((formals,t),uu____15829) ->
          let vs = mk_univ_subst formals us  in
          let uu____15853 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15853)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15870  ->
    match uu___1_15870 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15896  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15916 = inst_tscheme t  in
      match uu____15916 with
      | (us,t1) ->
          let uu____15927 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15927)
  
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
          let uu____15952 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15954 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15952 uu____15954
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
        fun uu____15981  ->
          match uu____15981 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15995 =
                    let uu____15997 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16001 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16005 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16007 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15997 uu____16001 uu____16005 uu____16007
                     in
                  failwith uu____15995)
               else ();
               (let uu____16012 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16012))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16030 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16041 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16052 -> false
  
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
             | ([],uu____16100) -> Maybe
             | (uu____16107,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16127 -> No  in
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
          let uu____16221 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16221 with
          | FStar_Pervasives_Native.None  ->
              let uu____16244 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16288  ->
                     match uu___2_16288 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16327 = FStar_Ident.lid_equals lid l  in
                         if uu____16327
                         then
                           let uu____16350 =
                             let uu____16369 =
                               let uu____16384 = inst_tscheme t  in
                               FStar_Util.Inl uu____16384  in
                             let uu____16399 = FStar_Ident.range_of_lid l  in
                             (uu____16369, uu____16399)  in
                           FStar_Pervasives_Native.Some uu____16350
                         else FStar_Pervasives_Native.None
                     | uu____16452 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16244
                (fun uu____16490  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16499  ->
                        match uu___3_16499 with
                        | (uu____16502,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16504);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16505;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16506;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16507;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16508;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16528 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16528
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
                                  uu____16580 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16587 -> cache t  in
                            let uu____16588 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16588 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16594 =
                                   let uu____16595 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16595)
                                    in
                                 maybe_cache uu____16594)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16666 = find_in_sigtab env lid  in
         match uu____16666 with
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
      let uu____16747 = lookup_qname env lid  in
      match uu____16747 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16768,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16882 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16882 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16927 =
          let uu____16930 = lookup_attr env1 attr  in se1 :: uu____16930  in
        FStar_Util.smap_add (attrtab env1) attr uu____16927  in
      FStar_List.iter
        (fun attr  ->
           let uu____16940 =
             let uu____16941 = FStar_Syntax_Subst.compress attr  in
             uu____16941.FStar_Syntax_Syntax.n  in
           match uu____16940 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16945 =
                 let uu____16947 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16947.FStar_Ident.str  in
               add_one1 env se uu____16945
           | uu____16948 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16971) ->
          add_sigelts env ses
      | uu____16980 ->
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
        (fun uu___4_17018  ->
           match uu___4_17018 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17036 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17098,lb::[]),uu____17100) ->
            let uu____17109 =
              let uu____17118 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17127 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17118, uu____17127)  in
            FStar_Pervasives_Native.Some uu____17109
        | FStar_Syntax_Syntax.Sig_let ((uu____17140,lbs),uu____17142) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17174 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17187 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17187
                     then
                       let uu____17200 =
                         let uu____17209 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17218 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17209, uu____17218)  in
                       FStar_Pervasives_Native.Some uu____17200
                     else FStar_Pervasives_Native.None)
        | uu____17241 -> FStar_Pervasives_Native.None
  
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
                    let uu____17333 =
                      let uu____17335 =
                        let uu____17337 =
                          let uu____17339 =
                            let uu____17341 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17347 =
                              let uu____17349 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17349  in
                            Prims.op_Hat uu____17341 uu____17347  in
                          Prims.op_Hat ", expected " uu____17339  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17337
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17335
                       in
                    failwith uu____17333
                  else ());
             (let uu____17356 =
                let uu____17365 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17365, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17356))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17385,uu____17386) ->
            let uu____17391 =
              let uu____17400 =
                let uu____17405 =
                  let uu____17406 =
                    let uu____17409 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17409  in
                  (us, uu____17406)  in
                inst_ts us_opt uu____17405  in
              (uu____17400, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17391
        | uu____17428 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17517 =
          match uu____17517 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17613,uvs,t,uu____17616,uu____17617,uu____17618);
                      FStar_Syntax_Syntax.sigrng = uu____17619;
                      FStar_Syntax_Syntax.sigquals = uu____17620;
                      FStar_Syntax_Syntax.sigmeta = uu____17621;
                      FStar_Syntax_Syntax.sigattrs = uu____17622;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17645 =
                     let uu____17654 = inst_tscheme1 (uvs, t)  in
                     (uu____17654, rng)  in
                   FStar_Pervasives_Native.Some uu____17645
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17678;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17680;
                      FStar_Syntax_Syntax.sigattrs = uu____17681;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17698 =
                     let uu____17700 = in_cur_mod env l  in uu____17700 = Yes
                      in
                   if uu____17698
                   then
                     let uu____17712 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17712
                      then
                        let uu____17728 =
                          let uu____17737 = inst_tscheme1 (uvs, t)  in
                          (uu____17737, rng)  in
                        FStar_Pervasives_Native.Some uu____17728
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17770 =
                        let uu____17779 = inst_tscheme1 (uvs, t)  in
                        (uu____17779, rng)  in
                      FStar_Pervasives_Native.Some uu____17770)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17804,uu____17805);
                      FStar_Syntax_Syntax.sigrng = uu____17806;
                      FStar_Syntax_Syntax.sigquals = uu____17807;
                      FStar_Syntax_Syntax.sigmeta = uu____17808;
                      FStar_Syntax_Syntax.sigattrs = uu____17809;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17850 =
                          let uu____17859 = inst_tscheme1 (uvs, k)  in
                          (uu____17859, rng)  in
                        FStar_Pervasives_Native.Some uu____17850
                    | uu____17880 ->
                        let uu____17881 =
                          let uu____17890 =
                            let uu____17895 =
                              let uu____17896 =
                                let uu____17899 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17899
                                 in
                              (uvs, uu____17896)  in
                            inst_tscheme1 uu____17895  in
                          (uu____17890, rng)  in
                        FStar_Pervasives_Native.Some uu____17881)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17922,uu____17923);
                      FStar_Syntax_Syntax.sigrng = uu____17924;
                      FStar_Syntax_Syntax.sigquals = uu____17925;
                      FStar_Syntax_Syntax.sigmeta = uu____17926;
                      FStar_Syntax_Syntax.sigattrs = uu____17927;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17969 =
                          let uu____17978 = inst_tscheme_with (uvs, k) us  in
                          (uu____17978, rng)  in
                        FStar_Pervasives_Native.Some uu____17969
                    | uu____17999 ->
                        let uu____18000 =
                          let uu____18009 =
                            let uu____18014 =
                              let uu____18015 =
                                let uu____18018 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18018
                                 in
                              (uvs, uu____18015)  in
                            inst_tscheme_with uu____18014 us  in
                          (uu____18009, rng)  in
                        FStar_Pervasives_Native.Some uu____18000)
               | FStar_Util.Inr se ->
                   let uu____18054 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18075;
                          FStar_Syntax_Syntax.sigrng = uu____18076;
                          FStar_Syntax_Syntax.sigquals = uu____18077;
                          FStar_Syntax_Syntax.sigmeta = uu____18078;
                          FStar_Syntax_Syntax.sigattrs = uu____18079;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18094 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18054
                     (FStar_Util.map_option
                        (fun uu____18142  ->
                           match uu____18142 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18173 =
          let uu____18184 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18184 mapper  in
        match uu____18173 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18258 =
              let uu____18269 =
                let uu____18276 =
                  let uu___836_18279 = t  in
                  let uu____18280 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___836_18279.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18280;
                    FStar_Syntax_Syntax.vars =
                      (uu___836_18279.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18276)  in
              (uu____18269, r)  in
            FStar_Pervasives_Native.Some uu____18258
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18329 = lookup_qname env l  in
      match uu____18329 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18350 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18404 = try_lookup_bv env bv  in
      match uu____18404 with
      | FStar_Pervasives_Native.None  ->
          let uu____18419 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18419 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18435 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18436 =
            let uu____18437 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18437  in
          (uu____18435, uu____18436)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18459 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18459 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18525 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18525  in
          let uu____18526 =
            let uu____18535 =
              let uu____18540 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18540)  in
            (uu____18535, r1)  in
          FStar_Pervasives_Native.Some uu____18526
  
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
        let uu____18575 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18575 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18608,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18633 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18633  in
            let uu____18634 =
              let uu____18639 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18639, r1)  in
            FStar_Pervasives_Native.Some uu____18634
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18663 = try_lookup_lid env l  in
      match uu____18663 with
      | FStar_Pervasives_Native.None  ->
          let uu____18690 = name_not_found l  in
          let uu____18696 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18690 uu____18696
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18739  ->
              match uu___5_18739 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18743 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18764 = lookup_qname env lid  in
      match uu____18764 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18773,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18776;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18778;
              FStar_Syntax_Syntax.sigattrs = uu____18779;_},FStar_Pervasives_Native.None
            ),uu____18780)
          ->
          let uu____18829 =
            let uu____18836 =
              let uu____18837 =
                let uu____18840 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18840 t  in
              (uvs, uu____18837)  in
            (uu____18836, q)  in
          FStar_Pervasives_Native.Some uu____18829
      | uu____18853 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18875 = lookup_qname env lid  in
      match uu____18875 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18880,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18883;
              FStar_Syntax_Syntax.sigquals = uu____18884;
              FStar_Syntax_Syntax.sigmeta = uu____18885;
              FStar_Syntax_Syntax.sigattrs = uu____18886;_},FStar_Pervasives_Native.None
            ),uu____18887)
          ->
          let uu____18936 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18936 (uvs, t)
      | uu____18941 ->
          let uu____18942 = name_not_found lid  in
          let uu____18948 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18942 uu____18948
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18968 = lookup_qname env lid  in
      match uu____18968 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18973,uvs,t,uu____18976,uu____18977,uu____18978);
              FStar_Syntax_Syntax.sigrng = uu____18979;
              FStar_Syntax_Syntax.sigquals = uu____18980;
              FStar_Syntax_Syntax.sigmeta = uu____18981;
              FStar_Syntax_Syntax.sigattrs = uu____18982;_},FStar_Pervasives_Native.None
            ),uu____18983)
          ->
          let uu____19038 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19038 (uvs, t)
      | uu____19043 ->
          let uu____19044 = name_not_found lid  in
          let uu____19050 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19044 uu____19050
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19073 = lookup_qname env lid  in
      match uu____19073 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19081,uu____19082,uu____19083,uu____19084,uu____19085,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19087;
              FStar_Syntax_Syntax.sigquals = uu____19088;
              FStar_Syntax_Syntax.sigmeta = uu____19089;
              FStar_Syntax_Syntax.sigattrs = uu____19090;_},uu____19091),uu____19092)
          -> (true, dcs)
      | uu____19155 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19171 = lookup_qname env lid  in
      match uu____19171 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19172,uu____19173,uu____19174,l,uu____19176,uu____19177);
              FStar_Syntax_Syntax.sigrng = uu____19178;
              FStar_Syntax_Syntax.sigquals = uu____19179;
              FStar_Syntax_Syntax.sigmeta = uu____19180;
              FStar_Syntax_Syntax.sigattrs = uu____19181;_},uu____19182),uu____19183)
          -> l
      | uu____19240 ->
          let uu____19241 =
            let uu____19243 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19243  in
          failwith uu____19241
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19313)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19370) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19394 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19394
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19429 -> FStar_Pervasives_Native.None)
          | uu____19438 -> FStar_Pervasives_Native.None
  
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
        let uu____19500 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19500
  
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
        let uu____19533 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19533
  
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
             (FStar_Util.Inl uu____19585,uu____19586) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19635),uu____19636) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19685 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19703 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19713 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19730 ->
                  let uu____19737 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19737
              | FStar_Syntax_Syntax.Sig_let ((uu____19738,lbs),uu____19740)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19756 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19756
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19763 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19771 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19772 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19779 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19780 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19781 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19782 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19795 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19813 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19813
           (fun d_opt  ->
              let uu____19826 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19826
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19836 =
                   let uu____19839 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19839  in
                 match uu____19836 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19840 =
                       let uu____19842 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19842
                        in
                     failwith uu____19840
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19847 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19847
                       then
                         let uu____19850 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19852 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19854 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19850 uu____19852 uu____19854
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
        (FStar_Util.Inr (se,uu____19879),uu____19880) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19929 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19951),uu____19952) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20001 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20023 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20023
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20056 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20056 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20078 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20087 =
                        let uu____20088 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20088.FStar_Syntax_Syntax.n  in
                      match uu____20087 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20093 -> false))
               in
            (true, uu____20078)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20116 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20116
  
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
          let uu____20188 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20188.FStar_Ident.str  in
        let uu____20189 = FStar_Util.smap_try_find tab s  in
        match uu____20189 with
        | FStar_Pervasives_Native.None  ->
            let uu____20192 = f ()  in
            (match uu____20192 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20230 =
        let uu____20231 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20231 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20265 =
        let uu____20266 = FStar_Syntax_Util.unrefine t  in
        uu____20266.FStar_Syntax_Syntax.n  in
      match uu____20265 with
      | FStar_Syntax_Syntax.Tm_type uu____20270 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20274) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20300) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20305,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20327 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20360 =
        let attrs =
          let uu____20366 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20366  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20406 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20406)
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
      let uu____20451 = lookup_qname env ftv  in
      match uu____20451 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20455) ->
          let uu____20500 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20500 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20521,t),r) ->
               let uu____20536 =
                 let uu____20537 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20537 t  in
               FStar_Pervasives_Native.Some uu____20536)
      | uu____20538 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20550 = try_lookup_effect_lid env ftv  in
      match uu____20550 with
      | FStar_Pervasives_Native.None  ->
          let uu____20553 = name_not_found ftv  in
          let uu____20559 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20553 uu____20559
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
        let uu____20583 = lookup_qname env lid0  in
        match uu____20583 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20594);
                FStar_Syntax_Syntax.sigrng = uu____20595;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20597;
                FStar_Syntax_Syntax.sigattrs = uu____20598;_},FStar_Pervasives_Native.None
              ),uu____20599)
            ->
            let lid1 =
              let uu____20653 =
                let uu____20654 = FStar_Ident.range_of_lid lid  in
                let uu____20655 =
                  let uu____20656 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20656  in
                FStar_Range.set_use_range uu____20654 uu____20655  in
              FStar_Ident.set_lid_range lid uu____20653  in
            let uu____20657 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20663  ->
                      match uu___6_20663 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20666 -> false))
               in
            if uu____20657
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20685 =
                      let uu____20687 =
                        let uu____20689 = get_range env  in
                        FStar_Range.string_of_range uu____20689  in
                      let uu____20690 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20692 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20687 uu____20690 uu____20692
                       in
                    failwith uu____20685)
                  in
               match (binders, univs1) with
               | ([],uu____20713) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20739,uu____20740::uu____20741::uu____20742) ->
                   let uu____20763 =
                     let uu____20765 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20767 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20765 uu____20767
                      in
                   failwith uu____20763
               | uu____20778 ->
                   let uu____20793 =
                     let uu____20798 =
                       let uu____20799 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20799)  in
                     inst_tscheme_with uu____20798 insts  in
                   (match uu____20793 with
                    | (uu____20812,t) ->
                        let t1 =
                          let uu____20815 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20815 t  in
                        let uu____20816 =
                          let uu____20817 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20817.FStar_Syntax_Syntax.n  in
                        (match uu____20816 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20852 -> failwith "Impossible")))
        | uu____20860 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20884 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20884 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20897,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20904 = find1 l2  in
            (match uu____20904 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20911 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20911 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20915 = find1 l  in
            (match uu____20915 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20920 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20920
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____20941 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____20941 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____20947) ->
            FStar_List.length bs
        | uu____20986 ->
            let uu____20987 =
              let uu____20993 =
                let uu____20995 = FStar_Ident.string_of_lid name  in
                let uu____20997 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20995 uu____20997
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20993)
               in
            FStar_Errors.raise_error uu____20987 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21016 = lookup_qname env l1  in
      match uu____21016 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21019;
              FStar_Syntax_Syntax.sigrng = uu____21020;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21022;
              FStar_Syntax_Syntax.sigattrs = uu____21023;_},uu____21024),uu____21025)
          -> q
      | uu____21076 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21100 =
          let uu____21101 =
            let uu____21103 = FStar_Util.string_of_int i  in
            let uu____21105 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21103 uu____21105
             in
          failwith uu____21101  in
        let uu____21108 = lookup_datacon env lid  in
        match uu____21108 with
        | (uu____21113,t) ->
            let uu____21115 =
              let uu____21116 = FStar_Syntax_Subst.compress t  in
              uu____21116.FStar_Syntax_Syntax.n  in
            (match uu____21115 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21120) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21164 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21164
                      FStar_Pervasives_Native.fst)
             | uu____21175 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21189 = lookup_qname env l  in
      match uu____21189 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21191,uu____21192,uu____21193);
              FStar_Syntax_Syntax.sigrng = uu____21194;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21196;
              FStar_Syntax_Syntax.sigattrs = uu____21197;_},uu____21198),uu____21199)
          ->
          FStar_Util.for_some
            (fun uu___7_21252  ->
               match uu___7_21252 with
               | FStar_Syntax_Syntax.Projector uu____21254 -> true
               | uu____21260 -> false) quals
      | uu____21262 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21276 = lookup_qname env lid  in
      match uu____21276 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21278,uu____21279,uu____21280,uu____21281,uu____21282,uu____21283);
              FStar_Syntax_Syntax.sigrng = uu____21284;
              FStar_Syntax_Syntax.sigquals = uu____21285;
              FStar_Syntax_Syntax.sigmeta = uu____21286;
              FStar_Syntax_Syntax.sigattrs = uu____21287;_},uu____21288),uu____21289)
          -> true
      | uu____21347 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21361 = lookup_qname env lid  in
      match uu____21361 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21363,uu____21364,uu____21365,uu____21366,uu____21367,uu____21368);
              FStar_Syntax_Syntax.sigrng = uu____21369;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21371;
              FStar_Syntax_Syntax.sigattrs = uu____21372;_},uu____21373),uu____21374)
          ->
          FStar_Util.for_some
            (fun uu___8_21435  ->
               match uu___8_21435 with
               | FStar_Syntax_Syntax.RecordType uu____21437 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21447 -> true
               | uu____21457 -> false) quals
      | uu____21459 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21469,uu____21470);
            FStar_Syntax_Syntax.sigrng = uu____21471;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21473;
            FStar_Syntax_Syntax.sigattrs = uu____21474;_},uu____21475),uu____21476)
        ->
        FStar_Util.for_some
          (fun uu___9_21533  ->
             match uu___9_21533 with
             | FStar_Syntax_Syntax.Action uu____21535 -> true
             | uu____21537 -> false) quals
    | uu____21539 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21553 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21553
  
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
      let uu____21570 =
        let uu____21571 = FStar_Syntax_Util.un_uinst head1  in
        uu____21571.FStar_Syntax_Syntax.n  in
      match uu____21570 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21577 ->
               true
           | uu____21580 -> false)
      | uu____21582 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21596 = lookup_qname env l  in
      match uu____21596 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21599),uu____21600) ->
          FStar_Util.for_some
            (fun uu___10_21648  ->
               match uu___10_21648 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21651 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21653 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21729 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21747) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21765 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21773 ->
                 FStar_Pervasives_Native.Some true
             | uu____21792 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21795 =
        let uu____21799 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21799 mapper  in
      match uu____21795 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21859 = lookup_qname env lid  in
      match uu____21859 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21863,uu____21864,tps,uu____21866,uu____21867,uu____21868);
              FStar_Syntax_Syntax.sigrng = uu____21869;
              FStar_Syntax_Syntax.sigquals = uu____21870;
              FStar_Syntax_Syntax.sigmeta = uu____21871;
              FStar_Syntax_Syntax.sigattrs = uu____21872;_},uu____21873),uu____21874)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21940 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21986  ->
              match uu____21986 with
              | (d,uu____21995) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____22011 = effect_decl_opt env l  in
      match uu____22011 with
      | FStar_Pervasives_Native.None  ->
          let uu____22026 = name_not_found l  in
          let uu____22032 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22026 uu____22032
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22060 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____22060
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22069  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22087  ->
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
        let uu____22119 = FStar_Ident.lid_equals l1 l2  in
        if uu____22119
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____22130 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22130
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____22141 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22194  ->
                        match uu____22194 with
                        | (m1,m2,uu____22208,uu____22209,uu____22210) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22141 with
              | FStar_Pervasives_Native.None  ->
                  let uu____22227 =
                    let uu____22233 =
                      let uu____22235 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____22237 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____22235
                        uu____22237
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22233)
                     in
                  FStar_Errors.raise_error uu____22227 env.range
              | FStar_Pervasives_Native.Some
                  (uu____22247,uu____22248,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22282 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22282
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
  'Auu____22302 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22302) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22331 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22357  ->
                match uu____22357 with
                | (d,uu____22364) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22331 with
      | FStar_Pervasives_Native.None  ->
          let uu____22375 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22375
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22390 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22390 with
           | (uu____22401,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22419)::(wp,uu____22421)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22477 -> failwith "Impossible"))
  
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
        | uu____22542 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22555 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22555 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22572 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22572 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22597 =
                     let uu____22603 =
                       let uu____22605 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22613 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22624 =
                         let uu____22626 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22626  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22605 uu____22613 uu____22624
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22603)
                      in
                   FStar_Errors.raise_error uu____22597
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22634 =
                     let uu____22645 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22645 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22682  ->
                        fun uu____22683  ->
                          match (uu____22682, uu____22683) with
                          | ((x,uu____22713),(t,uu____22715)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22634
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22746 =
                     let uu___1574_22747 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1574_22747.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1574_22747.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1574_22747.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1574_22747.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22746
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22759 .
    'Auu____22759 ->
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
            let uu____22800 =
              let uu____22807 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____22807)  in
            match uu____22800 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____22831 = FStar_Ident.string_of_lid eff_name  in
                     let uu____22833 = FStar_Util.string_of_int given  in
                     let uu____22835 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____22831 uu____22833 uu____22835
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____22840 = effect_decl_opt env effect_name  in
          match uu____22840 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____22862) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22883 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr =
                     inst_effect_fun_with [u_res] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____22890 =
                       let uu____22893 = get_range env  in
                       let uu____22894 =
                         let uu____22901 =
                           let uu____22902 =
                             let uu____22919 =
                               let uu____22930 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____22930 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____22919)  in
                           FStar_Syntax_Syntax.Tm_app uu____22902  in
                         FStar_Syntax_Syntax.mk uu____22901  in
                       uu____22894 FStar_Pervasives_Native.None uu____22893
                        in
                     FStar_Pervasives_Native.Some uu____22890)))
  
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
      | uu____23066 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23081 =
        let uu____23082 = FStar_Syntax_Subst.compress t  in
        uu____23082.FStar_Syntax_Syntax.n  in
      match uu____23081 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23086,c) ->
          is_reifiable_comp env c
      | uu____23108 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23128 =
           let uu____23130 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23130  in
         if uu____23128
         then
           let uu____23133 =
             let uu____23139 =
               let uu____23141 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23141
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23139)  in
           let uu____23145 = get_range env  in
           FStar_Errors.raise_error uu____23133 uu____23145
         else ());
        (let uu____23148 = effect_repr_aux true env c u_c  in
         match uu____23148 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1642_23184 = env  in
        {
          solver = (uu___1642_23184.solver);
          range = (uu___1642_23184.range);
          curmodule = (uu___1642_23184.curmodule);
          gamma = (uu___1642_23184.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1642_23184.gamma_cache);
          modules = (uu___1642_23184.modules);
          expected_typ = (uu___1642_23184.expected_typ);
          sigtab = (uu___1642_23184.sigtab);
          attrtab = (uu___1642_23184.attrtab);
          is_pattern = (uu___1642_23184.is_pattern);
          instantiate_imp = (uu___1642_23184.instantiate_imp);
          effects = (uu___1642_23184.effects);
          generalize = (uu___1642_23184.generalize);
          letrecs = (uu___1642_23184.letrecs);
          top_level = (uu___1642_23184.top_level);
          check_uvars = (uu___1642_23184.check_uvars);
          use_eq = (uu___1642_23184.use_eq);
          is_iface = (uu___1642_23184.is_iface);
          admit = (uu___1642_23184.admit);
          lax = (uu___1642_23184.lax);
          lax_universes = (uu___1642_23184.lax_universes);
          phase1 = (uu___1642_23184.phase1);
          failhard = (uu___1642_23184.failhard);
          nosynth = (uu___1642_23184.nosynth);
          uvar_subtyping = (uu___1642_23184.uvar_subtyping);
          tc_term = (uu___1642_23184.tc_term);
          type_of = (uu___1642_23184.type_of);
          universe_of = (uu___1642_23184.universe_of);
          check_type_of = (uu___1642_23184.check_type_of);
          use_bv_sorts = (uu___1642_23184.use_bv_sorts);
          qtbl_name_and_index = (uu___1642_23184.qtbl_name_and_index);
          normalized_eff_names = (uu___1642_23184.normalized_eff_names);
          fv_delta_depths = (uu___1642_23184.fv_delta_depths);
          proof_ns = (uu___1642_23184.proof_ns);
          synth_hook = (uu___1642_23184.synth_hook);
          try_solve_implicits_hook =
            (uu___1642_23184.try_solve_implicits_hook);
          splice = (uu___1642_23184.splice);
          postprocess = (uu___1642_23184.postprocess);
          is_native_tactic = (uu___1642_23184.is_native_tactic);
          identifier_info = (uu___1642_23184.identifier_info);
          tc_hooks = (uu___1642_23184.tc_hooks);
          dsenv = (uu___1642_23184.dsenv);
          nbe = (uu___1642_23184.nbe);
          strict_args_tab = (uu___1642_23184.strict_args_tab);
          erasable_types_tab = (uu___1642_23184.erasable_types_tab)
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
    fun uu____23203  ->
      match uu____23203 with
      | (ed,quals) ->
          let effects =
            let uu___1651_23217 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1651_23217.order);
              joins = (uu___1651_23217.joins)
            }  in
          let uu___1654_23226 = env  in
          {
            solver = (uu___1654_23226.solver);
            range = (uu___1654_23226.range);
            curmodule = (uu___1654_23226.curmodule);
            gamma = (uu___1654_23226.gamma);
            gamma_sig = (uu___1654_23226.gamma_sig);
            gamma_cache = (uu___1654_23226.gamma_cache);
            modules = (uu___1654_23226.modules);
            expected_typ = (uu___1654_23226.expected_typ);
            sigtab = (uu___1654_23226.sigtab);
            attrtab = (uu___1654_23226.attrtab);
            is_pattern = (uu___1654_23226.is_pattern);
            instantiate_imp = (uu___1654_23226.instantiate_imp);
            effects;
            generalize = (uu___1654_23226.generalize);
            letrecs = (uu___1654_23226.letrecs);
            top_level = (uu___1654_23226.top_level);
            check_uvars = (uu___1654_23226.check_uvars);
            use_eq = (uu___1654_23226.use_eq);
            is_iface = (uu___1654_23226.is_iface);
            admit = (uu___1654_23226.admit);
            lax = (uu___1654_23226.lax);
            lax_universes = (uu___1654_23226.lax_universes);
            phase1 = (uu___1654_23226.phase1);
            failhard = (uu___1654_23226.failhard);
            nosynth = (uu___1654_23226.nosynth);
            uvar_subtyping = (uu___1654_23226.uvar_subtyping);
            tc_term = (uu___1654_23226.tc_term);
            type_of = (uu___1654_23226.type_of);
            universe_of = (uu___1654_23226.universe_of);
            check_type_of = (uu___1654_23226.check_type_of);
            use_bv_sorts = (uu___1654_23226.use_bv_sorts);
            qtbl_name_and_index = (uu___1654_23226.qtbl_name_and_index);
            normalized_eff_names = (uu___1654_23226.normalized_eff_names);
            fv_delta_depths = (uu___1654_23226.fv_delta_depths);
            proof_ns = (uu___1654_23226.proof_ns);
            synth_hook = (uu___1654_23226.synth_hook);
            try_solve_implicits_hook =
              (uu___1654_23226.try_solve_implicits_hook);
            splice = (uu___1654_23226.splice);
            postprocess = (uu___1654_23226.postprocess);
            is_native_tactic = (uu___1654_23226.is_native_tactic);
            identifier_info = (uu___1654_23226.identifier_info);
            tc_hooks = (uu___1654_23226.tc_hooks);
            dsenv = (uu___1654_23226.dsenv);
            nbe = (uu___1654_23226.nbe);
            strict_args_tab = (uu___1654_23226.strict_args_tab);
            erasable_types_tab = (uu___1654_23226.erasable_types_tab)
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
                let uu____23287 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____23287
                  (fun uu____23308  ->
                     match uu____23308 with
                     | (c1,g1) ->
                         let uu____23319 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____23319
                           (fun uu____23340  ->
                              match uu____23340 with
                              | (c2,g2) ->
                                  let uu____23351 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____23351)))
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
                                let uu____23508 = l1 u t wp e  in
                                l2 u t FStar_Syntax_Syntax.tun uu____23508))
                | uu____23509 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_ts env1 c =
            let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
            let uu____23575 =
              inst_tscheme_with lift_ts ct.FStar_Syntax_Syntax.comp_univs  in
            match uu____23575 with
            | (uu____23584,lift_t) ->
                let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
                let uu____23603 =
                  let uu____23604 =
                    let uu___1695_23605 = ct  in
                    let uu____23606 =
                      let uu____23617 =
                        let uu____23626 =
                          let uu____23627 =
                            let uu____23634 =
                              let uu____23635 =
                                let uu____23652 =
                                  let uu____23663 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ
                                     in
                                  [uu____23663; wp]  in
                                (lift_t, uu____23652)  in
                              FStar_Syntax_Syntax.Tm_app uu____23635  in
                            FStar_Syntax_Syntax.mk uu____23634  in
                          uu____23627 FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                           in
                        FStar_All.pipe_right uu____23626
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____23617]  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___1695_23605.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = tgt;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___1695_23605.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args = uu____23606;
                      FStar_Syntax_Syntax.flags =
                        (uu___1695_23605.FStar_Syntax_Syntax.flags)
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____23604  in
                (uu____23603, FStar_TypeChecker_Common.trivial_guard)
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____23768 = inst_tscheme_with lift_t [u]  in
            match uu____23768 with
            | (uu____23775,lift_t1) ->
                let uu____23777 =
                  let uu____23784 =
                    let uu____23785 =
                      let uu____23802 =
                        let uu____23813 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____23822 =
                          let uu____23833 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____23842 =
                            let uu____23853 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____23853]  in
                          uu____23833 :: uu____23842  in
                        uu____23813 :: uu____23822  in
                      (lift_t1, uu____23802)  in
                    FStar_Syntax_Syntax.Tm_app uu____23785  in
                  FStar_Syntax_Syntax.mk uu____23784  in
                uu____23777 FStar_Pervasives_Native.None
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
            | uu____24003 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24054  ->
                    match uu____24054 with
                    | (e,uu____24062) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24085 =
            match uu____24085 with
            | (i,j) ->
                let uu____24096 = FStar_Ident.lid_equals i j  in
                if uu____24096
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _24103  -> FStar_Pervasives_Native.Some _24103)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24132 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24142 = FStar_Ident.lid_equals i k  in
                        if uu____24142
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24156 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24156
                                  then []
                                  else
                                    (let uu____24163 =
                                       let uu____24172 =
                                         find_edge order1 (i, k)  in
                                       let uu____24175 =
                                         find_edge order1 (k, j)  in
                                       (uu____24172, uu____24175)  in
                                     match uu____24163 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24190 =
                                           compose_edges e1 e2  in
                                         [uu____24190]
                                     | uu____24191 -> [])))))
                 in
              FStar_List.append order1 uu____24132  in
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
                  let uu____24221 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24224 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____24224
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24221
                  then
                    let uu____24231 =
                      let uu____24237 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24237)
                       in
                    let uu____24241 = get_range env  in
                    FStar_Errors.raise_error uu____24231 uu____24241
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt =
                               let uu____24319 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24319
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24371 =
                                             let uu____24380 =
                                               find_edge order2 (i, k)  in
                                             let uu____24383 =
                                               find_edge order2 (j, k)  in
                                             (uu____24380, uu____24383)  in
                                           match uu____24371 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____24425,uu____24426)
                                                    ->
                                                    let uu____24433 =
                                                      let uu____24440 =
                                                        let uu____24442 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24442
                                                         in
                                                      let uu____24445 =
                                                        let uu____24447 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24447
                                                         in
                                                      (uu____24440,
                                                        uu____24445)
                                                       in
                                                    (match uu____24433 with
                                                     | (true ,true ) ->
                                                         let uu____24464 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____24464
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
                                           | uu____24507 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1792_24580 = env.effects  in
             { decls = (uu___1792_24580.decls); order = order2; joins }  in
           let uu___1795_24581 = env  in
           {
             solver = (uu___1795_24581.solver);
             range = (uu___1795_24581.range);
             curmodule = (uu___1795_24581.curmodule);
             gamma = (uu___1795_24581.gamma);
             gamma_sig = (uu___1795_24581.gamma_sig);
             gamma_cache = (uu___1795_24581.gamma_cache);
             modules = (uu___1795_24581.modules);
             expected_typ = (uu___1795_24581.expected_typ);
             sigtab = (uu___1795_24581.sigtab);
             attrtab = (uu___1795_24581.attrtab);
             is_pattern = (uu___1795_24581.is_pattern);
             instantiate_imp = (uu___1795_24581.instantiate_imp);
             effects;
             generalize = (uu___1795_24581.generalize);
             letrecs = (uu___1795_24581.letrecs);
             top_level = (uu___1795_24581.top_level);
             check_uvars = (uu___1795_24581.check_uvars);
             use_eq = (uu___1795_24581.use_eq);
             is_iface = (uu___1795_24581.is_iface);
             admit = (uu___1795_24581.admit);
             lax = (uu___1795_24581.lax);
             lax_universes = (uu___1795_24581.lax_universes);
             phase1 = (uu___1795_24581.phase1);
             failhard = (uu___1795_24581.failhard);
             nosynth = (uu___1795_24581.nosynth);
             uvar_subtyping = (uu___1795_24581.uvar_subtyping);
             tc_term = (uu___1795_24581.tc_term);
             type_of = (uu___1795_24581.type_of);
             universe_of = (uu___1795_24581.universe_of);
             check_type_of = (uu___1795_24581.check_type_of);
             use_bv_sorts = (uu___1795_24581.use_bv_sorts);
             qtbl_name_and_index = (uu___1795_24581.qtbl_name_and_index);
             normalized_eff_names = (uu___1795_24581.normalized_eff_names);
             fv_delta_depths = (uu___1795_24581.fv_delta_depths);
             proof_ns = (uu___1795_24581.proof_ns);
             synth_hook = (uu___1795_24581.synth_hook);
             try_solve_implicits_hook =
               (uu___1795_24581.try_solve_implicits_hook);
             splice = (uu___1795_24581.splice);
             postprocess = (uu___1795_24581.postprocess);
             is_native_tactic = (uu___1795_24581.is_native_tactic);
             identifier_info = (uu___1795_24581.identifier_info);
             tc_hooks = (uu___1795_24581.tc_hooks);
             dsenv = (uu___1795_24581.dsenv);
             nbe = (uu___1795_24581.nbe);
             strict_args_tab = (uu___1795_24581.strict_args_tab);
             erasable_types_tab = (uu___1795_24581.erasable_types_tab)
           })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1799_24593 = env  in
      {
        solver = (uu___1799_24593.solver);
        range = (uu___1799_24593.range);
        curmodule = (uu___1799_24593.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1799_24593.gamma_sig);
        gamma_cache = (uu___1799_24593.gamma_cache);
        modules = (uu___1799_24593.modules);
        expected_typ = (uu___1799_24593.expected_typ);
        sigtab = (uu___1799_24593.sigtab);
        attrtab = (uu___1799_24593.attrtab);
        is_pattern = (uu___1799_24593.is_pattern);
        instantiate_imp = (uu___1799_24593.instantiate_imp);
        effects = (uu___1799_24593.effects);
        generalize = (uu___1799_24593.generalize);
        letrecs = (uu___1799_24593.letrecs);
        top_level = (uu___1799_24593.top_level);
        check_uvars = (uu___1799_24593.check_uvars);
        use_eq = (uu___1799_24593.use_eq);
        is_iface = (uu___1799_24593.is_iface);
        admit = (uu___1799_24593.admit);
        lax = (uu___1799_24593.lax);
        lax_universes = (uu___1799_24593.lax_universes);
        phase1 = (uu___1799_24593.phase1);
        failhard = (uu___1799_24593.failhard);
        nosynth = (uu___1799_24593.nosynth);
        uvar_subtyping = (uu___1799_24593.uvar_subtyping);
        tc_term = (uu___1799_24593.tc_term);
        type_of = (uu___1799_24593.type_of);
        universe_of = (uu___1799_24593.universe_of);
        check_type_of = (uu___1799_24593.check_type_of);
        use_bv_sorts = (uu___1799_24593.use_bv_sorts);
        qtbl_name_and_index = (uu___1799_24593.qtbl_name_and_index);
        normalized_eff_names = (uu___1799_24593.normalized_eff_names);
        fv_delta_depths = (uu___1799_24593.fv_delta_depths);
        proof_ns = (uu___1799_24593.proof_ns);
        synth_hook = (uu___1799_24593.synth_hook);
        try_solve_implicits_hook = (uu___1799_24593.try_solve_implicits_hook);
        splice = (uu___1799_24593.splice);
        postprocess = (uu___1799_24593.postprocess);
        is_native_tactic = (uu___1799_24593.is_native_tactic);
        identifier_info = (uu___1799_24593.identifier_info);
        tc_hooks = (uu___1799_24593.tc_hooks);
        dsenv = (uu___1799_24593.dsenv);
        nbe = (uu___1799_24593.nbe);
        strict_args_tab = (uu___1799_24593.strict_args_tab);
        erasable_types_tab = (uu___1799_24593.erasable_types_tab)
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
            (let uu___1812_24651 = env  in
             {
               solver = (uu___1812_24651.solver);
               range = (uu___1812_24651.range);
               curmodule = (uu___1812_24651.curmodule);
               gamma = rest;
               gamma_sig = (uu___1812_24651.gamma_sig);
               gamma_cache = (uu___1812_24651.gamma_cache);
               modules = (uu___1812_24651.modules);
               expected_typ = (uu___1812_24651.expected_typ);
               sigtab = (uu___1812_24651.sigtab);
               attrtab = (uu___1812_24651.attrtab);
               is_pattern = (uu___1812_24651.is_pattern);
               instantiate_imp = (uu___1812_24651.instantiate_imp);
               effects = (uu___1812_24651.effects);
               generalize = (uu___1812_24651.generalize);
               letrecs = (uu___1812_24651.letrecs);
               top_level = (uu___1812_24651.top_level);
               check_uvars = (uu___1812_24651.check_uvars);
               use_eq = (uu___1812_24651.use_eq);
               is_iface = (uu___1812_24651.is_iface);
               admit = (uu___1812_24651.admit);
               lax = (uu___1812_24651.lax);
               lax_universes = (uu___1812_24651.lax_universes);
               phase1 = (uu___1812_24651.phase1);
               failhard = (uu___1812_24651.failhard);
               nosynth = (uu___1812_24651.nosynth);
               uvar_subtyping = (uu___1812_24651.uvar_subtyping);
               tc_term = (uu___1812_24651.tc_term);
               type_of = (uu___1812_24651.type_of);
               universe_of = (uu___1812_24651.universe_of);
               check_type_of = (uu___1812_24651.check_type_of);
               use_bv_sorts = (uu___1812_24651.use_bv_sorts);
               qtbl_name_and_index = (uu___1812_24651.qtbl_name_and_index);
               normalized_eff_names = (uu___1812_24651.normalized_eff_names);
               fv_delta_depths = (uu___1812_24651.fv_delta_depths);
               proof_ns = (uu___1812_24651.proof_ns);
               synth_hook = (uu___1812_24651.synth_hook);
               try_solve_implicits_hook =
                 (uu___1812_24651.try_solve_implicits_hook);
               splice = (uu___1812_24651.splice);
               postprocess = (uu___1812_24651.postprocess);
               is_native_tactic = (uu___1812_24651.is_native_tactic);
               identifier_info = (uu___1812_24651.identifier_info);
               tc_hooks = (uu___1812_24651.tc_hooks);
               dsenv = (uu___1812_24651.dsenv);
               nbe = (uu___1812_24651.nbe);
               strict_args_tab = (uu___1812_24651.strict_args_tab);
               erasable_types_tab = (uu___1812_24651.erasable_types_tab)
             }))
    | uu____24652 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24681  ->
             match uu____24681 with | (x,uu____24689) -> push_bv env1 x) env
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
            let uu___1826_24724 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1826_24724.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1826_24724.FStar_Syntax_Syntax.index);
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
        let uu____24797 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24797 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24825 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24825)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1847_24841 = env  in
      {
        solver = (uu___1847_24841.solver);
        range = (uu___1847_24841.range);
        curmodule = (uu___1847_24841.curmodule);
        gamma = (uu___1847_24841.gamma);
        gamma_sig = (uu___1847_24841.gamma_sig);
        gamma_cache = (uu___1847_24841.gamma_cache);
        modules = (uu___1847_24841.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1847_24841.sigtab);
        attrtab = (uu___1847_24841.attrtab);
        is_pattern = (uu___1847_24841.is_pattern);
        instantiate_imp = (uu___1847_24841.instantiate_imp);
        effects = (uu___1847_24841.effects);
        generalize = (uu___1847_24841.generalize);
        letrecs = (uu___1847_24841.letrecs);
        top_level = (uu___1847_24841.top_level);
        check_uvars = (uu___1847_24841.check_uvars);
        use_eq = false;
        is_iface = (uu___1847_24841.is_iface);
        admit = (uu___1847_24841.admit);
        lax = (uu___1847_24841.lax);
        lax_universes = (uu___1847_24841.lax_universes);
        phase1 = (uu___1847_24841.phase1);
        failhard = (uu___1847_24841.failhard);
        nosynth = (uu___1847_24841.nosynth);
        uvar_subtyping = (uu___1847_24841.uvar_subtyping);
        tc_term = (uu___1847_24841.tc_term);
        type_of = (uu___1847_24841.type_of);
        universe_of = (uu___1847_24841.universe_of);
        check_type_of = (uu___1847_24841.check_type_of);
        use_bv_sorts = (uu___1847_24841.use_bv_sorts);
        qtbl_name_and_index = (uu___1847_24841.qtbl_name_and_index);
        normalized_eff_names = (uu___1847_24841.normalized_eff_names);
        fv_delta_depths = (uu___1847_24841.fv_delta_depths);
        proof_ns = (uu___1847_24841.proof_ns);
        synth_hook = (uu___1847_24841.synth_hook);
        try_solve_implicits_hook = (uu___1847_24841.try_solve_implicits_hook);
        splice = (uu___1847_24841.splice);
        postprocess = (uu___1847_24841.postprocess);
        is_native_tactic = (uu___1847_24841.is_native_tactic);
        identifier_info = (uu___1847_24841.identifier_info);
        tc_hooks = (uu___1847_24841.tc_hooks);
        dsenv = (uu___1847_24841.dsenv);
        nbe = (uu___1847_24841.nbe);
        strict_args_tab = (uu___1847_24841.strict_args_tab);
        erasable_types_tab = (uu___1847_24841.erasable_types_tab)
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
    let uu____24872 = expected_typ env_  in
    ((let uu___1854_24878 = env_  in
      {
        solver = (uu___1854_24878.solver);
        range = (uu___1854_24878.range);
        curmodule = (uu___1854_24878.curmodule);
        gamma = (uu___1854_24878.gamma);
        gamma_sig = (uu___1854_24878.gamma_sig);
        gamma_cache = (uu___1854_24878.gamma_cache);
        modules = (uu___1854_24878.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1854_24878.sigtab);
        attrtab = (uu___1854_24878.attrtab);
        is_pattern = (uu___1854_24878.is_pattern);
        instantiate_imp = (uu___1854_24878.instantiate_imp);
        effects = (uu___1854_24878.effects);
        generalize = (uu___1854_24878.generalize);
        letrecs = (uu___1854_24878.letrecs);
        top_level = (uu___1854_24878.top_level);
        check_uvars = (uu___1854_24878.check_uvars);
        use_eq = false;
        is_iface = (uu___1854_24878.is_iface);
        admit = (uu___1854_24878.admit);
        lax = (uu___1854_24878.lax);
        lax_universes = (uu___1854_24878.lax_universes);
        phase1 = (uu___1854_24878.phase1);
        failhard = (uu___1854_24878.failhard);
        nosynth = (uu___1854_24878.nosynth);
        uvar_subtyping = (uu___1854_24878.uvar_subtyping);
        tc_term = (uu___1854_24878.tc_term);
        type_of = (uu___1854_24878.type_of);
        universe_of = (uu___1854_24878.universe_of);
        check_type_of = (uu___1854_24878.check_type_of);
        use_bv_sorts = (uu___1854_24878.use_bv_sorts);
        qtbl_name_and_index = (uu___1854_24878.qtbl_name_and_index);
        normalized_eff_names = (uu___1854_24878.normalized_eff_names);
        fv_delta_depths = (uu___1854_24878.fv_delta_depths);
        proof_ns = (uu___1854_24878.proof_ns);
        synth_hook = (uu___1854_24878.synth_hook);
        try_solve_implicits_hook = (uu___1854_24878.try_solve_implicits_hook);
        splice = (uu___1854_24878.splice);
        postprocess = (uu___1854_24878.postprocess);
        is_native_tactic = (uu___1854_24878.is_native_tactic);
        identifier_info = (uu___1854_24878.identifier_info);
        tc_hooks = (uu___1854_24878.tc_hooks);
        dsenv = (uu___1854_24878.dsenv);
        nbe = (uu___1854_24878.nbe);
        strict_args_tab = (uu___1854_24878.strict_args_tab);
        erasable_types_tab = (uu___1854_24878.erasable_types_tab)
      }), uu____24872)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24890 =
      let uu____24893 = FStar_Ident.id_of_text ""  in [uu____24893]  in
    FStar_Ident.lid_of_ids uu____24890  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24900 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24900
        then
          let uu____24905 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24905 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1862_24933 = env  in
       {
         solver = (uu___1862_24933.solver);
         range = (uu___1862_24933.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1862_24933.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1862_24933.expected_typ);
         sigtab = (uu___1862_24933.sigtab);
         attrtab = (uu___1862_24933.attrtab);
         is_pattern = (uu___1862_24933.is_pattern);
         instantiate_imp = (uu___1862_24933.instantiate_imp);
         effects = (uu___1862_24933.effects);
         generalize = (uu___1862_24933.generalize);
         letrecs = (uu___1862_24933.letrecs);
         top_level = (uu___1862_24933.top_level);
         check_uvars = (uu___1862_24933.check_uvars);
         use_eq = (uu___1862_24933.use_eq);
         is_iface = (uu___1862_24933.is_iface);
         admit = (uu___1862_24933.admit);
         lax = (uu___1862_24933.lax);
         lax_universes = (uu___1862_24933.lax_universes);
         phase1 = (uu___1862_24933.phase1);
         failhard = (uu___1862_24933.failhard);
         nosynth = (uu___1862_24933.nosynth);
         uvar_subtyping = (uu___1862_24933.uvar_subtyping);
         tc_term = (uu___1862_24933.tc_term);
         type_of = (uu___1862_24933.type_of);
         universe_of = (uu___1862_24933.universe_of);
         check_type_of = (uu___1862_24933.check_type_of);
         use_bv_sorts = (uu___1862_24933.use_bv_sorts);
         qtbl_name_and_index = (uu___1862_24933.qtbl_name_and_index);
         normalized_eff_names = (uu___1862_24933.normalized_eff_names);
         fv_delta_depths = (uu___1862_24933.fv_delta_depths);
         proof_ns = (uu___1862_24933.proof_ns);
         synth_hook = (uu___1862_24933.synth_hook);
         try_solve_implicits_hook =
           (uu___1862_24933.try_solve_implicits_hook);
         splice = (uu___1862_24933.splice);
         postprocess = (uu___1862_24933.postprocess);
         is_native_tactic = (uu___1862_24933.is_native_tactic);
         identifier_info = (uu___1862_24933.identifier_info);
         tc_hooks = (uu___1862_24933.tc_hooks);
         dsenv = (uu___1862_24933.dsenv);
         nbe = (uu___1862_24933.nbe);
         strict_args_tab = (uu___1862_24933.strict_args_tab);
         erasable_types_tab = (uu___1862_24933.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24985)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24989,(uu____24990,t)))::tl1
          ->
          let uu____25011 =
            let uu____25014 = FStar_Syntax_Free.uvars t  in
            ext out uu____25014  in
          aux uu____25011 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25017;
            FStar_Syntax_Syntax.index = uu____25018;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25026 =
            let uu____25029 = FStar_Syntax_Free.uvars t  in
            ext out uu____25029  in
          aux uu____25026 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25087)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25091,(uu____25092,t)))::tl1
          ->
          let uu____25113 =
            let uu____25116 = FStar_Syntax_Free.univs t  in
            ext out uu____25116  in
          aux uu____25113 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25119;
            FStar_Syntax_Syntax.index = uu____25120;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25128 =
            let uu____25131 = FStar_Syntax_Free.univs t  in
            ext out uu____25131  in
          aux uu____25128 tl1
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
          let uu____25193 = FStar_Util.set_add uname out  in
          aux uu____25193 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25196,(uu____25197,t)))::tl1
          ->
          let uu____25218 =
            let uu____25221 = FStar_Syntax_Free.univnames t  in
            ext out uu____25221  in
          aux uu____25218 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25224;
            FStar_Syntax_Syntax.index = uu____25225;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25233 =
            let uu____25236 = FStar_Syntax_Free.univnames t  in
            ext out uu____25236  in
          aux uu____25233 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_25257  ->
            match uu___11_25257 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____25261 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____25274 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____25285 =
      let uu____25294 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____25294
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____25285 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____25342 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_25355  ->
              match uu___12_25355 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____25358 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____25358
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____25364) ->
                  let uu____25381 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____25381))
       in
    FStar_All.pipe_right uu____25342 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_25395  ->
    match uu___13_25395 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____25401 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____25401
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____25424  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____25479) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25512,uu____25513) -> false  in
      let uu____25527 =
        FStar_List.tryFind
          (fun uu____25549  ->
             match uu____25549 with | (p,uu____25560) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25527 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25579,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25609 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25609
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2005_25631 = e  in
        {
          solver = (uu___2005_25631.solver);
          range = (uu___2005_25631.range);
          curmodule = (uu___2005_25631.curmodule);
          gamma = (uu___2005_25631.gamma);
          gamma_sig = (uu___2005_25631.gamma_sig);
          gamma_cache = (uu___2005_25631.gamma_cache);
          modules = (uu___2005_25631.modules);
          expected_typ = (uu___2005_25631.expected_typ);
          sigtab = (uu___2005_25631.sigtab);
          attrtab = (uu___2005_25631.attrtab);
          is_pattern = (uu___2005_25631.is_pattern);
          instantiate_imp = (uu___2005_25631.instantiate_imp);
          effects = (uu___2005_25631.effects);
          generalize = (uu___2005_25631.generalize);
          letrecs = (uu___2005_25631.letrecs);
          top_level = (uu___2005_25631.top_level);
          check_uvars = (uu___2005_25631.check_uvars);
          use_eq = (uu___2005_25631.use_eq);
          is_iface = (uu___2005_25631.is_iface);
          admit = (uu___2005_25631.admit);
          lax = (uu___2005_25631.lax);
          lax_universes = (uu___2005_25631.lax_universes);
          phase1 = (uu___2005_25631.phase1);
          failhard = (uu___2005_25631.failhard);
          nosynth = (uu___2005_25631.nosynth);
          uvar_subtyping = (uu___2005_25631.uvar_subtyping);
          tc_term = (uu___2005_25631.tc_term);
          type_of = (uu___2005_25631.type_of);
          universe_of = (uu___2005_25631.universe_of);
          check_type_of = (uu___2005_25631.check_type_of);
          use_bv_sorts = (uu___2005_25631.use_bv_sorts);
          qtbl_name_and_index = (uu___2005_25631.qtbl_name_and_index);
          normalized_eff_names = (uu___2005_25631.normalized_eff_names);
          fv_delta_depths = (uu___2005_25631.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2005_25631.synth_hook);
          try_solve_implicits_hook =
            (uu___2005_25631.try_solve_implicits_hook);
          splice = (uu___2005_25631.splice);
          postprocess = (uu___2005_25631.postprocess);
          is_native_tactic = (uu___2005_25631.is_native_tactic);
          identifier_info = (uu___2005_25631.identifier_info);
          tc_hooks = (uu___2005_25631.tc_hooks);
          dsenv = (uu___2005_25631.dsenv);
          nbe = (uu___2005_25631.nbe);
          strict_args_tab = (uu___2005_25631.strict_args_tab);
          erasable_types_tab = (uu___2005_25631.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2014_25679 = e  in
      {
        solver = (uu___2014_25679.solver);
        range = (uu___2014_25679.range);
        curmodule = (uu___2014_25679.curmodule);
        gamma = (uu___2014_25679.gamma);
        gamma_sig = (uu___2014_25679.gamma_sig);
        gamma_cache = (uu___2014_25679.gamma_cache);
        modules = (uu___2014_25679.modules);
        expected_typ = (uu___2014_25679.expected_typ);
        sigtab = (uu___2014_25679.sigtab);
        attrtab = (uu___2014_25679.attrtab);
        is_pattern = (uu___2014_25679.is_pattern);
        instantiate_imp = (uu___2014_25679.instantiate_imp);
        effects = (uu___2014_25679.effects);
        generalize = (uu___2014_25679.generalize);
        letrecs = (uu___2014_25679.letrecs);
        top_level = (uu___2014_25679.top_level);
        check_uvars = (uu___2014_25679.check_uvars);
        use_eq = (uu___2014_25679.use_eq);
        is_iface = (uu___2014_25679.is_iface);
        admit = (uu___2014_25679.admit);
        lax = (uu___2014_25679.lax);
        lax_universes = (uu___2014_25679.lax_universes);
        phase1 = (uu___2014_25679.phase1);
        failhard = (uu___2014_25679.failhard);
        nosynth = (uu___2014_25679.nosynth);
        uvar_subtyping = (uu___2014_25679.uvar_subtyping);
        tc_term = (uu___2014_25679.tc_term);
        type_of = (uu___2014_25679.type_of);
        universe_of = (uu___2014_25679.universe_of);
        check_type_of = (uu___2014_25679.check_type_of);
        use_bv_sorts = (uu___2014_25679.use_bv_sorts);
        qtbl_name_and_index = (uu___2014_25679.qtbl_name_and_index);
        normalized_eff_names = (uu___2014_25679.normalized_eff_names);
        fv_delta_depths = (uu___2014_25679.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2014_25679.synth_hook);
        try_solve_implicits_hook = (uu___2014_25679.try_solve_implicits_hook);
        splice = (uu___2014_25679.splice);
        postprocess = (uu___2014_25679.postprocess);
        is_native_tactic = (uu___2014_25679.is_native_tactic);
        identifier_info = (uu___2014_25679.identifier_info);
        tc_hooks = (uu___2014_25679.tc_hooks);
        dsenv = (uu___2014_25679.dsenv);
        nbe = (uu___2014_25679.nbe);
        strict_args_tab = (uu___2014_25679.strict_args_tab);
        erasable_types_tab = (uu___2014_25679.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25695 = FStar_Syntax_Free.names t  in
      let uu____25698 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25695 uu____25698
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25721 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25721
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25731 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25731
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25752 =
      match uu____25752 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25772 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25772)
       in
    let uu____25780 =
      let uu____25784 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25784 FStar_List.rev  in
    FStar_All.pipe_right uu____25780 (FStar_String.concat " ")
  
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
                  (let uu____25852 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25852 with
                   | FStar_Pervasives_Native.Some uu____25856 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25859 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25869;
        FStar_TypeChecker_Common.univ_ineqs = uu____25870;
        FStar_TypeChecker_Common.implicits = uu____25871;_} -> true
    | uu____25881 -> false
  
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
          let uu___2058_25903 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2058_25903.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2058_25903.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2058_25903.FStar_TypeChecker_Common.implicits)
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
          let uu____25942 = FStar_Options.defensive ()  in
          if uu____25942
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25948 =
              let uu____25950 =
                let uu____25952 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25952  in
              Prims.op_Negation uu____25950  in
            (if uu____25948
             then
               let uu____25959 =
                 let uu____25965 =
                   let uu____25967 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25969 =
                     let uu____25971 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25971
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25967 uu____25969
                    in
                 (FStar_Errors.Warning_Defensive, uu____25965)  in
               FStar_Errors.log_issue rng uu____25959
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
          let uu____26011 =
            let uu____26013 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26013  in
          if uu____26011
          then ()
          else
            (let uu____26018 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26018 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26044 =
            let uu____26046 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26046  in
          if uu____26044
          then ()
          else
            (let uu____26051 = bound_vars e  in
             def_check_closed_in rng msg uu____26051 t)
  
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
          let uu___2095_26090 = g  in
          let uu____26091 =
            let uu____26092 =
              let uu____26093 =
                let uu____26100 =
                  let uu____26101 =
                    let uu____26118 =
                      let uu____26129 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____26129]  in
                    (f, uu____26118)  in
                  FStar_Syntax_Syntax.Tm_app uu____26101  in
                FStar_Syntax_Syntax.mk uu____26100  in
              uu____26093 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _26166  -> FStar_TypeChecker_Common.NonTrivial _26166)
              uu____26092
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____26091;
            FStar_TypeChecker_Common.deferred =
              (uu___2095_26090.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2095_26090.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2095_26090.FStar_TypeChecker_Common.implicits)
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
          let uu___2102_26184 = g  in
          let uu____26185 =
            let uu____26186 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26186  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26185;
            FStar_TypeChecker_Common.deferred =
              (uu___2102_26184.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2102_26184.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2102_26184.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2107_26203 = g  in
          let uu____26204 =
            let uu____26205 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____26205  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26204;
            FStar_TypeChecker_Common.deferred =
              (uu___2107_26203.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2107_26203.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2107_26203.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2111_26207 = g  in
          let uu____26208 =
            let uu____26209 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26209  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26208;
            FStar_TypeChecker_Common.deferred =
              (uu___2111_26207.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2111_26207.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2111_26207.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____26216 ->
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
                       let uu____26293 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____26293
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2134_26300 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2134_26300.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2134_26300.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2134_26300.FStar_TypeChecker_Common.implicits)
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
               let uu____26334 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____26334
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
            let uu___2149_26361 = g  in
            let uu____26362 =
              let uu____26363 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____26363  in
            {
              FStar_TypeChecker_Common.guard_f = uu____26362;
              FStar_TypeChecker_Common.deferred =
                (uu___2149_26361.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2149_26361.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2149_26361.FStar_TypeChecker_Common.implicits)
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
              let uu____26421 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26421 with
              | FStar_Pervasives_Native.Some
                  (uu____26446::(tm,uu____26448)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26512 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26530 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26530;
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
                      let uu___2171_26562 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2171_26562.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2171_26562.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2171_26562.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____26616 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____26673  ->
                      fun b  ->
                        match uu____26673 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____26715 =
                              let uu____26728 = reason b  in
                              new_implicit_var_aux uu____26728 r env sort
                                FStar_Syntax_Syntax.Strict
                                FStar_Pervasives_Native.None
                               in
                            (match uu____26715 with
                             | (t,uu____26745,g_t) ->
                                 let uu____26759 =
                                   let uu____26762 =
                                     let uu____26765 =
                                       let uu____26766 =
                                         let uu____26773 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26773, t)  in
                                       FStar_Syntax_Syntax.NT uu____26766  in
                                     [uu____26765]  in
                                   FStar_List.append substs1 uu____26762  in
                                 let uu____26784 = conj_guard g g_t  in
                                 (uu____26759,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26784))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____26616
              (fun uu____26813  ->
                 match uu____26813 with
                 | (uu____26830,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26846  -> ());
    push = (fun uu____26848  -> ());
    pop = (fun uu____26851  -> ());
    snapshot =
      (fun uu____26854  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26873  -> fun uu____26874  -> ());
    encode_sig = (fun uu____26889  -> fun uu____26890  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26896 =
             let uu____26903 = FStar_Options.peek ()  in (e, g, uu____26903)
              in
           [uu____26896]);
    solve = (fun uu____26919  -> fun uu____26920  -> fun uu____26921  -> ());
    finish = (fun uu____26928  -> ());
    refresh = (fun uu____26930  -> ())
  } 