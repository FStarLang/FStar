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
  fun projectee  -> match projectee with | Beta  -> true | uu____106 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____117 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____128 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____140 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____158 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____169 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____180 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____191 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____202 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____213 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____225 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____246 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____273 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____300 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____324 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____335 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____346 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____357 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____368 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____379 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____390 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____401 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____412 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____423 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____434 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____445 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____456 -> false
  
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
      | uu____516 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____542 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____553 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____564 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____576 -> false
  
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
    ;
  polymonadic_binds:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env ->
         FStar_Syntax_Syntax.comp_typ ->
           FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStar_Syntax_Syntax.comp_typ ->
               FStar_Syntax_Syntax.cflag Prims.list ->
                 FStar_Range.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list
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
  use_eq_strict: Prims.bool ;
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
  mpreprocess:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
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
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> joins
  
let (__proj__Mkeffects__item__polymonadic_binds :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env ->
         FStar_Syntax_Syntax.comp_typ ->
           FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStar_Syntax_Syntax.comp_typ ->
               FStar_Syntax_Syntax.cflag Prims.list ->
                 FStar_Range.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> polymonadic_binds
  
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq_strict
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> splice1
  
let (__proj__Mkenv__item__mpreprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> mpreprocess
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
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
type polymonadic_bind_t =
  env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.comp_typ ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicit = FStar_TypeChecker_Common.implicit
type implicits = FStar_TypeChecker_Common.implicits
type guard_t = FStar_TypeChecker_Common.guard_t
let (preprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun tau  -> fun tm  -> env.mpreprocess env tau tm 
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
           (fun uu___0_14336  ->
              match uu___0_14336 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14339 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14339  in
                  let uu____14340 =
                    let uu____14341 = FStar_Syntax_Subst.compress y  in
                    uu____14341.FStar_Syntax_Syntax.n  in
                  (match uu____14340 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14345 =
                         let uu___324_14346 = y1  in
                         let uu____14347 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___324_14346.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___324_14346.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14347
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14345
                   | uu____14350 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___330_14364 = env  in
      let uu____14365 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___330_14364.solver);
        range = (uu___330_14364.range);
        curmodule = (uu___330_14364.curmodule);
        gamma = uu____14365;
        gamma_sig = (uu___330_14364.gamma_sig);
        gamma_cache = (uu___330_14364.gamma_cache);
        modules = (uu___330_14364.modules);
        expected_typ = (uu___330_14364.expected_typ);
        sigtab = (uu___330_14364.sigtab);
        attrtab = (uu___330_14364.attrtab);
        instantiate_imp = (uu___330_14364.instantiate_imp);
        effects = (uu___330_14364.effects);
        generalize = (uu___330_14364.generalize);
        letrecs = (uu___330_14364.letrecs);
        top_level = (uu___330_14364.top_level);
        check_uvars = (uu___330_14364.check_uvars);
        use_eq = (uu___330_14364.use_eq);
        use_eq_strict = (uu___330_14364.use_eq_strict);
        is_iface = (uu___330_14364.is_iface);
        admit = (uu___330_14364.admit);
        lax = (uu___330_14364.lax);
        lax_universes = (uu___330_14364.lax_universes);
        phase1 = (uu___330_14364.phase1);
        failhard = (uu___330_14364.failhard);
        nosynth = (uu___330_14364.nosynth);
        uvar_subtyping = (uu___330_14364.uvar_subtyping);
        tc_term = (uu___330_14364.tc_term);
        type_of = (uu___330_14364.type_of);
        universe_of = (uu___330_14364.universe_of);
        check_type_of = (uu___330_14364.check_type_of);
        use_bv_sorts = (uu___330_14364.use_bv_sorts);
        qtbl_name_and_index = (uu___330_14364.qtbl_name_and_index);
        normalized_eff_names = (uu___330_14364.normalized_eff_names);
        fv_delta_depths = (uu___330_14364.fv_delta_depths);
        proof_ns = (uu___330_14364.proof_ns);
        synth_hook = (uu___330_14364.synth_hook);
        try_solve_implicits_hook = (uu___330_14364.try_solve_implicits_hook);
        splice = (uu___330_14364.splice);
        mpreprocess = (uu___330_14364.mpreprocess);
        postprocess = (uu___330_14364.postprocess);
        is_native_tactic = (uu___330_14364.is_native_tactic);
        identifier_info = (uu___330_14364.identifier_info);
        tc_hooks = (uu___330_14364.tc_hooks);
        dsenv = (uu___330_14364.dsenv);
        nbe = (uu___330_14364.nbe);
        strict_args_tab = (uu___330_14364.strict_args_tab);
        erasable_types_tab = (uu___330_14364.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14373  -> fun uu____14374  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___337_14396 = env  in
      {
        solver = (uu___337_14396.solver);
        range = (uu___337_14396.range);
        curmodule = (uu___337_14396.curmodule);
        gamma = (uu___337_14396.gamma);
        gamma_sig = (uu___337_14396.gamma_sig);
        gamma_cache = (uu___337_14396.gamma_cache);
        modules = (uu___337_14396.modules);
        expected_typ = (uu___337_14396.expected_typ);
        sigtab = (uu___337_14396.sigtab);
        attrtab = (uu___337_14396.attrtab);
        instantiate_imp = (uu___337_14396.instantiate_imp);
        effects = (uu___337_14396.effects);
        generalize = (uu___337_14396.generalize);
        letrecs = (uu___337_14396.letrecs);
        top_level = (uu___337_14396.top_level);
        check_uvars = (uu___337_14396.check_uvars);
        use_eq = (uu___337_14396.use_eq);
        use_eq_strict = (uu___337_14396.use_eq_strict);
        is_iface = (uu___337_14396.is_iface);
        admit = (uu___337_14396.admit);
        lax = (uu___337_14396.lax);
        lax_universes = (uu___337_14396.lax_universes);
        phase1 = (uu___337_14396.phase1);
        failhard = (uu___337_14396.failhard);
        nosynth = (uu___337_14396.nosynth);
        uvar_subtyping = (uu___337_14396.uvar_subtyping);
        tc_term = (uu___337_14396.tc_term);
        type_of = (uu___337_14396.type_of);
        universe_of = (uu___337_14396.universe_of);
        check_type_of = (uu___337_14396.check_type_of);
        use_bv_sorts = (uu___337_14396.use_bv_sorts);
        qtbl_name_and_index = (uu___337_14396.qtbl_name_and_index);
        normalized_eff_names = (uu___337_14396.normalized_eff_names);
        fv_delta_depths = (uu___337_14396.fv_delta_depths);
        proof_ns = (uu___337_14396.proof_ns);
        synth_hook = (uu___337_14396.synth_hook);
        try_solve_implicits_hook = (uu___337_14396.try_solve_implicits_hook);
        splice = (uu___337_14396.splice);
        mpreprocess = (uu___337_14396.mpreprocess);
        postprocess = (uu___337_14396.postprocess);
        is_native_tactic = (uu___337_14396.is_native_tactic);
        identifier_info = (uu___337_14396.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___337_14396.dsenv);
        nbe = (uu___337_14396.nbe);
        strict_args_tab = (uu___337_14396.strict_args_tab);
        erasable_types_tab = (uu___337_14396.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___341_14408 = e  in
      let uu____14409 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___341_14408.solver);
        range = (uu___341_14408.range);
        curmodule = (uu___341_14408.curmodule);
        gamma = (uu___341_14408.gamma);
        gamma_sig = (uu___341_14408.gamma_sig);
        gamma_cache = (uu___341_14408.gamma_cache);
        modules = (uu___341_14408.modules);
        expected_typ = (uu___341_14408.expected_typ);
        sigtab = (uu___341_14408.sigtab);
        attrtab = (uu___341_14408.attrtab);
        instantiate_imp = (uu___341_14408.instantiate_imp);
        effects = (uu___341_14408.effects);
        generalize = (uu___341_14408.generalize);
        letrecs = (uu___341_14408.letrecs);
        top_level = (uu___341_14408.top_level);
        check_uvars = (uu___341_14408.check_uvars);
        use_eq = (uu___341_14408.use_eq);
        use_eq_strict = (uu___341_14408.use_eq_strict);
        is_iface = (uu___341_14408.is_iface);
        admit = (uu___341_14408.admit);
        lax = (uu___341_14408.lax);
        lax_universes = (uu___341_14408.lax_universes);
        phase1 = (uu___341_14408.phase1);
        failhard = (uu___341_14408.failhard);
        nosynth = (uu___341_14408.nosynth);
        uvar_subtyping = (uu___341_14408.uvar_subtyping);
        tc_term = (uu___341_14408.tc_term);
        type_of = (uu___341_14408.type_of);
        universe_of = (uu___341_14408.universe_of);
        check_type_of = (uu___341_14408.check_type_of);
        use_bv_sorts = (uu___341_14408.use_bv_sorts);
        qtbl_name_and_index = (uu___341_14408.qtbl_name_and_index);
        normalized_eff_names = (uu___341_14408.normalized_eff_names);
        fv_delta_depths = (uu___341_14408.fv_delta_depths);
        proof_ns = (uu___341_14408.proof_ns);
        synth_hook = (uu___341_14408.synth_hook);
        try_solve_implicits_hook = (uu___341_14408.try_solve_implicits_hook);
        splice = (uu___341_14408.splice);
        mpreprocess = (uu___341_14408.mpreprocess);
        postprocess = (uu___341_14408.postprocess);
        is_native_tactic = (uu___341_14408.is_native_tactic);
        identifier_info = (uu___341_14408.identifier_info);
        tc_hooks = (uu___341_14408.tc_hooks);
        dsenv = uu____14409;
        nbe = (uu___341_14408.nbe);
        strict_args_tab = (uu___341_14408.strict_args_tab);
        erasable_types_tab = (uu___341_14408.erasable_types_tab)
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
      | (NoDelta ,uu____14438) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14441,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14443,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14446 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14460 . unit -> 'Auu____14460 FStar_Util.smap =
  fun uu____14467  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14473 . unit -> 'Auu____14473 FStar_Util.smap =
  fun uu____14480  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14618 = new_gamma_cache ()  in
                  let uu____14621 = new_sigtab ()  in
                  let uu____14624 = new_sigtab ()  in
                  let uu____14631 =
                    let uu____14646 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14646, FStar_Pervasives_Native.None)  in
                  let uu____14667 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14671 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14675 = FStar_Options.using_facts_from ()  in
                  let uu____14676 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14679 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14680 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14694 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14618;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14621;
                    attrtab = uu____14624;
                    instantiate_imp = true;
                    effects =
                      {
                        decls = [];
                        order = [];
                        joins = [];
                        polymonadic_binds = []
                      };
                    generalize = true;
                    letrecs = [];
                    top_level = false;
                    check_uvars = false;
                    use_eq = false;
                    use_eq_strict = false;
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
                    qtbl_name_and_index = uu____14631;
                    normalized_eff_names = uu____14667;
                    fv_delta_depths = uu____14671;
                    proof_ns = uu____14675;
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
                    mpreprocess =
                      (fun e  ->
                         fun tau  ->
                           fun tm  -> failwith "no preprocessor available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____14809  -> false);
                    identifier_info = uu____14676;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14679;
                    nbe = nbe1;
                    strict_args_tab = uu____14680;
                    erasable_types_tab = uu____14694
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
  fun uu____14888  ->
    let uu____14889 = FStar_ST.op_Bang query_indices  in
    match uu____14889 with
    | [] -> failwith "Empty query indices!"
    | uu____14944 ->
        let uu____14954 =
          let uu____14964 =
            let uu____14972 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14972  in
          let uu____15026 = FStar_ST.op_Bang query_indices  in uu____14964 ::
            uu____15026
           in
        FStar_ST.op_Colon_Equals query_indices uu____14954
  
let (pop_query_indices : unit -> unit) =
  fun uu____15122  ->
    let uu____15123 = FStar_ST.op_Bang query_indices  in
    match uu____15123 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15250  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15287  ->
    match uu____15287 with
    | (l,n1) ->
        let uu____15297 = FStar_ST.op_Bang query_indices  in
        (match uu____15297 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15419 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15442  ->
    let uu____15443 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15443
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15511 =
       let uu____15514 = FStar_ST.op_Bang stack  in env :: uu____15514  in
     FStar_ST.op_Colon_Equals stack uu____15511);
    (let uu___415_15563 = env  in
     let uu____15564 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15567 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15570 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15577 =
       let uu____15592 =
         let uu____15596 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15596  in
       let uu____15628 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15592, uu____15628)  in
     let uu____15677 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____15680 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____15683 =
       let uu____15686 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____15686  in
     let uu____15706 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15719 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___415_15563.solver);
       range = (uu___415_15563.range);
       curmodule = (uu___415_15563.curmodule);
       gamma = (uu___415_15563.gamma);
       gamma_sig = (uu___415_15563.gamma_sig);
       gamma_cache = uu____15564;
       modules = (uu___415_15563.modules);
       expected_typ = (uu___415_15563.expected_typ);
       sigtab = uu____15567;
       attrtab = uu____15570;
       instantiate_imp = (uu___415_15563.instantiate_imp);
       effects = (uu___415_15563.effects);
       generalize = (uu___415_15563.generalize);
       letrecs = (uu___415_15563.letrecs);
       top_level = (uu___415_15563.top_level);
       check_uvars = (uu___415_15563.check_uvars);
       use_eq = (uu___415_15563.use_eq);
       use_eq_strict = (uu___415_15563.use_eq_strict);
       is_iface = (uu___415_15563.is_iface);
       admit = (uu___415_15563.admit);
       lax = (uu___415_15563.lax);
       lax_universes = (uu___415_15563.lax_universes);
       phase1 = (uu___415_15563.phase1);
       failhard = (uu___415_15563.failhard);
       nosynth = (uu___415_15563.nosynth);
       uvar_subtyping = (uu___415_15563.uvar_subtyping);
       tc_term = (uu___415_15563.tc_term);
       type_of = (uu___415_15563.type_of);
       universe_of = (uu___415_15563.universe_of);
       check_type_of = (uu___415_15563.check_type_of);
       use_bv_sorts = (uu___415_15563.use_bv_sorts);
       qtbl_name_and_index = uu____15577;
       normalized_eff_names = uu____15677;
       fv_delta_depths = uu____15680;
       proof_ns = (uu___415_15563.proof_ns);
       synth_hook = (uu___415_15563.synth_hook);
       try_solve_implicits_hook = (uu___415_15563.try_solve_implicits_hook);
       splice = (uu___415_15563.splice);
       mpreprocess = (uu___415_15563.mpreprocess);
       postprocess = (uu___415_15563.postprocess);
       is_native_tactic = (uu___415_15563.is_native_tactic);
       identifier_info = uu____15683;
       tc_hooks = (uu___415_15563.tc_hooks);
       dsenv = (uu___415_15563.dsenv);
       nbe = (uu___415_15563.nbe);
       strict_args_tab = uu____15706;
       erasable_types_tab = uu____15719
     })
  
let (pop_stack : unit -> env) =
  fun uu____15729  ->
    let uu____15730 = FStar_ST.op_Bang stack  in
    match uu____15730 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15784 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15874  ->
           let uu____15875 = snapshot_stack env  in
           match uu____15875 with
           | (stack_depth,env1) ->
               let uu____15909 = snapshot_query_indices ()  in
               (match uu____15909 with
                | (query_indices_depth,()) ->
                    let uu____15942 = (env1.solver).snapshot msg  in
                    (match uu____15942 with
                     | (solver_depth,()) ->
                         let uu____15999 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____15999 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___440_16066 = env1  in
                                 {
                                   solver = (uu___440_16066.solver);
                                   range = (uu___440_16066.range);
                                   curmodule = (uu___440_16066.curmodule);
                                   gamma = (uu___440_16066.gamma);
                                   gamma_sig = (uu___440_16066.gamma_sig);
                                   gamma_cache = (uu___440_16066.gamma_cache);
                                   modules = (uu___440_16066.modules);
                                   expected_typ =
                                     (uu___440_16066.expected_typ);
                                   sigtab = (uu___440_16066.sigtab);
                                   attrtab = (uu___440_16066.attrtab);
                                   instantiate_imp =
                                     (uu___440_16066.instantiate_imp);
                                   effects = (uu___440_16066.effects);
                                   generalize = (uu___440_16066.generalize);
                                   letrecs = (uu___440_16066.letrecs);
                                   top_level = (uu___440_16066.top_level);
                                   check_uvars = (uu___440_16066.check_uvars);
                                   use_eq = (uu___440_16066.use_eq);
                                   use_eq_strict =
                                     (uu___440_16066.use_eq_strict);
                                   is_iface = (uu___440_16066.is_iface);
                                   admit = (uu___440_16066.admit);
                                   lax = (uu___440_16066.lax);
                                   lax_universes =
                                     (uu___440_16066.lax_universes);
                                   phase1 = (uu___440_16066.phase1);
                                   failhard = (uu___440_16066.failhard);
                                   nosynth = (uu___440_16066.nosynth);
                                   uvar_subtyping =
                                     (uu___440_16066.uvar_subtyping);
                                   tc_term = (uu___440_16066.tc_term);
                                   type_of = (uu___440_16066.type_of);
                                   universe_of = (uu___440_16066.universe_of);
                                   check_type_of =
                                     (uu___440_16066.check_type_of);
                                   use_bv_sorts =
                                     (uu___440_16066.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___440_16066.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___440_16066.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___440_16066.fv_delta_depths);
                                   proof_ns = (uu___440_16066.proof_ns);
                                   synth_hook = (uu___440_16066.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___440_16066.try_solve_implicits_hook);
                                   splice = (uu___440_16066.splice);
                                   mpreprocess = (uu___440_16066.mpreprocess);
                                   postprocess = (uu___440_16066.postprocess);
                                   is_native_tactic =
                                     (uu___440_16066.is_native_tactic);
                                   identifier_info =
                                     (uu___440_16066.identifier_info);
                                   tc_hooks = (uu___440_16066.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___440_16066.nbe);
                                   strict_args_tab =
                                     (uu___440_16066.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___440_16066.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16100  ->
             let uu____16101 =
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
             match uu____16101 with
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
                             ((let uu____16281 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16281
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____16297 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____16297
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16329,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16371 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16401  ->
                  match uu____16401 with
                  | (m,uu____16409) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16371 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___485_16424 = env  in
               {
                 solver = (uu___485_16424.solver);
                 range = (uu___485_16424.range);
                 curmodule = (uu___485_16424.curmodule);
                 gamma = (uu___485_16424.gamma);
                 gamma_sig = (uu___485_16424.gamma_sig);
                 gamma_cache = (uu___485_16424.gamma_cache);
                 modules = (uu___485_16424.modules);
                 expected_typ = (uu___485_16424.expected_typ);
                 sigtab = (uu___485_16424.sigtab);
                 attrtab = (uu___485_16424.attrtab);
                 instantiate_imp = (uu___485_16424.instantiate_imp);
                 effects = (uu___485_16424.effects);
                 generalize = (uu___485_16424.generalize);
                 letrecs = (uu___485_16424.letrecs);
                 top_level = (uu___485_16424.top_level);
                 check_uvars = (uu___485_16424.check_uvars);
                 use_eq = (uu___485_16424.use_eq);
                 use_eq_strict = (uu___485_16424.use_eq_strict);
                 is_iface = (uu___485_16424.is_iface);
                 admit = (uu___485_16424.admit);
                 lax = (uu___485_16424.lax);
                 lax_universes = (uu___485_16424.lax_universes);
                 phase1 = (uu___485_16424.phase1);
                 failhard = (uu___485_16424.failhard);
                 nosynth = (uu___485_16424.nosynth);
                 uvar_subtyping = (uu___485_16424.uvar_subtyping);
                 tc_term = (uu___485_16424.tc_term);
                 type_of = (uu___485_16424.type_of);
                 universe_of = (uu___485_16424.universe_of);
                 check_type_of = (uu___485_16424.check_type_of);
                 use_bv_sorts = (uu___485_16424.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___485_16424.normalized_eff_names);
                 fv_delta_depths = (uu___485_16424.fv_delta_depths);
                 proof_ns = (uu___485_16424.proof_ns);
                 synth_hook = (uu___485_16424.synth_hook);
                 try_solve_implicits_hook =
                   (uu___485_16424.try_solve_implicits_hook);
                 splice = (uu___485_16424.splice);
                 mpreprocess = (uu___485_16424.mpreprocess);
                 postprocess = (uu___485_16424.postprocess);
                 is_native_tactic = (uu___485_16424.is_native_tactic);
                 identifier_info = (uu___485_16424.identifier_info);
                 tc_hooks = (uu___485_16424.tc_hooks);
                 dsenv = (uu___485_16424.dsenv);
                 nbe = (uu___485_16424.nbe);
                 strict_args_tab = (uu___485_16424.strict_args_tab);
                 erasable_types_tab = (uu___485_16424.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16441,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___494_16457 = env  in
               {
                 solver = (uu___494_16457.solver);
                 range = (uu___494_16457.range);
                 curmodule = (uu___494_16457.curmodule);
                 gamma = (uu___494_16457.gamma);
                 gamma_sig = (uu___494_16457.gamma_sig);
                 gamma_cache = (uu___494_16457.gamma_cache);
                 modules = (uu___494_16457.modules);
                 expected_typ = (uu___494_16457.expected_typ);
                 sigtab = (uu___494_16457.sigtab);
                 attrtab = (uu___494_16457.attrtab);
                 instantiate_imp = (uu___494_16457.instantiate_imp);
                 effects = (uu___494_16457.effects);
                 generalize = (uu___494_16457.generalize);
                 letrecs = (uu___494_16457.letrecs);
                 top_level = (uu___494_16457.top_level);
                 check_uvars = (uu___494_16457.check_uvars);
                 use_eq = (uu___494_16457.use_eq);
                 use_eq_strict = (uu___494_16457.use_eq_strict);
                 is_iface = (uu___494_16457.is_iface);
                 admit = (uu___494_16457.admit);
                 lax = (uu___494_16457.lax);
                 lax_universes = (uu___494_16457.lax_universes);
                 phase1 = (uu___494_16457.phase1);
                 failhard = (uu___494_16457.failhard);
                 nosynth = (uu___494_16457.nosynth);
                 uvar_subtyping = (uu___494_16457.uvar_subtyping);
                 tc_term = (uu___494_16457.tc_term);
                 type_of = (uu___494_16457.type_of);
                 universe_of = (uu___494_16457.universe_of);
                 check_type_of = (uu___494_16457.check_type_of);
                 use_bv_sorts = (uu___494_16457.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___494_16457.normalized_eff_names);
                 fv_delta_depths = (uu___494_16457.fv_delta_depths);
                 proof_ns = (uu___494_16457.proof_ns);
                 synth_hook = (uu___494_16457.synth_hook);
                 try_solve_implicits_hook =
                   (uu___494_16457.try_solve_implicits_hook);
                 splice = (uu___494_16457.splice);
                 mpreprocess = (uu___494_16457.mpreprocess);
                 postprocess = (uu___494_16457.postprocess);
                 is_native_tactic = (uu___494_16457.is_native_tactic);
                 identifier_info = (uu___494_16457.identifier_info);
                 tc_hooks = (uu___494_16457.tc_hooks);
                 dsenv = (uu___494_16457.dsenv);
                 nbe = (uu___494_16457.nbe);
                 strict_args_tab = (uu___494_16457.strict_args_tab);
                 erasable_types_tab = (uu___494_16457.erasable_types_tab)
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
        (let uu___501_16500 = e  in
         {
           solver = (uu___501_16500.solver);
           range = r;
           curmodule = (uu___501_16500.curmodule);
           gamma = (uu___501_16500.gamma);
           gamma_sig = (uu___501_16500.gamma_sig);
           gamma_cache = (uu___501_16500.gamma_cache);
           modules = (uu___501_16500.modules);
           expected_typ = (uu___501_16500.expected_typ);
           sigtab = (uu___501_16500.sigtab);
           attrtab = (uu___501_16500.attrtab);
           instantiate_imp = (uu___501_16500.instantiate_imp);
           effects = (uu___501_16500.effects);
           generalize = (uu___501_16500.generalize);
           letrecs = (uu___501_16500.letrecs);
           top_level = (uu___501_16500.top_level);
           check_uvars = (uu___501_16500.check_uvars);
           use_eq = (uu___501_16500.use_eq);
           use_eq_strict = (uu___501_16500.use_eq_strict);
           is_iface = (uu___501_16500.is_iface);
           admit = (uu___501_16500.admit);
           lax = (uu___501_16500.lax);
           lax_universes = (uu___501_16500.lax_universes);
           phase1 = (uu___501_16500.phase1);
           failhard = (uu___501_16500.failhard);
           nosynth = (uu___501_16500.nosynth);
           uvar_subtyping = (uu___501_16500.uvar_subtyping);
           tc_term = (uu___501_16500.tc_term);
           type_of = (uu___501_16500.type_of);
           universe_of = (uu___501_16500.universe_of);
           check_type_of = (uu___501_16500.check_type_of);
           use_bv_sorts = (uu___501_16500.use_bv_sorts);
           qtbl_name_and_index = (uu___501_16500.qtbl_name_and_index);
           normalized_eff_names = (uu___501_16500.normalized_eff_names);
           fv_delta_depths = (uu___501_16500.fv_delta_depths);
           proof_ns = (uu___501_16500.proof_ns);
           synth_hook = (uu___501_16500.synth_hook);
           try_solve_implicits_hook =
             (uu___501_16500.try_solve_implicits_hook);
           splice = (uu___501_16500.splice);
           mpreprocess = (uu___501_16500.mpreprocess);
           postprocess = (uu___501_16500.postprocess);
           is_native_tactic = (uu___501_16500.is_native_tactic);
           identifier_info = (uu___501_16500.identifier_info);
           tc_hooks = (uu___501_16500.tc_hooks);
           dsenv = (uu___501_16500.dsenv);
           nbe = (uu___501_16500.nbe);
           strict_args_tab = (uu___501_16500.strict_args_tab);
           erasable_types_tab = (uu___501_16500.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16520 =
        let uu____16521 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16521 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16520
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16576 =
          let uu____16577 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16577 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16576
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16632 =
          let uu____16633 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16633 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16632
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16688 =
        let uu____16689 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16689 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16688
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___518_16753 = env  in
      {
        solver = (uu___518_16753.solver);
        range = (uu___518_16753.range);
        curmodule = lid;
        gamma = (uu___518_16753.gamma);
        gamma_sig = (uu___518_16753.gamma_sig);
        gamma_cache = (uu___518_16753.gamma_cache);
        modules = (uu___518_16753.modules);
        expected_typ = (uu___518_16753.expected_typ);
        sigtab = (uu___518_16753.sigtab);
        attrtab = (uu___518_16753.attrtab);
        instantiate_imp = (uu___518_16753.instantiate_imp);
        effects = (uu___518_16753.effects);
        generalize = (uu___518_16753.generalize);
        letrecs = (uu___518_16753.letrecs);
        top_level = (uu___518_16753.top_level);
        check_uvars = (uu___518_16753.check_uvars);
        use_eq = (uu___518_16753.use_eq);
        use_eq_strict = (uu___518_16753.use_eq_strict);
        is_iface = (uu___518_16753.is_iface);
        admit = (uu___518_16753.admit);
        lax = (uu___518_16753.lax);
        lax_universes = (uu___518_16753.lax_universes);
        phase1 = (uu___518_16753.phase1);
        failhard = (uu___518_16753.failhard);
        nosynth = (uu___518_16753.nosynth);
        uvar_subtyping = (uu___518_16753.uvar_subtyping);
        tc_term = (uu___518_16753.tc_term);
        type_of = (uu___518_16753.type_of);
        universe_of = (uu___518_16753.universe_of);
        check_type_of = (uu___518_16753.check_type_of);
        use_bv_sorts = (uu___518_16753.use_bv_sorts);
        qtbl_name_and_index = (uu___518_16753.qtbl_name_and_index);
        normalized_eff_names = (uu___518_16753.normalized_eff_names);
        fv_delta_depths = (uu___518_16753.fv_delta_depths);
        proof_ns = (uu___518_16753.proof_ns);
        synth_hook = (uu___518_16753.synth_hook);
        try_solve_implicits_hook = (uu___518_16753.try_solve_implicits_hook);
        splice = (uu___518_16753.splice);
        mpreprocess = (uu___518_16753.mpreprocess);
        postprocess = (uu___518_16753.postprocess);
        is_native_tactic = (uu___518_16753.is_native_tactic);
        identifier_info = (uu___518_16753.identifier_info);
        tc_hooks = (uu___518_16753.tc_hooks);
        dsenv = (uu___518_16753.dsenv);
        nbe = (uu___518_16753.nbe);
        strict_args_tab = (uu___518_16753.strict_args_tab);
        erasable_types_tab = (uu___518_16753.erasable_types_tab)
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
      let uu____16784 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16784
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16797 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16797)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16812 =
      let uu____16814 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16814  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16812)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16823  ->
    let uu____16824 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16824
  
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
      | ((formals,t),uu____16924) ->
          let vs = mk_univ_subst formals us  in
          let uu____16948 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16948)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16965  ->
    match uu___1_16965 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16991  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17011 = inst_tscheme t  in
      match uu____17011 with
      | (us,t1) ->
          let uu____17022 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17022)
  
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
          let uu____17047 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17049 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17047 uu____17049
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
        fun uu____17076  ->
          match uu____17076 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17090 =
                    let uu____17092 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17096 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17100 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17102 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17092 uu____17096 uu____17100 uu____17102
                     in
                  failwith uu____17090)
               else ();
               (let uu____17107 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17107))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17125 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17136 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17147 -> false
  
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
             | ([],uu____17195) -> Maybe
             | (uu____17202,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____17222 -> No  in
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
          let uu____17316 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____17316 with
          | FStar_Pervasives_Native.None  ->
              let uu____17339 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17383  ->
                     match uu___2_17383 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17422 = FStar_Ident.lid_equals lid l  in
                         if uu____17422
                         then
                           let uu____17445 =
                             let uu____17464 =
                               let uu____17479 = inst_tscheme t  in
                               FStar_Util.Inl uu____17479  in
                             let uu____17494 = FStar_Ident.range_of_lid l  in
                             (uu____17464, uu____17494)  in
                           FStar_Pervasives_Native.Some uu____17445
                         else FStar_Pervasives_Native.None
                     | uu____17547 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17339
                (fun uu____17585  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17595  ->
                        match uu___3_17595 with
                        | (uu____17598,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17600);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17601;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17602;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17603;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17604;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17605;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17627 =
                                   let uu____17629 =
                                     FStar_Syntax_Util.lids_of_sigelt se  in
                                   FStar_All.pipe_right uu____17629
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17627
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
                                  uu____17682 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17689 -> cache t  in
                            let uu____17690 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17690 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17696 =
                                   let uu____17697 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17697)
                                    in
                                 maybe_cache uu____17696)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17768 = find_in_sigtab env lid  in
         match uu____17768 with
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
      let uu____17849 = lookup_qname env lid  in
      match uu____17849 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17870,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17984 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17984 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18029 =
          let uu____18032 = lookup_attr env1 attr  in se1 :: uu____18032  in
        FStar_Util.smap_add (attrtab env1) attr uu____18029  in
      FStar_List.iter
        (fun attr  ->
           let uu____18042 =
             let uu____18043 = FStar_Syntax_Subst.compress attr  in
             uu____18043.FStar_Syntax_Syntax.n  in
           match uu____18042 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18047 =
                 let uu____18049 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18049.FStar_Ident.str  in
               add_one1 env se uu____18047
           | uu____18050 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18073) ->
          add_sigelts env ses
      | uu____18082 ->
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
        (fun uu___4_18120  ->
           match uu___4_18120 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18138 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18200,lb::[]),uu____18202) ->
            let uu____18211 =
              let uu____18220 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18229 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18220, uu____18229)  in
            FStar_Pervasives_Native.Some uu____18211
        | FStar_Syntax_Syntax.Sig_let ((uu____18242,lbs),uu____18244) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18276 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18289 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18289
                     then
                       let uu____18302 =
                         let uu____18311 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18320 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18311, uu____18320)  in
                       FStar_Pervasives_Native.Some uu____18302
                     else FStar_Pervasives_Native.None)
        | uu____18343 -> FStar_Pervasives_Native.None
  
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
                    let uu____18435 =
                      let uu____18437 =
                        let uu____18439 =
                          let uu____18441 =
                            let uu____18443 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18449 =
                              let uu____18451 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18451  in
                            Prims.op_Hat uu____18443 uu____18449  in
                          Prims.op_Hat ", expected " uu____18441  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18439
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18437
                       in
                    failwith uu____18435
                  else ());
             (let uu____18458 =
                let uu____18467 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18467, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18458))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18487,uu____18488) ->
            let uu____18493 =
              let uu____18502 =
                let uu____18507 =
                  let uu____18508 =
                    let uu____18511 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18511  in
                  (us, uu____18508)  in
                inst_ts us_opt uu____18507  in
              (uu____18502, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18493
        | uu____18530 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18619 =
          match uu____18619 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18715,uvs,t,uu____18718,uu____18719,uu____18720);
                      FStar_Syntax_Syntax.sigrng = uu____18721;
                      FStar_Syntax_Syntax.sigquals = uu____18722;
                      FStar_Syntax_Syntax.sigmeta = uu____18723;
                      FStar_Syntax_Syntax.sigattrs = uu____18724;
                      FStar_Syntax_Syntax.sigopts = uu____18725;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18750 =
                     let uu____18759 = inst_tscheme1 (uvs, t)  in
                     (uu____18759, rng)  in
                   FStar_Pervasives_Native.Some uu____18750
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18783;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18785;
                      FStar_Syntax_Syntax.sigattrs = uu____18786;
                      FStar_Syntax_Syntax.sigopts = uu____18787;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18806 =
                     let uu____18808 = in_cur_mod env l  in uu____18808 = Yes
                      in
                   if uu____18806
                   then
                     let uu____18820 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18820
                      then
                        let uu____18836 =
                          let uu____18845 = inst_tscheme1 (uvs, t)  in
                          (uu____18845, rng)  in
                        FStar_Pervasives_Native.Some uu____18836
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18878 =
                        let uu____18887 = inst_tscheme1 (uvs, t)  in
                        (uu____18887, rng)  in
                      FStar_Pervasives_Native.Some uu____18878)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18912,uu____18913);
                      FStar_Syntax_Syntax.sigrng = uu____18914;
                      FStar_Syntax_Syntax.sigquals = uu____18915;
                      FStar_Syntax_Syntax.sigmeta = uu____18916;
                      FStar_Syntax_Syntax.sigattrs = uu____18917;
                      FStar_Syntax_Syntax.sigopts = uu____18918;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18961 =
                          let uu____18970 = inst_tscheme1 (uvs, k)  in
                          (uu____18970, rng)  in
                        FStar_Pervasives_Native.Some uu____18961
                    | uu____18991 ->
                        let uu____18992 =
                          let uu____19001 =
                            let uu____19006 =
                              let uu____19007 =
                                let uu____19010 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19010
                                 in
                              (uvs, uu____19007)  in
                            inst_tscheme1 uu____19006  in
                          (uu____19001, rng)  in
                        FStar_Pervasives_Native.Some uu____18992)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19033,uu____19034);
                      FStar_Syntax_Syntax.sigrng = uu____19035;
                      FStar_Syntax_Syntax.sigquals = uu____19036;
                      FStar_Syntax_Syntax.sigmeta = uu____19037;
                      FStar_Syntax_Syntax.sigattrs = uu____19038;
                      FStar_Syntax_Syntax.sigopts = uu____19039;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19083 =
                          let uu____19092 = inst_tscheme_with (uvs, k) us  in
                          (uu____19092, rng)  in
                        FStar_Pervasives_Native.Some uu____19083
                    | uu____19113 ->
                        let uu____19114 =
                          let uu____19123 =
                            let uu____19128 =
                              let uu____19129 =
                                let uu____19132 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19132
                                 in
                              (uvs, uu____19129)  in
                            inst_tscheme_with uu____19128 us  in
                          (uu____19123, rng)  in
                        FStar_Pervasives_Native.Some uu____19114)
               | FStar_Util.Inr se ->
                   let uu____19168 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19189;
                          FStar_Syntax_Syntax.sigrng = uu____19190;
                          FStar_Syntax_Syntax.sigquals = uu____19191;
                          FStar_Syntax_Syntax.sigmeta = uu____19192;
                          FStar_Syntax_Syntax.sigattrs = uu____19193;
                          FStar_Syntax_Syntax.sigopts = uu____19194;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19211 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19168
                     (FStar_Util.map_option
                        (fun uu____19259  ->
                           match uu____19259 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19290 =
          let uu____19301 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19301 mapper  in
        match uu____19290 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19375 =
              let uu____19386 =
                let uu____19393 =
                  let uu___855_19396 = t  in
                  let uu____19397 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_19396.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19397;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_19396.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19393)  in
              (uu____19386, r)  in
            FStar_Pervasives_Native.Some uu____19375
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19446 = lookup_qname env l  in
      match uu____19446 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19467 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19521 = try_lookup_bv env bv  in
      match uu____19521 with
      | FStar_Pervasives_Native.None  ->
          let uu____19536 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19536 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19552 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19553 =
            let uu____19554 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19554  in
          (uu____19552, uu____19553)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19576 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19576 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19642 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19642  in
          let uu____19643 =
            let uu____19652 =
              let uu____19657 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19657)  in
            (uu____19652, r1)  in
          FStar_Pervasives_Native.Some uu____19643
  
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
        let uu____19692 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19692 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19725,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19750 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19750  in
            let uu____19751 =
              let uu____19756 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19756, r1)  in
            FStar_Pervasives_Native.Some uu____19751
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19780 = try_lookup_lid env l  in
      match uu____19780 with
      | FStar_Pervasives_Native.None  ->
          let uu____19807 = name_not_found l  in
          let uu____19813 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19807 uu____19813
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19856  ->
              match uu___5_19856 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19860 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19881 = lookup_qname env lid  in
      match uu____19881 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19890,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19893;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19895;
              FStar_Syntax_Syntax.sigattrs = uu____19896;
              FStar_Syntax_Syntax.sigopts = uu____19897;_},FStar_Pervasives_Native.None
            ),uu____19898)
          ->
          let uu____19949 =
            let uu____19956 =
              let uu____19957 =
                let uu____19960 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19960 t  in
              (uvs, uu____19957)  in
            (uu____19956, q)  in
          FStar_Pervasives_Native.Some uu____19949
      | uu____19973 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19995 = lookup_qname env lid  in
      match uu____19995 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20000,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20003;
              FStar_Syntax_Syntax.sigquals = uu____20004;
              FStar_Syntax_Syntax.sigmeta = uu____20005;
              FStar_Syntax_Syntax.sigattrs = uu____20006;
              FStar_Syntax_Syntax.sigopts = uu____20007;_},FStar_Pervasives_Native.None
            ),uu____20008)
          ->
          let uu____20059 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20059 (uvs, t)
      | uu____20064 ->
          let uu____20065 = name_not_found lid  in
          let uu____20071 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20065 uu____20071
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20091 = lookup_qname env lid  in
      match uu____20091 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20096,uvs,t,uu____20099,uu____20100,uu____20101);
              FStar_Syntax_Syntax.sigrng = uu____20102;
              FStar_Syntax_Syntax.sigquals = uu____20103;
              FStar_Syntax_Syntax.sigmeta = uu____20104;
              FStar_Syntax_Syntax.sigattrs = uu____20105;
              FStar_Syntax_Syntax.sigopts = uu____20106;_},FStar_Pervasives_Native.None
            ),uu____20107)
          ->
          let uu____20164 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20164 (uvs, t)
      | uu____20169 ->
          let uu____20170 = name_not_found lid  in
          let uu____20176 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20170 uu____20176
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20199 = lookup_qname env lid  in
      match uu____20199 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20207,uu____20208,uu____20209,uu____20210,uu____20211,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20213;
              FStar_Syntax_Syntax.sigquals = uu____20214;
              FStar_Syntax_Syntax.sigmeta = uu____20215;
              FStar_Syntax_Syntax.sigattrs = uu____20216;
              FStar_Syntax_Syntax.sigopts = uu____20217;_},uu____20218),uu____20219)
          -> (true, dcs)
      | uu____20284 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20300 = lookup_qname env lid  in
      match uu____20300 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20301,uu____20302,uu____20303,l,uu____20305,uu____20306);
              FStar_Syntax_Syntax.sigrng = uu____20307;
              FStar_Syntax_Syntax.sigquals = uu____20308;
              FStar_Syntax_Syntax.sigmeta = uu____20309;
              FStar_Syntax_Syntax.sigattrs = uu____20310;
              FStar_Syntax_Syntax.sigopts = uu____20311;_},uu____20312),uu____20313)
          -> l
      | uu____20372 ->
          let uu____20373 =
            let uu____20375 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20375  in
          failwith uu____20373
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20445)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20502) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20526 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20526
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20561 -> FStar_Pervasives_Native.None)
          | uu____20570 -> FStar_Pervasives_Native.None
  
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
        let uu____20632 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20632
  
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
        let uu____20665 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20665
  
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
             (FStar_Util.Inl uu____20717,uu____20718) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20767),uu____20768) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20817 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20835 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20845 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20862 ->
                  let uu____20869 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20869
              | FStar_Syntax_Syntax.Sig_let ((uu____20870,lbs),uu____20872)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20888 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20888
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20895 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20911 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20921 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20922 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20929 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20930 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20931 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20944 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20945 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20973 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20973
           (fun d_opt  ->
              let uu____20986 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20986
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20996 =
                   let uu____20999 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20999  in
                 match uu____20996 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21000 =
                       let uu____21002 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21002
                        in
                     failwith uu____21000
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21007 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21007
                       then
                         let uu____21010 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21012 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21014 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21010 uu____21012 uu____21014
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
        (FStar_Util.Inr (se,uu____21039),uu____21040) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21089 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21111),uu____21112) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21161 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21183 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21183
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21216 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21216 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21238 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21247 =
                        let uu____21248 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21248.FStar_Syntax_Syntax.n  in
                      match uu____21247 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21253 -> false))
               in
            (true, uu____21238)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21276 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21276
  
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
          let uu____21348 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21348.FStar_Ident.str  in
        let uu____21349 = FStar_Util.smap_try_find tab s  in
        match uu____21349 with
        | FStar_Pervasives_Native.None  ->
            let uu____21352 = f ()  in
            (match uu____21352 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21390 =
        let uu____21391 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21391 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21425 =
        let uu____21426 = FStar_Syntax_Util.unrefine t  in
        uu____21426.FStar_Syntax_Syntax.n  in
      match uu____21425 with
      | FStar_Syntax_Syntax.Tm_type uu____21430 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21434) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21460) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21465,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21487 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21520 =
        let attrs =
          let uu____21526 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21526  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21566 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21566)
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
      let uu____21611 = lookup_qname env ftv  in
      match uu____21611 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21615) ->
          let uu____21660 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21660 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21681,t),r) ->
               let uu____21696 =
                 let uu____21697 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21697 t  in
               FStar_Pervasives_Native.Some uu____21696)
      | uu____21698 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21710 = try_lookup_effect_lid env ftv  in
      match uu____21710 with
      | FStar_Pervasives_Native.None  ->
          let uu____21713 = name_not_found ftv  in
          let uu____21719 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21713 uu____21719
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
        let uu____21743 = lookup_qname env lid0  in
        match uu____21743 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21754);
                FStar_Syntax_Syntax.sigrng = uu____21755;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21757;
                FStar_Syntax_Syntax.sigattrs = uu____21758;
                FStar_Syntax_Syntax.sigopts = uu____21759;_},FStar_Pervasives_Native.None
              ),uu____21760)
            ->
            let lid1 =
              let uu____21816 =
                let uu____21817 = FStar_Ident.range_of_lid lid  in
                let uu____21818 =
                  let uu____21819 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21819  in
                FStar_Range.set_use_range uu____21817 uu____21818  in
              FStar_Ident.set_lid_range lid uu____21816  in
            let uu____21820 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21826  ->
                      match uu___6_21826 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21829 -> false))
               in
            if uu____21820
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21848 =
                      let uu____21850 =
                        let uu____21852 = get_range env  in
                        FStar_Range.string_of_range uu____21852  in
                      let uu____21853 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21855 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21850 uu____21853 uu____21855
                       in
                    failwith uu____21848)
                  in
               match (binders, univs1) with
               | ([],uu____21876) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21902,uu____21903::uu____21904::uu____21905) ->
                   let uu____21926 =
                     let uu____21928 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21930 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21928 uu____21930
                      in
                   failwith uu____21926
               | uu____21941 ->
                   let uu____21956 =
                     let uu____21961 =
                       let uu____21962 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21962)  in
                     inst_tscheme_with uu____21961 insts  in
                   (match uu____21956 with
                    | (uu____21975,t) ->
                        let t1 =
                          let uu____21978 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21978 t  in
                        let uu____21979 =
                          let uu____21980 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21980.FStar_Syntax_Syntax.n  in
                        (match uu____21979 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22015 -> failwith "Impossible")))
        | uu____22023 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22047 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22047 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22060,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22067 = find1 l2  in
            (match uu____22067 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22074 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22074 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22078 = find1 l  in
            (match uu____22078 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22083 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22083
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22104 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22104 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22110) ->
            FStar_List.length bs
        | uu____22149 ->
            let uu____22150 =
              let uu____22156 =
                let uu____22158 = FStar_Ident.string_of_lid name  in
                let uu____22160 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22158 uu____22160
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22156)
               in
            FStar_Errors.raise_error uu____22150 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22179 = lookup_qname env l1  in
      match uu____22179 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22182;
              FStar_Syntax_Syntax.sigrng = uu____22183;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22185;
              FStar_Syntax_Syntax.sigattrs = uu____22186;
              FStar_Syntax_Syntax.sigopts = uu____22187;_},uu____22188),uu____22189)
          -> q
      | uu____22242 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22266 =
          let uu____22267 =
            let uu____22269 = FStar_Util.string_of_int i  in
            let uu____22271 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22269 uu____22271
             in
          failwith uu____22267  in
        let uu____22274 = lookup_datacon env lid  in
        match uu____22274 with
        | (uu____22279,t) ->
            let uu____22281 =
              let uu____22282 = FStar_Syntax_Subst.compress t  in
              uu____22282.FStar_Syntax_Syntax.n  in
            (match uu____22281 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22286) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____22330 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____22330
                      FStar_Pervasives_Native.fst)
             | uu____22341 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22355 = lookup_qname env l  in
      match uu____22355 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22357,uu____22358,uu____22359);
              FStar_Syntax_Syntax.sigrng = uu____22360;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22362;
              FStar_Syntax_Syntax.sigattrs = uu____22363;
              FStar_Syntax_Syntax.sigopts = uu____22364;_},uu____22365),uu____22366)
          ->
          FStar_Util.for_some
            (fun uu___7_22421  ->
               match uu___7_22421 with
               | FStar_Syntax_Syntax.Projector uu____22423 -> true
               | uu____22429 -> false) quals
      | uu____22431 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22445 = lookup_qname env lid  in
      match uu____22445 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22447,uu____22448,uu____22449,uu____22450,uu____22451,uu____22452);
              FStar_Syntax_Syntax.sigrng = uu____22453;
              FStar_Syntax_Syntax.sigquals = uu____22454;
              FStar_Syntax_Syntax.sigmeta = uu____22455;
              FStar_Syntax_Syntax.sigattrs = uu____22456;
              FStar_Syntax_Syntax.sigopts = uu____22457;_},uu____22458),uu____22459)
          -> true
      | uu____22519 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22533 = lookup_qname env lid  in
      match uu____22533 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22535,uu____22536,uu____22537,uu____22538,uu____22539,uu____22540);
              FStar_Syntax_Syntax.sigrng = uu____22541;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22543;
              FStar_Syntax_Syntax.sigattrs = uu____22544;
              FStar_Syntax_Syntax.sigopts = uu____22545;_},uu____22546),uu____22547)
          ->
          FStar_Util.for_some
            (fun uu___8_22610  ->
               match uu___8_22610 with
               | FStar_Syntax_Syntax.RecordType uu____22612 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22622 -> true
               | uu____22632 -> false) quals
      | uu____22634 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22644,uu____22645);
            FStar_Syntax_Syntax.sigrng = uu____22646;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22648;
            FStar_Syntax_Syntax.sigattrs = uu____22649;
            FStar_Syntax_Syntax.sigopts = uu____22650;_},uu____22651),uu____22652)
        ->
        FStar_Util.for_some
          (fun uu___9_22711  ->
             match uu___9_22711 with
             | FStar_Syntax_Syntax.Action uu____22713 -> true
             | uu____22715 -> false) quals
    | uu____22717 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22731 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22731
  
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
      let uu____22748 =
        let uu____22749 = FStar_Syntax_Util.un_uinst head1  in
        uu____22749.FStar_Syntax_Syntax.n  in
      match uu____22748 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22755 ->
               true
           | uu____22758 -> false)
      | uu____22760 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22774 = lookup_qname env l  in
      match uu____22774 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22777),uu____22778) ->
          FStar_Util.for_some
            (fun uu___10_22826  ->
               match uu___10_22826 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22829 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22831 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22907 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22925) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22943 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22951 ->
                 FStar_Pervasives_Native.Some true
             | uu____22970 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22973 =
        let uu____22977 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22977 mapper  in
      match uu____22973 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23037 = lookup_qname env lid  in
      match uu____23037 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23041,uu____23042,tps,uu____23044,uu____23045,uu____23046);
              FStar_Syntax_Syntax.sigrng = uu____23047;
              FStar_Syntax_Syntax.sigquals = uu____23048;
              FStar_Syntax_Syntax.sigmeta = uu____23049;
              FStar_Syntax_Syntax.sigattrs = uu____23050;
              FStar_Syntax_Syntax.sigopts = uu____23051;_},uu____23052),uu____23053)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23121 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23167  ->
              match uu____23167 with
              | (d,uu____23176) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23192 = effect_decl_opt env l  in
      match uu____23192 with
      | FStar_Pervasives_Native.None  ->
          let uu____23207 = name_not_found l  in
          let uu____23213 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23207 uu____23213
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23241 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23241 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23248  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23262  ->
            fun uu____23263  -> fun e  -> FStar_Util.return_all e))
  } 
let (join_opt :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23297 = FStar_Ident.lid_equals l1 l2  in
        if uu____23297
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23316 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23316
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23335 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23388  ->
                        match uu____23388 with
                        | (m1,m2,uu____23402,uu____23403,uu____23404) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23335 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23429,uu____23430,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23478 = join_opt env l1 l2  in
        match uu____23478 with
        | FStar_Pervasives_Native.None  ->
            let uu____23499 =
              let uu____23505 =
                let uu____23507 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23509 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23507 uu____23509
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23505)  in
            FStar_Errors.raise_error uu____23499 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23552 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23552
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
  'Auu____23572 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23572) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23601 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23627  ->
                match uu____23627 with
                | (d,uu____23634) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23601 with
      | FStar_Pervasives_Native.None  ->
          let uu____23645 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23645
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23660 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23660 with
           | (uu____23671,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23689)::(wp,uu____23691)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23747 -> failwith "Impossible"))
  
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
        | uu____23812 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23825 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23825 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23842 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23842 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23867 =
                     let uu____23873 =
                       let uu____23875 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23883 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23894 =
                         let uu____23896 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23896  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23875 uu____23883 uu____23894
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23873)
                      in
                   FStar_Errors.raise_error uu____23867
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23904 =
                     let uu____23915 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23915 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23952  ->
                        fun uu____23953  ->
                          match (uu____23952, uu____23953) with
                          | ((x,uu____23983),(t,uu____23985)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23904
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____24016 =
                     let uu___1611_24017 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1611_24017.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1611_24017.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1611_24017.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1611_24017.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24016
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24029 .
    'Auu____24029 ->
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
            let uu____24070 =
              let uu____24077 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24077)  in
            match uu____24070 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24101 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24103 = FStar_Util.string_of_int given  in
                     let uu____24105 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24101 uu____24103 uu____24105
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24110 = effect_decl_opt env effect_name  in
          match uu____24110 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24132) ->
              let uu____24143 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24143 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24161 =
                       let uu____24164 = get_range env  in
                       let uu____24165 =
                         let uu____24172 =
                           let uu____24173 =
                             let uu____24190 =
                               let uu____24201 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24201 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24190)  in
                           FStar_Syntax_Syntax.Tm_app uu____24173  in
                         FStar_Syntax_Syntax.mk uu____24172  in
                       uu____24165 FStar_Pervasives_Native.None uu____24164
                        in
                     FStar_Pervasives_Native.Some uu____24161)))
  
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
           (fun uu___11_24301  ->
              match uu___11_24301 with
              | FStar_Syntax_Syntax.Reflectable uu____24303 -> true
              | uu____24305 -> false))
  
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
      | uu____24365 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24380 =
        let uu____24381 = FStar_Syntax_Subst.compress t  in
        uu____24381.FStar_Syntax_Syntax.n  in
      match uu____24380 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24385,c) ->
          is_reifiable_comp env c
      | uu____24407 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24427 =
           let uu____24429 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24429  in
         if uu____24427
         then
           let uu____24432 =
             let uu____24438 =
               let uu____24440 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24440
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24438)  in
           let uu____24444 = get_range env  in
           FStar_Errors.raise_error uu____24432 uu____24444
         else ());
        (let uu____24447 = effect_repr_aux true env c u_c  in
         match uu____24447 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb =
        let uu____24480 = FStar_Syntax_Util.lids_of_sigelt s  in
        (uu____24480, s)  in
      let env1 =
        let uu___1688_24486 = env  in
        {
          solver = (uu___1688_24486.solver);
          range = (uu___1688_24486.range);
          curmodule = (uu___1688_24486.curmodule);
          gamma = (uu___1688_24486.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1688_24486.gamma_cache);
          modules = (uu___1688_24486.modules);
          expected_typ = (uu___1688_24486.expected_typ);
          sigtab = (uu___1688_24486.sigtab);
          attrtab = (uu___1688_24486.attrtab);
          instantiate_imp = (uu___1688_24486.instantiate_imp);
          effects = (uu___1688_24486.effects);
          generalize = (uu___1688_24486.generalize);
          letrecs = (uu___1688_24486.letrecs);
          top_level = (uu___1688_24486.top_level);
          check_uvars = (uu___1688_24486.check_uvars);
          use_eq = (uu___1688_24486.use_eq);
          use_eq_strict = (uu___1688_24486.use_eq_strict);
          is_iface = (uu___1688_24486.is_iface);
          admit = (uu___1688_24486.admit);
          lax = (uu___1688_24486.lax);
          lax_universes = (uu___1688_24486.lax_universes);
          phase1 = (uu___1688_24486.phase1);
          failhard = (uu___1688_24486.failhard);
          nosynth = (uu___1688_24486.nosynth);
          uvar_subtyping = (uu___1688_24486.uvar_subtyping);
          tc_term = (uu___1688_24486.tc_term);
          type_of = (uu___1688_24486.type_of);
          universe_of = (uu___1688_24486.universe_of);
          check_type_of = (uu___1688_24486.check_type_of);
          use_bv_sorts = (uu___1688_24486.use_bv_sorts);
          qtbl_name_and_index = (uu___1688_24486.qtbl_name_and_index);
          normalized_eff_names = (uu___1688_24486.normalized_eff_names);
          fv_delta_depths = (uu___1688_24486.fv_delta_depths);
          proof_ns = (uu___1688_24486.proof_ns);
          synth_hook = (uu___1688_24486.synth_hook);
          try_solve_implicits_hook =
            (uu___1688_24486.try_solve_implicits_hook);
          splice = (uu___1688_24486.splice);
          mpreprocess = (uu___1688_24486.mpreprocess);
          postprocess = (uu___1688_24486.postprocess);
          is_native_tactic = (uu___1688_24486.is_native_tactic);
          identifier_info = (uu___1688_24486.identifier_info);
          tc_hooks = (uu___1688_24486.tc_hooks);
          dsenv = (uu___1688_24486.dsenv);
          nbe = (uu___1688_24486.nbe);
          strict_args_tab = (uu___1688_24486.strict_args_tab);
          erasable_types_tab = (uu___1688_24486.erasable_types_tab)
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
    fun uu____24505  ->
      match uu____24505 with
      | (ed,quals) ->
          let effects =
            let uu___1697_24519 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1697_24519.order);
              joins = (uu___1697_24519.joins);
              polymonadic_binds = (uu___1697_24519.polymonadic_binds)
            }  in
          let uu___1700_24528 = env  in
          {
            solver = (uu___1700_24528.solver);
            range = (uu___1700_24528.range);
            curmodule = (uu___1700_24528.curmodule);
            gamma = (uu___1700_24528.gamma);
            gamma_sig = (uu___1700_24528.gamma_sig);
            gamma_cache = (uu___1700_24528.gamma_cache);
            modules = (uu___1700_24528.modules);
            expected_typ = (uu___1700_24528.expected_typ);
            sigtab = (uu___1700_24528.sigtab);
            attrtab = (uu___1700_24528.attrtab);
            instantiate_imp = (uu___1700_24528.instantiate_imp);
            effects;
            generalize = (uu___1700_24528.generalize);
            letrecs = (uu___1700_24528.letrecs);
            top_level = (uu___1700_24528.top_level);
            check_uvars = (uu___1700_24528.check_uvars);
            use_eq = (uu___1700_24528.use_eq);
            use_eq_strict = (uu___1700_24528.use_eq_strict);
            is_iface = (uu___1700_24528.is_iface);
            admit = (uu___1700_24528.admit);
            lax = (uu___1700_24528.lax);
            lax_universes = (uu___1700_24528.lax_universes);
            phase1 = (uu___1700_24528.phase1);
            failhard = (uu___1700_24528.failhard);
            nosynth = (uu___1700_24528.nosynth);
            uvar_subtyping = (uu___1700_24528.uvar_subtyping);
            tc_term = (uu___1700_24528.tc_term);
            type_of = (uu___1700_24528.type_of);
            universe_of = (uu___1700_24528.universe_of);
            check_type_of = (uu___1700_24528.check_type_of);
            use_bv_sorts = (uu___1700_24528.use_bv_sorts);
            qtbl_name_and_index = (uu___1700_24528.qtbl_name_and_index);
            normalized_eff_names = (uu___1700_24528.normalized_eff_names);
            fv_delta_depths = (uu___1700_24528.fv_delta_depths);
            proof_ns = (uu___1700_24528.proof_ns);
            synth_hook = (uu___1700_24528.synth_hook);
            try_solve_implicits_hook =
              (uu___1700_24528.try_solve_implicits_hook);
            splice = (uu___1700_24528.splice);
            mpreprocess = (uu___1700_24528.mpreprocess);
            postprocess = (uu___1700_24528.postprocess);
            is_native_tactic = (uu___1700_24528.is_native_tactic);
            identifier_info = (uu___1700_24528.identifier_info);
            tc_hooks = (uu___1700_24528.tc_hooks);
            dsenv = (uu___1700_24528.dsenv);
            nbe = (uu___1700_24528.nbe);
            strict_args_tab = (uu___1700_24528.strict_args_tab);
            erasable_types_tab = (uu___1700_24528.erasable_types_tab)
          }
  
let (exists_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * polymonadic_bind_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        let uu____24557 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24625  ->
                  match uu____24625 with
                  | (m1,n11,uu____24643,uu____24644) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24557 with
        | FStar_Pervasives_Native.Some (uu____24669,uu____24670,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24715 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24790 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24790
                  (fun uu____24811  ->
                     match uu____24811 with
                     | (c1,g1) ->
                         let uu____24822 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24822
                           (fun uu____24843  ->
                              match uu____24843 with
                              | (c2,g2) ->
                                  let uu____24854 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24854)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24976 = l1 u t e  in
                              l2 u t uu____24976))
                | uu____24977 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25045  ->
                    match uu____25045 with
                    | (e,uu____25053) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25076 =
            match uu____25076 with
            | (i,j) ->
                let uu____25087 = FStar_Ident.lid_equals i j  in
                if uu____25087
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25094  -> FStar_Pervasives_Native.Some _25094)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25123 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25133 = FStar_Ident.lid_equals i k  in
                        if uu____25133
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25147 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25147
                                  then []
                                  else
                                    (let uu____25154 =
                                       let uu____25163 =
                                         find_edge order1 (i, k)  in
                                       let uu____25166 =
                                         find_edge order1 (k, j)  in
                                       (uu____25163, uu____25166)  in
                                     match uu____25154 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25181 =
                                           compose_edges e1 e2  in
                                         [uu____25181]
                                     | uu____25182 -> [])))))
                 in
              FStar_List.append order1 uu____25123  in
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
                  let uu____25212 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25215 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25215
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25212
                  then
                    let uu____25222 =
                      let uu____25228 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25228)
                       in
                    let uu____25232 = get_range env  in
                    FStar_Errors.raise_error uu____25222 uu____25232
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25310 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25310
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25362 =
                                             let uu____25371 =
                                               find_edge order2 (i, k)  in
                                             let uu____25374 =
                                               find_edge order2 (j, k)  in
                                             (uu____25371, uu____25374)  in
                                           match uu____25362 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25416,uu____25417)
                                                    ->
                                                    let uu____25424 =
                                                      let uu____25431 =
                                                        let uu____25433 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25433
                                                         in
                                                      let uu____25436 =
                                                        let uu____25438 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25438
                                                         in
                                                      (uu____25431,
                                                        uu____25436)
                                                       in
                                                    (match uu____25424 with
                                                     | (true ,true ) ->
                                                         let uu____25455 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25455
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
                                           | uu____25498 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25550 =
                                   let uu____25552 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25552
                                     FStar_Util.is_some
                                    in
                                 if uu____25550
                                 then
                                   let uu____25601 =
                                     let uu____25607 =
                                       let uu____25609 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25611 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25613 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25615 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25609 uu____25611 uu____25613
                                         uu____25615
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25607)
                                      in
                                   FStar_Errors.raise_error uu____25601
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1821_25654 = env.effects  in
             {
               decls = (uu___1821_25654.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1821_25654.polymonadic_binds)
             }  in
           let uu___1824_25655 = env  in
           {
             solver = (uu___1824_25655.solver);
             range = (uu___1824_25655.range);
             curmodule = (uu___1824_25655.curmodule);
             gamma = (uu___1824_25655.gamma);
             gamma_sig = (uu___1824_25655.gamma_sig);
             gamma_cache = (uu___1824_25655.gamma_cache);
             modules = (uu___1824_25655.modules);
             expected_typ = (uu___1824_25655.expected_typ);
             sigtab = (uu___1824_25655.sigtab);
             attrtab = (uu___1824_25655.attrtab);
             instantiate_imp = (uu___1824_25655.instantiate_imp);
             effects;
             generalize = (uu___1824_25655.generalize);
             letrecs = (uu___1824_25655.letrecs);
             top_level = (uu___1824_25655.top_level);
             check_uvars = (uu___1824_25655.check_uvars);
             use_eq = (uu___1824_25655.use_eq);
             use_eq_strict = (uu___1824_25655.use_eq_strict);
             is_iface = (uu___1824_25655.is_iface);
             admit = (uu___1824_25655.admit);
             lax = (uu___1824_25655.lax);
             lax_universes = (uu___1824_25655.lax_universes);
             phase1 = (uu___1824_25655.phase1);
             failhard = (uu___1824_25655.failhard);
             nosynth = (uu___1824_25655.nosynth);
             uvar_subtyping = (uu___1824_25655.uvar_subtyping);
             tc_term = (uu___1824_25655.tc_term);
             type_of = (uu___1824_25655.type_of);
             universe_of = (uu___1824_25655.universe_of);
             check_type_of = (uu___1824_25655.check_type_of);
             use_bv_sorts = (uu___1824_25655.use_bv_sorts);
             qtbl_name_and_index = (uu___1824_25655.qtbl_name_and_index);
             normalized_eff_names = (uu___1824_25655.normalized_eff_names);
             fv_delta_depths = (uu___1824_25655.fv_delta_depths);
             proof_ns = (uu___1824_25655.proof_ns);
             synth_hook = (uu___1824_25655.synth_hook);
             try_solve_implicits_hook =
               (uu___1824_25655.try_solve_implicits_hook);
             splice = (uu___1824_25655.splice);
             mpreprocess = (uu___1824_25655.mpreprocess);
             postprocess = (uu___1824_25655.postprocess);
             is_native_tactic = (uu___1824_25655.is_native_tactic);
             identifier_info = (uu___1824_25655.identifier_info);
             tc_hooks = (uu___1824_25655.tc_hooks);
             dsenv = (uu___1824_25655.dsenv);
             nbe = (uu___1824_25655.nbe);
             strict_args_tab = (uu___1824_25655.strict_args_tab);
             erasable_types_tab = (uu___1824_25655.erasable_types_tab)
           })
  
let (add_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Ident.lident -> polymonadic_bind_t -> env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            let err_msg poly =
              let uu____25703 = FStar_Ident.string_of_lid m  in
              let uu____25705 = FStar_Ident.string_of_lid n1  in
              let uu____25707 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25703 uu____25705 uu____25707
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25716 =
              let uu____25718 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25718 FStar_Util.is_some  in
            if uu____25716
            then
              let uu____25755 =
                let uu____25761 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25761)
                 in
              FStar_Errors.raise_error uu____25755 env.range
            else
              (let uu____25767 =
                 let uu____25769 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25769 FStar_Util.is_some  in
               if uu____25767
               then
                 let uu____25794 =
                   let uu____25800 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25800)
                    in
                 FStar_Errors.raise_error uu____25794 env.range
               else
                 (let uu___1839_25806 = env  in
                  {
                    solver = (uu___1839_25806.solver);
                    range = (uu___1839_25806.range);
                    curmodule = (uu___1839_25806.curmodule);
                    gamma = (uu___1839_25806.gamma);
                    gamma_sig = (uu___1839_25806.gamma_sig);
                    gamma_cache = (uu___1839_25806.gamma_cache);
                    modules = (uu___1839_25806.modules);
                    expected_typ = (uu___1839_25806.expected_typ);
                    sigtab = (uu___1839_25806.sigtab);
                    attrtab = (uu___1839_25806.attrtab);
                    instantiate_imp = (uu___1839_25806.instantiate_imp);
                    effects =
                      (let uu___1841_25808 = env.effects  in
                       {
                         decls = (uu___1841_25808.decls);
                         order = (uu___1841_25808.order);
                         joins = (uu___1841_25808.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1839_25806.generalize);
                    letrecs = (uu___1839_25806.letrecs);
                    top_level = (uu___1839_25806.top_level);
                    check_uvars = (uu___1839_25806.check_uvars);
                    use_eq = (uu___1839_25806.use_eq);
                    use_eq_strict = (uu___1839_25806.use_eq_strict);
                    is_iface = (uu___1839_25806.is_iface);
                    admit = (uu___1839_25806.admit);
                    lax = (uu___1839_25806.lax);
                    lax_universes = (uu___1839_25806.lax_universes);
                    phase1 = (uu___1839_25806.phase1);
                    failhard = (uu___1839_25806.failhard);
                    nosynth = (uu___1839_25806.nosynth);
                    uvar_subtyping = (uu___1839_25806.uvar_subtyping);
                    tc_term = (uu___1839_25806.tc_term);
                    type_of = (uu___1839_25806.type_of);
                    universe_of = (uu___1839_25806.universe_of);
                    check_type_of = (uu___1839_25806.check_type_of);
                    use_bv_sorts = (uu___1839_25806.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1839_25806.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1839_25806.normalized_eff_names);
                    fv_delta_depths = (uu___1839_25806.fv_delta_depths);
                    proof_ns = (uu___1839_25806.proof_ns);
                    synth_hook = (uu___1839_25806.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1839_25806.try_solve_implicits_hook);
                    splice = (uu___1839_25806.splice);
                    mpreprocess = (uu___1839_25806.mpreprocess);
                    postprocess = (uu___1839_25806.postprocess);
                    is_native_tactic = (uu___1839_25806.is_native_tactic);
                    identifier_info = (uu___1839_25806.identifier_info);
                    tc_hooks = (uu___1839_25806.tc_hooks);
                    dsenv = (uu___1839_25806.dsenv);
                    nbe = (uu___1839_25806.nbe);
                    strict_args_tab = (uu___1839_25806.strict_args_tab);
                    erasable_types_tab = (uu___1839_25806.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1845_25880 = env  in
      {
        solver = (uu___1845_25880.solver);
        range = (uu___1845_25880.range);
        curmodule = (uu___1845_25880.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1845_25880.gamma_sig);
        gamma_cache = (uu___1845_25880.gamma_cache);
        modules = (uu___1845_25880.modules);
        expected_typ = (uu___1845_25880.expected_typ);
        sigtab = (uu___1845_25880.sigtab);
        attrtab = (uu___1845_25880.attrtab);
        instantiate_imp = (uu___1845_25880.instantiate_imp);
        effects = (uu___1845_25880.effects);
        generalize = (uu___1845_25880.generalize);
        letrecs = (uu___1845_25880.letrecs);
        top_level = (uu___1845_25880.top_level);
        check_uvars = (uu___1845_25880.check_uvars);
        use_eq = (uu___1845_25880.use_eq);
        use_eq_strict = (uu___1845_25880.use_eq_strict);
        is_iface = (uu___1845_25880.is_iface);
        admit = (uu___1845_25880.admit);
        lax = (uu___1845_25880.lax);
        lax_universes = (uu___1845_25880.lax_universes);
        phase1 = (uu___1845_25880.phase1);
        failhard = (uu___1845_25880.failhard);
        nosynth = (uu___1845_25880.nosynth);
        uvar_subtyping = (uu___1845_25880.uvar_subtyping);
        tc_term = (uu___1845_25880.tc_term);
        type_of = (uu___1845_25880.type_of);
        universe_of = (uu___1845_25880.universe_of);
        check_type_of = (uu___1845_25880.check_type_of);
        use_bv_sorts = (uu___1845_25880.use_bv_sorts);
        qtbl_name_and_index = (uu___1845_25880.qtbl_name_and_index);
        normalized_eff_names = (uu___1845_25880.normalized_eff_names);
        fv_delta_depths = (uu___1845_25880.fv_delta_depths);
        proof_ns = (uu___1845_25880.proof_ns);
        synth_hook = (uu___1845_25880.synth_hook);
        try_solve_implicits_hook = (uu___1845_25880.try_solve_implicits_hook);
        splice = (uu___1845_25880.splice);
        mpreprocess = (uu___1845_25880.mpreprocess);
        postprocess = (uu___1845_25880.postprocess);
        is_native_tactic = (uu___1845_25880.is_native_tactic);
        identifier_info = (uu___1845_25880.identifier_info);
        tc_hooks = (uu___1845_25880.tc_hooks);
        dsenv = (uu___1845_25880.dsenv);
        nbe = (uu___1845_25880.nbe);
        strict_args_tab = (uu___1845_25880.strict_args_tab);
        erasable_types_tab = (uu___1845_25880.erasable_types_tab)
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
            (let uu___1858_25938 = env  in
             {
               solver = (uu___1858_25938.solver);
               range = (uu___1858_25938.range);
               curmodule = (uu___1858_25938.curmodule);
               gamma = rest;
               gamma_sig = (uu___1858_25938.gamma_sig);
               gamma_cache = (uu___1858_25938.gamma_cache);
               modules = (uu___1858_25938.modules);
               expected_typ = (uu___1858_25938.expected_typ);
               sigtab = (uu___1858_25938.sigtab);
               attrtab = (uu___1858_25938.attrtab);
               instantiate_imp = (uu___1858_25938.instantiate_imp);
               effects = (uu___1858_25938.effects);
               generalize = (uu___1858_25938.generalize);
               letrecs = (uu___1858_25938.letrecs);
               top_level = (uu___1858_25938.top_level);
               check_uvars = (uu___1858_25938.check_uvars);
               use_eq = (uu___1858_25938.use_eq);
               use_eq_strict = (uu___1858_25938.use_eq_strict);
               is_iface = (uu___1858_25938.is_iface);
               admit = (uu___1858_25938.admit);
               lax = (uu___1858_25938.lax);
               lax_universes = (uu___1858_25938.lax_universes);
               phase1 = (uu___1858_25938.phase1);
               failhard = (uu___1858_25938.failhard);
               nosynth = (uu___1858_25938.nosynth);
               uvar_subtyping = (uu___1858_25938.uvar_subtyping);
               tc_term = (uu___1858_25938.tc_term);
               type_of = (uu___1858_25938.type_of);
               universe_of = (uu___1858_25938.universe_of);
               check_type_of = (uu___1858_25938.check_type_of);
               use_bv_sorts = (uu___1858_25938.use_bv_sorts);
               qtbl_name_and_index = (uu___1858_25938.qtbl_name_and_index);
               normalized_eff_names = (uu___1858_25938.normalized_eff_names);
               fv_delta_depths = (uu___1858_25938.fv_delta_depths);
               proof_ns = (uu___1858_25938.proof_ns);
               synth_hook = (uu___1858_25938.synth_hook);
               try_solve_implicits_hook =
                 (uu___1858_25938.try_solve_implicits_hook);
               splice = (uu___1858_25938.splice);
               mpreprocess = (uu___1858_25938.mpreprocess);
               postprocess = (uu___1858_25938.postprocess);
               is_native_tactic = (uu___1858_25938.is_native_tactic);
               identifier_info = (uu___1858_25938.identifier_info);
               tc_hooks = (uu___1858_25938.tc_hooks);
               dsenv = (uu___1858_25938.dsenv);
               nbe = (uu___1858_25938.nbe);
               strict_args_tab = (uu___1858_25938.strict_args_tab);
               erasable_types_tab = (uu___1858_25938.erasable_types_tab)
             }))
    | uu____25939 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25968  ->
             match uu____25968 with | (x,uu____25976) -> push_bv env1 x) env
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
            let uu___1872_26011 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1872_26011.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1872_26011.FStar_Syntax_Syntax.index);
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
        let uu____26084 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26084 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26112 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26112)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1893_26128 = env  in
      {
        solver = (uu___1893_26128.solver);
        range = (uu___1893_26128.range);
        curmodule = (uu___1893_26128.curmodule);
        gamma = (uu___1893_26128.gamma);
        gamma_sig = (uu___1893_26128.gamma_sig);
        gamma_cache = (uu___1893_26128.gamma_cache);
        modules = (uu___1893_26128.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1893_26128.sigtab);
        attrtab = (uu___1893_26128.attrtab);
        instantiate_imp = (uu___1893_26128.instantiate_imp);
        effects = (uu___1893_26128.effects);
        generalize = (uu___1893_26128.generalize);
        letrecs = (uu___1893_26128.letrecs);
        top_level = (uu___1893_26128.top_level);
        check_uvars = (uu___1893_26128.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1893_26128.use_eq_strict);
        is_iface = (uu___1893_26128.is_iface);
        admit = (uu___1893_26128.admit);
        lax = (uu___1893_26128.lax);
        lax_universes = (uu___1893_26128.lax_universes);
        phase1 = (uu___1893_26128.phase1);
        failhard = (uu___1893_26128.failhard);
        nosynth = (uu___1893_26128.nosynth);
        uvar_subtyping = (uu___1893_26128.uvar_subtyping);
        tc_term = (uu___1893_26128.tc_term);
        type_of = (uu___1893_26128.type_of);
        universe_of = (uu___1893_26128.universe_of);
        check_type_of = (uu___1893_26128.check_type_of);
        use_bv_sorts = (uu___1893_26128.use_bv_sorts);
        qtbl_name_and_index = (uu___1893_26128.qtbl_name_and_index);
        normalized_eff_names = (uu___1893_26128.normalized_eff_names);
        fv_delta_depths = (uu___1893_26128.fv_delta_depths);
        proof_ns = (uu___1893_26128.proof_ns);
        synth_hook = (uu___1893_26128.synth_hook);
        try_solve_implicits_hook = (uu___1893_26128.try_solve_implicits_hook);
        splice = (uu___1893_26128.splice);
        mpreprocess = (uu___1893_26128.mpreprocess);
        postprocess = (uu___1893_26128.postprocess);
        is_native_tactic = (uu___1893_26128.is_native_tactic);
        identifier_info = (uu___1893_26128.identifier_info);
        tc_hooks = (uu___1893_26128.tc_hooks);
        dsenv = (uu___1893_26128.dsenv);
        nbe = (uu___1893_26128.nbe);
        strict_args_tab = (uu___1893_26128.strict_args_tab);
        erasable_types_tab = (uu___1893_26128.erasable_types_tab)
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
    let uu____26159 = expected_typ env_  in
    ((let uu___1900_26165 = env_  in
      {
        solver = (uu___1900_26165.solver);
        range = (uu___1900_26165.range);
        curmodule = (uu___1900_26165.curmodule);
        gamma = (uu___1900_26165.gamma);
        gamma_sig = (uu___1900_26165.gamma_sig);
        gamma_cache = (uu___1900_26165.gamma_cache);
        modules = (uu___1900_26165.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1900_26165.sigtab);
        attrtab = (uu___1900_26165.attrtab);
        instantiate_imp = (uu___1900_26165.instantiate_imp);
        effects = (uu___1900_26165.effects);
        generalize = (uu___1900_26165.generalize);
        letrecs = (uu___1900_26165.letrecs);
        top_level = (uu___1900_26165.top_level);
        check_uvars = (uu___1900_26165.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1900_26165.use_eq_strict);
        is_iface = (uu___1900_26165.is_iface);
        admit = (uu___1900_26165.admit);
        lax = (uu___1900_26165.lax);
        lax_universes = (uu___1900_26165.lax_universes);
        phase1 = (uu___1900_26165.phase1);
        failhard = (uu___1900_26165.failhard);
        nosynth = (uu___1900_26165.nosynth);
        uvar_subtyping = (uu___1900_26165.uvar_subtyping);
        tc_term = (uu___1900_26165.tc_term);
        type_of = (uu___1900_26165.type_of);
        universe_of = (uu___1900_26165.universe_of);
        check_type_of = (uu___1900_26165.check_type_of);
        use_bv_sorts = (uu___1900_26165.use_bv_sorts);
        qtbl_name_and_index = (uu___1900_26165.qtbl_name_and_index);
        normalized_eff_names = (uu___1900_26165.normalized_eff_names);
        fv_delta_depths = (uu___1900_26165.fv_delta_depths);
        proof_ns = (uu___1900_26165.proof_ns);
        synth_hook = (uu___1900_26165.synth_hook);
        try_solve_implicits_hook = (uu___1900_26165.try_solve_implicits_hook);
        splice = (uu___1900_26165.splice);
        mpreprocess = (uu___1900_26165.mpreprocess);
        postprocess = (uu___1900_26165.postprocess);
        is_native_tactic = (uu___1900_26165.is_native_tactic);
        identifier_info = (uu___1900_26165.identifier_info);
        tc_hooks = (uu___1900_26165.tc_hooks);
        dsenv = (uu___1900_26165.dsenv);
        nbe = (uu___1900_26165.nbe);
        strict_args_tab = (uu___1900_26165.strict_args_tab);
        erasable_types_tab = (uu___1900_26165.erasable_types_tab)
      }), uu____26159)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26177 =
      let uu____26180 = FStar_Ident.id_of_text ""  in [uu____26180]  in
    FStar_Ident.lid_of_ids uu____26177  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26187 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26187
        then
          let uu____26192 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26192 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1908_26220 = env  in
       {
         solver = (uu___1908_26220.solver);
         range = (uu___1908_26220.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1908_26220.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1908_26220.expected_typ);
         sigtab = (uu___1908_26220.sigtab);
         attrtab = (uu___1908_26220.attrtab);
         instantiate_imp = (uu___1908_26220.instantiate_imp);
         effects = (uu___1908_26220.effects);
         generalize = (uu___1908_26220.generalize);
         letrecs = (uu___1908_26220.letrecs);
         top_level = (uu___1908_26220.top_level);
         check_uvars = (uu___1908_26220.check_uvars);
         use_eq = (uu___1908_26220.use_eq);
         use_eq_strict = (uu___1908_26220.use_eq_strict);
         is_iface = (uu___1908_26220.is_iface);
         admit = (uu___1908_26220.admit);
         lax = (uu___1908_26220.lax);
         lax_universes = (uu___1908_26220.lax_universes);
         phase1 = (uu___1908_26220.phase1);
         failhard = (uu___1908_26220.failhard);
         nosynth = (uu___1908_26220.nosynth);
         uvar_subtyping = (uu___1908_26220.uvar_subtyping);
         tc_term = (uu___1908_26220.tc_term);
         type_of = (uu___1908_26220.type_of);
         universe_of = (uu___1908_26220.universe_of);
         check_type_of = (uu___1908_26220.check_type_of);
         use_bv_sorts = (uu___1908_26220.use_bv_sorts);
         qtbl_name_and_index = (uu___1908_26220.qtbl_name_and_index);
         normalized_eff_names = (uu___1908_26220.normalized_eff_names);
         fv_delta_depths = (uu___1908_26220.fv_delta_depths);
         proof_ns = (uu___1908_26220.proof_ns);
         synth_hook = (uu___1908_26220.synth_hook);
         try_solve_implicits_hook =
           (uu___1908_26220.try_solve_implicits_hook);
         splice = (uu___1908_26220.splice);
         mpreprocess = (uu___1908_26220.mpreprocess);
         postprocess = (uu___1908_26220.postprocess);
         is_native_tactic = (uu___1908_26220.is_native_tactic);
         identifier_info = (uu___1908_26220.identifier_info);
         tc_hooks = (uu___1908_26220.tc_hooks);
         dsenv = (uu___1908_26220.dsenv);
         nbe = (uu___1908_26220.nbe);
         strict_args_tab = (uu___1908_26220.strict_args_tab);
         erasable_types_tab = (uu___1908_26220.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26272)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26276,(uu____26277,t)))::tl1
          ->
          let uu____26298 =
            let uu____26301 = FStar_Syntax_Free.uvars t  in
            ext out uu____26301  in
          aux uu____26298 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26304;
            FStar_Syntax_Syntax.index = uu____26305;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26313 =
            let uu____26316 = FStar_Syntax_Free.uvars t  in
            ext out uu____26316  in
          aux uu____26313 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26374)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26378,(uu____26379,t)))::tl1
          ->
          let uu____26400 =
            let uu____26403 = FStar_Syntax_Free.univs t  in
            ext out uu____26403  in
          aux uu____26400 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26406;
            FStar_Syntax_Syntax.index = uu____26407;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26415 =
            let uu____26418 = FStar_Syntax_Free.univs t  in
            ext out uu____26418  in
          aux uu____26415 tl1
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
          let uu____26480 = FStar_Util.set_add uname out  in
          aux uu____26480 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26483,(uu____26484,t)))::tl1
          ->
          let uu____26505 =
            let uu____26508 = FStar_Syntax_Free.univnames t  in
            ext out uu____26508  in
          aux uu____26505 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26511;
            FStar_Syntax_Syntax.index = uu____26512;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26520 =
            let uu____26523 = FStar_Syntax_Free.univnames t  in
            ext out uu____26523  in
          aux uu____26520 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26544  ->
            match uu___12_26544 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26548 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26561 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26572 =
      let uu____26581 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26581
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26572 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26629 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26642  ->
              match uu___13_26642 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26645 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26645
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26651) ->
                  let uu____26668 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26668))
       in
    FStar_All.pipe_right uu____26629 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26682  ->
    match uu___14_26682 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26688 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26688
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26712  ->
         fun v1  ->
           fun keys1  ->
             let uu____26718 = FStar_Syntax_Util.lids_of_sigelt v1  in
             FStar_List.append uu____26718 keys1) keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26770) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26803,uu____26804) -> false  in
      let uu____26818 =
        FStar_List.tryFind
          (fun uu____26840  ->
             match uu____26840 with | (p,uu____26851) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26818 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26870,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26900 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26900
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2051_26922 = e  in
        {
          solver = (uu___2051_26922.solver);
          range = (uu___2051_26922.range);
          curmodule = (uu___2051_26922.curmodule);
          gamma = (uu___2051_26922.gamma);
          gamma_sig = (uu___2051_26922.gamma_sig);
          gamma_cache = (uu___2051_26922.gamma_cache);
          modules = (uu___2051_26922.modules);
          expected_typ = (uu___2051_26922.expected_typ);
          sigtab = (uu___2051_26922.sigtab);
          attrtab = (uu___2051_26922.attrtab);
          instantiate_imp = (uu___2051_26922.instantiate_imp);
          effects = (uu___2051_26922.effects);
          generalize = (uu___2051_26922.generalize);
          letrecs = (uu___2051_26922.letrecs);
          top_level = (uu___2051_26922.top_level);
          check_uvars = (uu___2051_26922.check_uvars);
          use_eq = (uu___2051_26922.use_eq);
          use_eq_strict = (uu___2051_26922.use_eq_strict);
          is_iface = (uu___2051_26922.is_iface);
          admit = (uu___2051_26922.admit);
          lax = (uu___2051_26922.lax);
          lax_universes = (uu___2051_26922.lax_universes);
          phase1 = (uu___2051_26922.phase1);
          failhard = (uu___2051_26922.failhard);
          nosynth = (uu___2051_26922.nosynth);
          uvar_subtyping = (uu___2051_26922.uvar_subtyping);
          tc_term = (uu___2051_26922.tc_term);
          type_of = (uu___2051_26922.type_of);
          universe_of = (uu___2051_26922.universe_of);
          check_type_of = (uu___2051_26922.check_type_of);
          use_bv_sorts = (uu___2051_26922.use_bv_sorts);
          qtbl_name_and_index = (uu___2051_26922.qtbl_name_and_index);
          normalized_eff_names = (uu___2051_26922.normalized_eff_names);
          fv_delta_depths = (uu___2051_26922.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2051_26922.synth_hook);
          try_solve_implicits_hook =
            (uu___2051_26922.try_solve_implicits_hook);
          splice = (uu___2051_26922.splice);
          mpreprocess = (uu___2051_26922.mpreprocess);
          postprocess = (uu___2051_26922.postprocess);
          is_native_tactic = (uu___2051_26922.is_native_tactic);
          identifier_info = (uu___2051_26922.identifier_info);
          tc_hooks = (uu___2051_26922.tc_hooks);
          dsenv = (uu___2051_26922.dsenv);
          nbe = (uu___2051_26922.nbe);
          strict_args_tab = (uu___2051_26922.strict_args_tab);
          erasable_types_tab = (uu___2051_26922.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2060_26970 = e  in
      {
        solver = (uu___2060_26970.solver);
        range = (uu___2060_26970.range);
        curmodule = (uu___2060_26970.curmodule);
        gamma = (uu___2060_26970.gamma);
        gamma_sig = (uu___2060_26970.gamma_sig);
        gamma_cache = (uu___2060_26970.gamma_cache);
        modules = (uu___2060_26970.modules);
        expected_typ = (uu___2060_26970.expected_typ);
        sigtab = (uu___2060_26970.sigtab);
        attrtab = (uu___2060_26970.attrtab);
        instantiate_imp = (uu___2060_26970.instantiate_imp);
        effects = (uu___2060_26970.effects);
        generalize = (uu___2060_26970.generalize);
        letrecs = (uu___2060_26970.letrecs);
        top_level = (uu___2060_26970.top_level);
        check_uvars = (uu___2060_26970.check_uvars);
        use_eq = (uu___2060_26970.use_eq);
        use_eq_strict = (uu___2060_26970.use_eq_strict);
        is_iface = (uu___2060_26970.is_iface);
        admit = (uu___2060_26970.admit);
        lax = (uu___2060_26970.lax);
        lax_universes = (uu___2060_26970.lax_universes);
        phase1 = (uu___2060_26970.phase1);
        failhard = (uu___2060_26970.failhard);
        nosynth = (uu___2060_26970.nosynth);
        uvar_subtyping = (uu___2060_26970.uvar_subtyping);
        tc_term = (uu___2060_26970.tc_term);
        type_of = (uu___2060_26970.type_of);
        universe_of = (uu___2060_26970.universe_of);
        check_type_of = (uu___2060_26970.check_type_of);
        use_bv_sorts = (uu___2060_26970.use_bv_sorts);
        qtbl_name_and_index = (uu___2060_26970.qtbl_name_and_index);
        normalized_eff_names = (uu___2060_26970.normalized_eff_names);
        fv_delta_depths = (uu___2060_26970.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2060_26970.synth_hook);
        try_solve_implicits_hook = (uu___2060_26970.try_solve_implicits_hook);
        splice = (uu___2060_26970.splice);
        mpreprocess = (uu___2060_26970.mpreprocess);
        postprocess = (uu___2060_26970.postprocess);
        is_native_tactic = (uu___2060_26970.is_native_tactic);
        identifier_info = (uu___2060_26970.identifier_info);
        tc_hooks = (uu___2060_26970.tc_hooks);
        dsenv = (uu___2060_26970.dsenv);
        nbe = (uu___2060_26970.nbe);
        strict_args_tab = (uu___2060_26970.strict_args_tab);
        erasable_types_tab = (uu___2060_26970.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26986 = FStar_Syntax_Free.names t  in
      let uu____26989 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26986 uu____26989
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27012 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27012
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27022 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27022
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27043 =
      match uu____27043 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27063 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27063)
       in
    let uu____27071 =
      let uu____27075 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27075 FStar_List.rev  in
    FStar_All.pipe_right uu____27071 (FStar_String.concat " ")
  
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
                  (let uu____27143 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27143 with
                   | FStar_Pervasives_Native.Some uu____27147 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27150 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27160;
        FStar_TypeChecker_Common.univ_ineqs = uu____27161;
        FStar_TypeChecker_Common.implicits = uu____27162;_} -> true
    | uu____27172 -> false
  
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
          let uu___2104_27194 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2104_27194.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2104_27194.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2104_27194.FStar_TypeChecker_Common.implicits)
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
          let uu____27233 = FStar_Options.defensive ()  in
          if uu____27233
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27239 =
              let uu____27241 =
                let uu____27243 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27243  in
              Prims.op_Negation uu____27241  in
            (if uu____27239
             then
               let uu____27250 =
                 let uu____27256 =
                   let uu____27258 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27260 =
                     let uu____27262 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27262
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27258 uu____27260
                    in
                 (FStar_Errors.Warning_Defensive, uu____27256)  in
               FStar_Errors.log_issue rng uu____27250
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
          let uu____27302 =
            let uu____27304 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27304  in
          if uu____27302
          then ()
          else
            (let uu____27309 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27309 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27335 =
            let uu____27337 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27337  in
          if uu____27335
          then ()
          else
            (let uu____27342 = bound_vars e  in
             def_check_closed_in rng msg uu____27342 t)
  
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
          let uu___2141_27381 = g  in
          let uu____27382 =
            let uu____27383 =
              let uu____27384 =
                let uu____27391 =
                  let uu____27392 =
                    let uu____27409 =
                      let uu____27420 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27420]  in
                    (f, uu____27409)  in
                  FStar_Syntax_Syntax.Tm_app uu____27392  in
                FStar_Syntax_Syntax.mk uu____27391  in
              uu____27384 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27457  -> FStar_TypeChecker_Common.NonTrivial _27457)
              uu____27383
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27382;
            FStar_TypeChecker_Common.deferred =
              (uu___2141_27381.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2141_27381.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2141_27381.FStar_TypeChecker_Common.implicits)
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
          let uu___2148_27475 = g  in
          let uu____27476 =
            let uu____27477 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27477  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27476;
            FStar_TypeChecker_Common.deferred =
              (uu___2148_27475.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2148_27475.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2148_27475.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2153_27494 = g  in
          let uu____27495 =
            let uu____27496 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27496  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27495;
            FStar_TypeChecker_Common.deferred =
              (uu___2153_27494.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2153_27494.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2153_27494.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2157_27498 = g  in
          let uu____27499 =
            let uu____27500 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27500  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27499;
            FStar_TypeChecker_Common.deferred =
              (uu___2157_27498.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2157_27498.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2157_27498.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27507 ->
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
                       let uu____27584 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27584
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2180_27591 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2180_27591.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2180_27591.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2180_27591.FStar_TypeChecker_Common.implicits)
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
               let uu____27625 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27625
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
            let uu___2195_27652 = g  in
            let uu____27653 =
              let uu____27654 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27654  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27653;
              FStar_TypeChecker_Common.deferred =
                (uu___2195_27652.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2195_27652.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2195_27652.FStar_TypeChecker_Common.implicits)
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
              let uu____27712 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27712 with
              | FStar_Pervasives_Native.Some
                  (uu____27737::(tm,uu____27739)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27803 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27821 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27821;
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
                    (let uu____27853 =
                       debug env (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27853
                     then
                       let uu____27857 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27857
                     else ());
                    (let g =
                       let uu___2219_27863 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2219_27863.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2219_27863.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2219_27863.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits = [imp]
                       }  in
                     (t, [(ctx_uvar, r)], g))))
  
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
            let uu____27917 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27974  ->
                      fun b  ->
                        match uu____27974 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____28016 =
                              let uu____28029 = reason b  in
                              new_implicit_var_aux uu____28029 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____28016 with
                             | (t,uu____28046,g_t) ->
                                 let uu____28060 =
                                   let uu____28063 =
                                     let uu____28066 =
                                       let uu____28067 =
                                         let uu____28074 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28074, t)  in
                                       FStar_Syntax_Syntax.NT uu____28067  in
                                     [uu____28066]  in
                                   FStar_List.append substs1 uu____28063  in
                                 let uu____28085 = conj_guard g g_t  in
                                 (uu____28060,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28085))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27917
              (fun uu____28114  ->
                 match uu____28114 with
                 | (uu____28131,uvars1,g) -> (uvars1, g))
  
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        fun wp  ->
          fun r  ->
            let trivial_post =
              let post_ts =
                let uu____28172 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28172 FStar_Util.must  in
              let uu____28189 = inst_tscheme_with post_ts [u]  in
              match uu____28189 with
              | (uu____28194,post) ->
                  let uu____28196 =
                    let uu____28201 =
                      let uu____28202 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28202]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28201  in
                  uu____28196 FStar_Pervasives_Native.None r
               in
            let uu____28235 =
              let uu____28240 =
                let uu____28241 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28241]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28240  in
            uu____28235 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28277  -> ());
    push = (fun uu____28279  -> ());
    pop = (fun uu____28282  -> ());
    snapshot =
      (fun uu____28285  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28304  -> fun uu____28305  -> ());
    encode_sig = (fun uu____28320  -> fun uu____28321  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28327 =
             let uu____28334 = FStar_Options.peek ()  in (e, g, uu____28334)
              in
           [uu____28327]);
    solve = (fun uu____28350  -> fun uu____28351  -> fun uu____28352  -> ());
    finish = (fun uu____28359  -> ());
    refresh = (fun uu____28361  -> ())
  } 