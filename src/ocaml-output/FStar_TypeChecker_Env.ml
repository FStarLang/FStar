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
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
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
                                  uu____17679 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17686 -> cache t  in
                            let uu____17687 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17687 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17693 =
                                   let uu____17694 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17694)
                                    in
                                 maybe_cache uu____17693)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17765 = find_in_sigtab env lid  in
         match uu____17765 with
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
      let uu____17846 = lookup_qname env lid  in
      match uu____17846 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17867,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17981 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17981 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18026 =
          let uu____18029 = lookup_attr env1 attr  in se1 :: uu____18029  in
        FStar_Util.smap_add (attrtab env1) attr uu____18026  in
      FStar_List.iter
        (fun attr  ->
           let uu____18039 =
             let uu____18040 = FStar_Syntax_Subst.compress attr  in
             uu____18040.FStar_Syntax_Syntax.n  in
           match uu____18039 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18044 =
                 let uu____18046 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18046.FStar_Ident.str  in
               add_one1 env se uu____18044
           | uu____18047 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18070) ->
          add_sigelts env ses
      | uu____18079 ->
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
        (fun uu___4_18117  ->
           match uu___4_18117 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18135 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18197,lb::[]),uu____18199) ->
            let uu____18208 =
              let uu____18217 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18226 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18217, uu____18226)  in
            FStar_Pervasives_Native.Some uu____18208
        | FStar_Syntax_Syntax.Sig_let ((uu____18239,lbs),uu____18241) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18273 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18286 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18286
                     then
                       let uu____18299 =
                         let uu____18308 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18317 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18308, uu____18317)  in
                       FStar_Pervasives_Native.Some uu____18299
                     else FStar_Pervasives_Native.None)
        | uu____18340 -> FStar_Pervasives_Native.None
  
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
                    let uu____18432 =
                      let uu____18434 =
                        let uu____18436 =
                          let uu____18438 =
                            let uu____18440 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18446 =
                              let uu____18448 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18448  in
                            Prims.op_Hat uu____18440 uu____18446  in
                          Prims.op_Hat ", expected " uu____18438  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18436
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18434
                       in
                    failwith uu____18432
                  else ());
             (let uu____18455 =
                let uu____18464 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18464, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18455))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18484,uu____18485) ->
            let uu____18490 =
              let uu____18499 =
                let uu____18504 =
                  let uu____18505 =
                    let uu____18508 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18508  in
                  (us, uu____18505)  in
                inst_ts us_opt uu____18504  in
              (uu____18499, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18490
        | uu____18527 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18616 =
          match uu____18616 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18712,uvs,t,uu____18715,uu____18716,uu____18717);
                      FStar_Syntax_Syntax.sigrng = uu____18718;
                      FStar_Syntax_Syntax.sigquals = uu____18719;
                      FStar_Syntax_Syntax.sigmeta = uu____18720;
                      FStar_Syntax_Syntax.sigattrs = uu____18721;
                      FStar_Syntax_Syntax.sigopts = uu____18722;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18747 =
                     let uu____18756 = inst_tscheme1 (uvs, t)  in
                     (uu____18756, rng)  in
                   FStar_Pervasives_Native.Some uu____18747
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18780;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18782;
                      FStar_Syntax_Syntax.sigattrs = uu____18783;
                      FStar_Syntax_Syntax.sigopts = uu____18784;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18803 =
                     let uu____18805 = in_cur_mod env l  in uu____18805 = Yes
                      in
                   if uu____18803
                   then
                     let uu____18817 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18817
                      then
                        let uu____18833 =
                          let uu____18842 = inst_tscheme1 (uvs, t)  in
                          (uu____18842, rng)  in
                        FStar_Pervasives_Native.Some uu____18833
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18875 =
                        let uu____18884 = inst_tscheme1 (uvs, t)  in
                        (uu____18884, rng)  in
                      FStar_Pervasives_Native.Some uu____18875)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18909,uu____18910);
                      FStar_Syntax_Syntax.sigrng = uu____18911;
                      FStar_Syntax_Syntax.sigquals = uu____18912;
                      FStar_Syntax_Syntax.sigmeta = uu____18913;
                      FStar_Syntax_Syntax.sigattrs = uu____18914;
                      FStar_Syntax_Syntax.sigopts = uu____18915;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18958 =
                          let uu____18967 = inst_tscheme1 (uvs, k)  in
                          (uu____18967, rng)  in
                        FStar_Pervasives_Native.Some uu____18958
                    | uu____18988 ->
                        let uu____18989 =
                          let uu____18998 =
                            let uu____19003 =
                              let uu____19004 =
                                let uu____19007 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19007
                                 in
                              (uvs, uu____19004)  in
                            inst_tscheme1 uu____19003  in
                          (uu____18998, rng)  in
                        FStar_Pervasives_Native.Some uu____18989)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19030,uu____19031);
                      FStar_Syntax_Syntax.sigrng = uu____19032;
                      FStar_Syntax_Syntax.sigquals = uu____19033;
                      FStar_Syntax_Syntax.sigmeta = uu____19034;
                      FStar_Syntax_Syntax.sigattrs = uu____19035;
                      FStar_Syntax_Syntax.sigopts = uu____19036;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19080 =
                          let uu____19089 = inst_tscheme_with (uvs, k) us  in
                          (uu____19089, rng)  in
                        FStar_Pervasives_Native.Some uu____19080
                    | uu____19110 ->
                        let uu____19111 =
                          let uu____19120 =
                            let uu____19125 =
                              let uu____19126 =
                                let uu____19129 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19129
                                 in
                              (uvs, uu____19126)  in
                            inst_tscheme_with uu____19125 us  in
                          (uu____19120, rng)  in
                        FStar_Pervasives_Native.Some uu____19111)
               | FStar_Util.Inr se ->
                   let uu____19165 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19186;
                          FStar_Syntax_Syntax.sigrng = uu____19187;
                          FStar_Syntax_Syntax.sigquals = uu____19188;
                          FStar_Syntax_Syntax.sigmeta = uu____19189;
                          FStar_Syntax_Syntax.sigattrs = uu____19190;
                          FStar_Syntax_Syntax.sigopts = uu____19191;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19208 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19165
                     (FStar_Util.map_option
                        (fun uu____19256  ->
                           match uu____19256 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19287 =
          let uu____19298 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19298 mapper  in
        match uu____19287 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19372 =
              let uu____19383 =
                let uu____19390 =
                  let uu___855_19393 = t  in
                  let uu____19394 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_19393.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19394;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_19393.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19390)  in
              (uu____19383, r)  in
            FStar_Pervasives_Native.Some uu____19372
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19443 = lookup_qname env l  in
      match uu____19443 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19464 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19518 = try_lookup_bv env bv  in
      match uu____19518 with
      | FStar_Pervasives_Native.None  ->
          let uu____19533 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19533 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19549 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19550 =
            let uu____19551 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19551  in
          (uu____19549, uu____19550)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19573 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19573 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19639 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19639  in
          let uu____19640 =
            let uu____19649 =
              let uu____19654 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19654)  in
            (uu____19649, r1)  in
          FStar_Pervasives_Native.Some uu____19640
  
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
        let uu____19689 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19689 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19722,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19747 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19747  in
            let uu____19748 =
              let uu____19753 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19753, r1)  in
            FStar_Pervasives_Native.Some uu____19748
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19777 = try_lookup_lid env l  in
      match uu____19777 with
      | FStar_Pervasives_Native.None  ->
          let uu____19804 = name_not_found l  in
          let uu____19810 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19804 uu____19810
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19853  ->
              match uu___5_19853 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19857 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19878 = lookup_qname env lid  in
      match uu____19878 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19887,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19890;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19892;
              FStar_Syntax_Syntax.sigattrs = uu____19893;
              FStar_Syntax_Syntax.sigopts = uu____19894;_},FStar_Pervasives_Native.None
            ),uu____19895)
          ->
          let uu____19946 =
            let uu____19953 =
              let uu____19954 =
                let uu____19957 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19957 t  in
              (uvs, uu____19954)  in
            (uu____19953, q)  in
          FStar_Pervasives_Native.Some uu____19946
      | uu____19970 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19992 = lookup_qname env lid  in
      match uu____19992 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19997,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20000;
              FStar_Syntax_Syntax.sigquals = uu____20001;
              FStar_Syntax_Syntax.sigmeta = uu____20002;
              FStar_Syntax_Syntax.sigattrs = uu____20003;
              FStar_Syntax_Syntax.sigopts = uu____20004;_},FStar_Pervasives_Native.None
            ),uu____20005)
          ->
          let uu____20056 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20056 (uvs, t)
      | uu____20061 ->
          let uu____20062 = name_not_found lid  in
          let uu____20068 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20062 uu____20068
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20088 = lookup_qname env lid  in
      match uu____20088 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20093,uvs,t,uu____20096,uu____20097,uu____20098);
              FStar_Syntax_Syntax.sigrng = uu____20099;
              FStar_Syntax_Syntax.sigquals = uu____20100;
              FStar_Syntax_Syntax.sigmeta = uu____20101;
              FStar_Syntax_Syntax.sigattrs = uu____20102;
              FStar_Syntax_Syntax.sigopts = uu____20103;_},FStar_Pervasives_Native.None
            ),uu____20104)
          ->
          let uu____20161 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20161 (uvs, t)
      | uu____20166 ->
          let uu____20167 = name_not_found lid  in
          let uu____20173 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20167 uu____20173
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20196 = lookup_qname env lid  in
      match uu____20196 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20204,uu____20205,uu____20206,uu____20207,uu____20208,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20210;
              FStar_Syntax_Syntax.sigquals = uu____20211;
              FStar_Syntax_Syntax.sigmeta = uu____20212;
              FStar_Syntax_Syntax.sigattrs = uu____20213;
              FStar_Syntax_Syntax.sigopts = uu____20214;_},uu____20215),uu____20216)
          -> (true, dcs)
      | uu____20281 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20297 = lookup_qname env lid  in
      match uu____20297 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20298,uu____20299,uu____20300,l,uu____20302,uu____20303);
              FStar_Syntax_Syntax.sigrng = uu____20304;
              FStar_Syntax_Syntax.sigquals = uu____20305;
              FStar_Syntax_Syntax.sigmeta = uu____20306;
              FStar_Syntax_Syntax.sigattrs = uu____20307;
              FStar_Syntax_Syntax.sigopts = uu____20308;_},uu____20309),uu____20310)
          -> l
      | uu____20369 ->
          let uu____20370 =
            let uu____20372 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20372  in
          failwith uu____20370
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20442)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20499) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20523 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20523
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20558 -> FStar_Pervasives_Native.None)
          | uu____20567 -> FStar_Pervasives_Native.None
  
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
        let uu____20629 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20629
  
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
        let uu____20662 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20662
  
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
             (FStar_Util.Inl uu____20714,uu____20715) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20764),uu____20765) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20814 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20832 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20842 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20859 ->
                  let uu____20866 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20866
              | FStar_Syntax_Syntax.Sig_let ((uu____20867,lbs),uu____20869)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20885 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20885
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____20892 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____20900 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20901 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20908 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20909 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20910 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20923 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20924 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20952 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20952
           (fun d_opt  ->
              let uu____20965 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20965
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20975 =
                   let uu____20978 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20978  in
                 match uu____20975 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20979 =
                       let uu____20981 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20981
                        in
                     failwith uu____20979
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20986 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20986
                       then
                         let uu____20989 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20991 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20993 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20989 uu____20991 uu____20993
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
        (FStar_Util.Inr (se,uu____21018),uu____21019) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21068 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21090),uu____21091) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21140 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21162 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21162
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21195 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21195 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21217 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21226 =
                        let uu____21227 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21227.FStar_Syntax_Syntax.n  in
                      match uu____21226 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21232 -> false))
               in
            (true, uu____21217)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21255 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21255
  
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
          let uu____21327 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21327.FStar_Ident.str  in
        let uu____21328 = FStar_Util.smap_try_find tab s  in
        match uu____21328 with
        | FStar_Pervasives_Native.None  ->
            let uu____21331 = f ()  in
            (match uu____21331 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21369 =
        let uu____21370 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21370 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21404 =
        let uu____21405 = FStar_Syntax_Util.unrefine t  in
        uu____21405.FStar_Syntax_Syntax.n  in
      match uu____21404 with
      | FStar_Syntax_Syntax.Tm_type uu____21409 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21413) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21439) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21444,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21466 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21499 =
        let attrs =
          let uu____21505 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21505  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21545 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21545)
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
      let uu____21590 = lookup_qname env ftv  in
      match uu____21590 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21594) ->
          let uu____21639 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21639 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21660,t),r) ->
               let uu____21675 =
                 let uu____21676 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21676 t  in
               FStar_Pervasives_Native.Some uu____21675)
      | uu____21677 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21689 = try_lookup_effect_lid env ftv  in
      match uu____21689 with
      | FStar_Pervasives_Native.None  ->
          let uu____21692 = name_not_found ftv  in
          let uu____21698 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21692 uu____21698
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
        let uu____21722 = lookup_qname env lid0  in
        match uu____21722 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21733);
                FStar_Syntax_Syntax.sigrng = uu____21734;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21736;
                FStar_Syntax_Syntax.sigattrs = uu____21737;
                FStar_Syntax_Syntax.sigopts = uu____21738;_},FStar_Pervasives_Native.None
              ),uu____21739)
            ->
            let lid1 =
              let uu____21795 =
                let uu____21796 = FStar_Ident.range_of_lid lid  in
                let uu____21797 =
                  let uu____21798 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21798  in
                FStar_Range.set_use_range uu____21796 uu____21797  in
              FStar_Ident.set_lid_range lid uu____21795  in
            let uu____21799 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21805  ->
                      match uu___6_21805 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21808 -> false))
               in
            if uu____21799
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21827 =
                      let uu____21829 =
                        let uu____21831 = get_range env  in
                        FStar_Range.string_of_range uu____21831  in
                      let uu____21832 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21834 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21829 uu____21832 uu____21834
                       in
                    failwith uu____21827)
                  in
               match (binders, univs1) with
               | ([],uu____21855) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21881,uu____21882::uu____21883::uu____21884) ->
                   let uu____21905 =
                     let uu____21907 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21909 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21907 uu____21909
                      in
                   failwith uu____21905
               | uu____21920 ->
                   let uu____21935 =
                     let uu____21940 =
                       let uu____21941 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21941)  in
                     inst_tscheme_with uu____21940 insts  in
                   (match uu____21935 with
                    | (uu____21954,t) ->
                        let t1 =
                          let uu____21957 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21957 t  in
                        let uu____21958 =
                          let uu____21959 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21959.FStar_Syntax_Syntax.n  in
                        (match uu____21958 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21994 -> failwith "Impossible")))
        | uu____22002 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22026 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22026 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22039,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22046 = find1 l2  in
            (match uu____22046 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22053 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22053 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22057 = find1 l  in
            (match uu____22057 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22062 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22062
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22083 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22083 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22089) ->
            FStar_List.length bs
        | uu____22128 ->
            let uu____22129 =
              let uu____22135 =
                let uu____22137 = FStar_Ident.string_of_lid name  in
                let uu____22139 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22137 uu____22139
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22135)
               in
            FStar_Errors.raise_error uu____22129 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22158 = lookup_qname env l1  in
      match uu____22158 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22161;
              FStar_Syntax_Syntax.sigrng = uu____22162;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22164;
              FStar_Syntax_Syntax.sigattrs = uu____22165;
              FStar_Syntax_Syntax.sigopts = uu____22166;_},uu____22167),uu____22168)
          -> q
      | uu____22221 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22245 =
          let uu____22246 =
            let uu____22248 = FStar_Util.string_of_int i  in
            let uu____22250 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22248 uu____22250
             in
          failwith uu____22246  in
        let uu____22253 = lookup_datacon env lid  in
        match uu____22253 with
        | (uu____22258,t) ->
            let uu____22260 =
              let uu____22261 = FStar_Syntax_Subst.compress t  in
              uu____22261.FStar_Syntax_Syntax.n  in
            (match uu____22260 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22265) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____22309 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____22309
                      FStar_Pervasives_Native.fst)
             | uu____22320 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22334 = lookup_qname env l  in
      match uu____22334 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22336,uu____22337,uu____22338);
              FStar_Syntax_Syntax.sigrng = uu____22339;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22341;
              FStar_Syntax_Syntax.sigattrs = uu____22342;
              FStar_Syntax_Syntax.sigopts = uu____22343;_},uu____22344),uu____22345)
          ->
          FStar_Util.for_some
            (fun uu___7_22400  ->
               match uu___7_22400 with
               | FStar_Syntax_Syntax.Projector uu____22402 -> true
               | uu____22408 -> false) quals
      | uu____22410 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22424 = lookup_qname env lid  in
      match uu____22424 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22426,uu____22427,uu____22428,uu____22429,uu____22430,uu____22431);
              FStar_Syntax_Syntax.sigrng = uu____22432;
              FStar_Syntax_Syntax.sigquals = uu____22433;
              FStar_Syntax_Syntax.sigmeta = uu____22434;
              FStar_Syntax_Syntax.sigattrs = uu____22435;
              FStar_Syntax_Syntax.sigopts = uu____22436;_},uu____22437),uu____22438)
          -> true
      | uu____22498 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22512 = lookup_qname env lid  in
      match uu____22512 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22514,uu____22515,uu____22516,uu____22517,uu____22518,uu____22519);
              FStar_Syntax_Syntax.sigrng = uu____22520;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22522;
              FStar_Syntax_Syntax.sigattrs = uu____22523;
              FStar_Syntax_Syntax.sigopts = uu____22524;_},uu____22525),uu____22526)
          ->
          FStar_Util.for_some
            (fun uu___8_22589  ->
               match uu___8_22589 with
               | FStar_Syntax_Syntax.RecordType uu____22591 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22601 -> true
               | uu____22611 -> false) quals
      | uu____22613 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22623,uu____22624);
            FStar_Syntax_Syntax.sigrng = uu____22625;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22627;
            FStar_Syntax_Syntax.sigattrs = uu____22628;
            FStar_Syntax_Syntax.sigopts = uu____22629;_},uu____22630),uu____22631)
        ->
        FStar_Util.for_some
          (fun uu___9_22690  ->
             match uu___9_22690 with
             | FStar_Syntax_Syntax.Action uu____22692 -> true
             | uu____22694 -> false) quals
    | uu____22696 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22710 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22710
  
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
      let uu____22727 =
        let uu____22728 = FStar_Syntax_Util.un_uinst head1  in
        uu____22728.FStar_Syntax_Syntax.n  in
      match uu____22727 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22734 ->
               true
           | uu____22737 -> false)
      | uu____22739 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22753 = lookup_qname env l  in
      match uu____22753 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22756),uu____22757) ->
          FStar_Util.for_some
            (fun uu___10_22805  ->
               match uu___10_22805 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22808 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22810 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22886 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22904) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22922 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22930 ->
                 FStar_Pervasives_Native.Some true
             | uu____22949 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22952 =
        let uu____22956 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22956 mapper  in
      match uu____22952 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23016 = lookup_qname env lid  in
      match uu____23016 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23020,uu____23021,tps,uu____23023,uu____23024,uu____23025);
              FStar_Syntax_Syntax.sigrng = uu____23026;
              FStar_Syntax_Syntax.sigquals = uu____23027;
              FStar_Syntax_Syntax.sigmeta = uu____23028;
              FStar_Syntax_Syntax.sigattrs = uu____23029;
              FStar_Syntax_Syntax.sigopts = uu____23030;_},uu____23031),uu____23032)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23100 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23146  ->
              match uu____23146 with
              | (d,uu____23155) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23171 = effect_decl_opt env l  in
      match uu____23171 with
      | FStar_Pervasives_Native.None  ->
          let uu____23186 = name_not_found l  in
          let uu____23192 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23186 uu____23192
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23220 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23220 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23227  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23241  ->
            fun uu____23242  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23276 = FStar_Ident.lid_equals l1 l2  in
        if uu____23276
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23295 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23295
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23314 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23367  ->
                        match uu____23367 with
                        | (m1,m2,uu____23381,uu____23382,uu____23383) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23314 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23408,uu____23409,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23457 = join_opt env l1 l2  in
        match uu____23457 with
        | FStar_Pervasives_Native.None  ->
            let uu____23478 =
              let uu____23484 =
                let uu____23486 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23488 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23486 uu____23488
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23484)  in
            FStar_Errors.raise_error uu____23478 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23531 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23531
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
  'Auu____23551 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23551) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23580 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23606  ->
                match uu____23606 with
                | (d,uu____23613) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23580 with
      | FStar_Pervasives_Native.None  ->
          let uu____23624 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23624
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23639 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23639 with
           | (uu____23650,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23668)::(wp,uu____23670)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23726 -> failwith "Impossible"))
  
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
        | uu____23791 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23804 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23804 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23821 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23821 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23846 =
                     let uu____23852 =
                       let uu____23854 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23862 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23873 =
                         let uu____23875 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23875  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23854 uu____23862 uu____23873
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23852)
                      in
                   FStar_Errors.raise_error uu____23846
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23883 =
                     let uu____23894 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23894 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23931  ->
                        fun uu____23932  ->
                          match (uu____23931, uu____23932) with
                          | ((x,uu____23962),(t,uu____23964)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23883
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23995 =
                     let uu___1609_23996 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1609_23996.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1609_23996.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1609_23996.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1609_23996.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23995
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24008 .
    'Auu____24008 ->
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
            let uu____24049 =
              let uu____24056 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24056)  in
            match uu____24049 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24080 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24082 = FStar_Util.string_of_int given  in
                     let uu____24084 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24080 uu____24082 uu____24084
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24089 = effect_decl_opt env effect_name  in
          match uu____24089 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24111) ->
              let uu____24122 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24122 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24140 =
                       let uu____24143 = get_range env  in
                       let uu____24144 =
                         let uu____24151 =
                           let uu____24152 =
                             let uu____24169 =
                               let uu____24180 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24180 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24169)  in
                           FStar_Syntax_Syntax.Tm_app uu____24152  in
                         FStar_Syntax_Syntax.mk uu____24151  in
                       uu____24144 FStar_Pervasives_Native.None uu____24143
                        in
                     FStar_Pervasives_Native.Some uu____24140)))
  
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
           (fun uu___11_24280  ->
              match uu___11_24280 with
              | FStar_Syntax_Syntax.Reflectable uu____24282 -> true
              | uu____24284 -> false))
  
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
      | uu____24344 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24359 =
        let uu____24360 = FStar_Syntax_Subst.compress t  in
        uu____24360.FStar_Syntax_Syntax.n  in
      match uu____24359 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24364,c) ->
          is_reifiable_comp env c
      | uu____24386 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24406 =
           let uu____24408 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24408  in
         if uu____24406
         then
           let uu____24411 =
             let uu____24417 =
               let uu____24419 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24419
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24417)  in
           let uu____24423 = get_range env  in
           FStar_Errors.raise_error uu____24411 uu____24423
         else ());
        (let uu____24426 = effect_repr_aux true env c u_c  in
         match uu____24426 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1686_24462 = env  in
        {
          solver = (uu___1686_24462.solver);
          range = (uu___1686_24462.range);
          curmodule = (uu___1686_24462.curmodule);
          gamma = (uu___1686_24462.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1686_24462.gamma_cache);
          modules = (uu___1686_24462.modules);
          expected_typ = (uu___1686_24462.expected_typ);
          sigtab = (uu___1686_24462.sigtab);
          attrtab = (uu___1686_24462.attrtab);
          instantiate_imp = (uu___1686_24462.instantiate_imp);
          effects = (uu___1686_24462.effects);
          generalize = (uu___1686_24462.generalize);
          letrecs = (uu___1686_24462.letrecs);
          top_level = (uu___1686_24462.top_level);
          check_uvars = (uu___1686_24462.check_uvars);
          use_eq = (uu___1686_24462.use_eq);
          use_eq_strict = (uu___1686_24462.use_eq_strict);
          is_iface = (uu___1686_24462.is_iface);
          admit = (uu___1686_24462.admit);
          lax = (uu___1686_24462.lax);
          lax_universes = (uu___1686_24462.lax_universes);
          phase1 = (uu___1686_24462.phase1);
          failhard = (uu___1686_24462.failhard);
          nosynth = (uu___1686_24462.nosynth);
          uvar_subtyping = (uu___1686_24462.uvar_subtyping);
          tc_term = (uu___1686_24462.tc_term);
          type_of = (uu___1686_24462.type_of);
          universe_of = (uu___1686_24462.universe_of);
          check_type_of = (uu___1686_24462.check_type_of);
          use_bv_sorts = (uu___1686_24462.use_bv_sorts);
          qtbl_name_and_index = (uu___1686_24462.qtbl_name_and_index);
          normalized_eff_names = (uu___1686_24462.normalized_eff_names);
          fv_delta_depths = (uu___1686_24462.fv_delta_depths);
          proof_ns = (uu___1686_24462.proof_ns);
          synth_hook = (uu___1686_24462.synth_hook);
          try_solve_implicits_hook =
            (uu___1686_24462.try_solve_implicits_hook);
          splice = (uu___1686_24462.splice);
          mpreprocess = (uu___1686_24462.mpreprocess);
          postprocess = (uu___1686_24462.postprocess);
          is_native_tactic = (uu___1686_24462.is_native_tactic);
          identifier_info = (uu___1686_24462.identifier_info);
          tc_hooks = (uu___1686_24462.tc_hooks);
          dsenv = (uu___1686_24462.dsenv);
          nbe = (uu___1686_24462.nbe);
          strict_args_tab = (uu___1686_24462.strict_args_tab);
          erasable_types_tab = (uu___1686_24462.erasable_types_tab)
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
    fun uu____24481  ->
      match uu____24481 with
      | (ed,quals) ->
          let effects =
            let uu___1695_24495 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1695_24495.order);
              joins = (uu___1695_24495.joins);
              polymonadic_binds = (uu___1695_24495.polymonadic_binds)
            }  in
          let uu___1698_24504 = env  in
          {
            solver = (uu___1698_24504.solver);
            range = (uu___1698_24504.range);
            curmodule = (uu___1698_24504.curmodule);
            gamma = (uu___1698_24504.gamma);
            gamma_sig = (uu___1698_24504.gamma_sig);
            gamma_cache = (uu___1698_24504.gamma_cache);
            modules = (uu___1698_24504.modules);
            expected_typ = (uu___1698_24504.expected_typ);
            sigtab = (uu___1698_24504.sigtab);
            attrtab = (uu___1698_24504.attrtab);
            instantiate_imp = (uu___1698_24504.instantiate_imp);
            effects;
            generalize = (uu___1698_24504.generalize);
            letrecs = (uu___1698_24504.letrecs);
            top_level = (uu___1698_24504.top_level);
            check_uvars = (uu___1698_24504.check_uvars);
            use_eq = (uu___1698_24504.use_eq);
            use_eq_strict = (uu___1698_24504.use_eq_strict);
            is_iface = (uu___1698_24504.is_iface);
            admit = (uu___1698_24504.admit);
            lax = (uu___1698_24504.lax);
            lax_universes = (uu___1698_24504.lax_universes);
            phase1 = (uu___1698_24504.phase1);
            failhard = (uu___1698_24504.failhard);
            nosynth = (uu___1698_24504.nosynth);
            uvar_subtyping = (uu___1698_24504.uvar_subtyping);
            tc_term = (uu___1698_24504.tc_term);
            type_of = (uu___1698_24504.type_of);
            universe_of = (uu___1698_24504.universe_of);
            check_type_of = (uu___1698_24504.check_type_of);
            use_bv_sorts = (uu___1698_24504.use_bv_sorts);
            qtbl_name_and_index = (uu___1698_24504.qtbl_name_and_index);
            normalized_eff_names = (uu___1698_24504.normalized_eff_names);
            fv_delta_depths = (uu___1698_24504.fv_delta_depths);
            proof_ns = (uu___1698_24504.proof_ns);
            synth_hook = (uu___1698_24504.synth_hook);
            try_solve_implicits_hook =
              (uu___1698_24504.try_solve_implicits_hook);
            splice = (uu___1698_24504.splice);
            mpreprocess = (uu___1698_24504.mpreprocess);
            postprocess = (uu___1698_24504.postprocess);
            is_native_tactic = (uu___1698_24504.is_native_tactic);
            identifier_info = (uu___1698_24504.identifier_info);
            tc_hooks = (uu___1698_24504.tc_hooks);
            dsenv = (uu___1698_24504.dsenv);
            nbe = (uu___1698_24504.nbe);
            strict_args_tab = (uu___1698_24504.strict_args_tab);
            erasable_types_tab = (uu___1698_24504.erasable_types_tab)
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
        let uu____24533 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24601  ->
                  match uu____24601 with
                  | (m1,n11,uu____24619,uu____24620) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24533 with
        | FStar_Pervasives_Native.Some (uu____24645,uu____24646,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24691 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24766 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24766
                  (fun uu____24787  ->
                     match uu____24787 with
                     | (c1,g1) ->
                         let uu____24798 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24798
                           (fun uu____24819  ->
                              match uu____24819 with
                              | (c2,g2) ->
                                  let uu____24830 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24830)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24952 = l1 u t e  in
                              l2 u t uu____24952))
                | uu____24953 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25021  ->
                    match uu____25021 with
                    | (e,uu____25029) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25052 =
            match uu____25052 with
            | (i,j) ->
                let uu____25063 = FStar_Ident.lid_equals i j  in
                if uu____25063
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25070  -> FStar_Pervasives_Native.Some _25070)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25099 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25109 = FStar_Ident.lid_equals i k  in
                        if uu____25109
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25123 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25123
                                  then []
                                  else
                                    (let uu____25130 =
                                       let uu____25139 =
                                         find_edge order1 (i, k)  in
                                       let uu____25142 =
                                         find_edge order1 (k, j)  in
                                       (uu____25139, uu____25142)  in
                                     match uu____25130 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25157 =
                                           compose_edges e1 e2  in
                                         [uu____25157]
                                     | uu____25158 -> [])))))
                 in
              FStar_List.append order1 uu____25099  in
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
                  let uu____25188 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25191 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25191
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25188
                  then
                    let uu____25198 =
                      let uu____25204 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25204)
                       in
                    let uu____25208 = get_range env  in
                    FStar_Errors.raise_error uu____25198 uu____25208
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25286 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25286
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25338 =
                                             let uu____25347 =
                                               find_edge order2 (i, k)  in
                                             let uu____25350 =
                                               find_edge order2 (j, k)  in
                                             (uu____25347, uu____25350)  in
                                           match uu____25338 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25392,uu____25393)
                                                    ->
                                                    let uu____25400 =
                                                      let uu____25407 =
                                                        let uu____25409 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25409
                                                         in
                                                      let uu____25412 =
                                                        let uu____25414 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25414
                                                         in
                                                      (uu____25407,
                                                        uu____25412)
                                                       in
                                                    (match uu____25400 with
                                                     | (true ,true ) ->
                                                         let uu____25431 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25431
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
                                           | uu____25474 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25526 =
                                   let uu____25528 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25528
                                     FStar_Util.is_some
                                    in
                                 if uu____25526
                                 then
                                   let uu____25577 =
                                     let uu____25583 =
                                       let uu____25585 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25587 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25589 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25591 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25585 uu____25587 uu____25589
                                         uu____25591
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25583)
                                      in
                                   FStar_Errors.raise_error uu____25577
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1819_25630 = env.effects  in
             {
               decls = (uu___1819_25630.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1819_25630.polymonadic_binds)
             }  in
           let uu___1822_25631 = env  in
           {
             solver = (uu___1822_25631.solver);
             range = (uu___1822_25631.range);
             curmodule = (uu___1822_25631.curmodule);
             gamma = (uu___1822_25631.gamma);
             gamma_sig = (uu___1822_25631.gamma_sig);
             gamma_cache = (uu___1822_25631.gamma_cache);
             modules = (uu___1822_25631.modules);
             expected_typ = (uu___1822_25631.expected_typ);
             sigtab = (uu___1822_25631.sigtab);
             attrtab = (uu___1822_25631.attrtab);
             instantiate_imp = (uu___1822_25631.instantiate_imp);
             effects;
             generalize = (uu___1822_25631.generalize);
             letrecs = (uu___1822_25631.letrecs);
             top_level = (uu___1822_25631.top_level);
             check_uvars = (uu___1822_25631.check_uvars);
             use_eq = (uu___1822_25631.use_eq);
             use_eq_strict = (uu___1822_25631.use_eq_strict);
             is_iface = (uu___1822_25631.is_iface);
             admit = (uu___1822_25631.admit);
             lax = (uu___1822_25631.lax);
             lax_universes = (uu___1822_25631.lax_universes);
             phase1 = (uu___1822_25631.phase1);
             failhard = (uu___1822_25631.failhard);
             nosynth = (uu___1822_25631.nosynth);
             uvar_subtyping = (uu___1822_25631.uvar_subtyping);
             tc_term = (uu___1822_25631.tc_term);
             type_of = (uu___1822_25631.type_of);
             universe_of = (uu___1822_25631.universe_of);
             check_type_of = (uu___1822_25631.check_type_of);
             use_bv_sorts = (uu___1822_25631.use_bv_sorts);
             qtbl_name_and_index = (uu___1822_25631.qtbl_name_and_index);
             normalized_eff_names = (uu___1822_25631.normalized_eff_names);
             fv_delta_depths = (uu___1822_25631.fv_delta_depths);
             proof_ns = (uu___1822_25631.proof_ns);
             synth_hook = (uu___1822_25631.synth_hook);
             try_solve_implicits_hook =
               (uu___1822_25631.try_solve_implicits_hook);
             splice = (uu___1822_25631.splice);
             mpreprocess = (uu___1822_25631.mpreprocess);
             postprocess = (uu___1822_25631.postprocess);
             is_native_tactic = (uu___1822_25631.is_native_tactic);
             identifier_info = (uu___1822_25631.identifier_info);
             tc_hooks = (uu___1822_25631.tc_hooks);
             dsenv = (uu___1822_25631.dsenv);
             nbe = (uu___1822_25631.nbe);
             strict_args_tab = (uu___1822_25631.strict_args_tab);
             erasable_types_tab = (uu___1822_25631.erasable_types_tab)
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
              let uu____25679 = FStar_Ident.string_of_lid m  in
              let uu____25681 = FStar_Ident.string_of_lid n1  in
              let uu____25683 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25679 uu____25681 uu____25683
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25692 =
              let uu____25694 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25694 FStar_Util.is_some  in
            if uu____25692
            then
              let uu____25731 =
                let uu____25737 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25737)
                 in
              FStar_Errors.raise_error uu____25731 env.range
            else
              (let uu____25743 =
                 let uu____25745 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25745 FStar_Util.is_some  in
               if uu____25743
               then
                 let uu____25770 =
                   let uu____25776 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25776)
                    in
                 FStar_Errors.raise_error uu____25770 env.range
               else
                 (let uu___1837_25782 = env  in
                  {
                    solver = (uu___1837_25782.solver);
                    range = (uu___1837_25782.range);
                    curmodule = (uu___1837_25782.curmodule);
                    gamma = (uu___1837_25782.gamma);
                    gamma_sig = (uu___1837_25782.gamma_sig);
                    gamma_cache = (uu___1837_25782.gamma_cache);
                    modules = (uu___1837_25782.modules);
                    expected_typ = (uu___1837_25782.expected_typ);
                    sigtab = (uu___1837_25782.sigtab);
                    attrtab = (uu___1837_25782.attrtab);
                    instantiate_imp = (uu___1837_25782.instantiate_imp);
                    effects =
                      (let uu___1839_25784 = env.effects  in
                       {
                         decls = (uu___1839_25784.decls);
                         order = (uu___1839_25784.order);
                         joins = (uu___1839_25784.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1837_25782.generalize);
                    letrecs = (uu___1837_25782.letrecs);
                    top_level = (uu___1837_25782.top_level);
                    check_uvars = (uu___1837_25782.check_uvars);
                    use_eq = (uu___1837_25782.use_eq);
                    use_eq_strict = (uu___1837_25782.use_eq_strict);
                    is_iface = (uu___1837_25782.is_iface);
                    admit = (uu___1837_25782.admit);
                    lax = (uu___1837_25782.lax);
                    lax_universes = (uu___1837_25782.lax_universes);
                    phase1 = (uu___1837_25782.phase1);
                    failhard = (uu___1837_25782.failhard);
                    nosynth = (uu___1837_25782.nosynth);
                    uvar_subtyping = (uu___1837_25782.uvar_subtyping);
                    tc_term = (uu___1837_25782.tc_term);
                    type_of = (uu___1837_25782.type_of);
                    universe_of = (uu___1837_25782.universe_of);
                    check_type_of = (uu___1837_25782.check_type_of);
                    use_bv_sorts = (uu___1837_25782.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1837_25782.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1837_25782.normalized_eff_names);
                    fv_delta_depths = (uu___1837_25782.fv_delta_depths);
                    proof_ns = (uu___1837_25782.proof_ns);
                    synth_hook = (uu___1837_25782.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1837_25782.try_solve_implicits_hook);
                    splice = (uu___1837_25782.splice);
                    mpreprocess = (uu___1837_25782.mpreprocess);
                    postprocess = (uu___1837_25782.postprocess);
                    is_native_tactic = (uu___1837_25782.is_native_tactic);
                    identifier_info = (uu___1837_25782.identifier_info);
                    tc_hooks = (uu___1837_25782.tc_hooks);
                    dsenv = (uu___1837_25782.dsenv);
                    nbe = (uu___1837_25782.nbe);
                    strict_args_tab = (uu___1837_25782.strict_args_tab);
                    erasable_types_tab = (uu___1837_25782.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1843_25856 = env  in
      {
        solver = (uu___1843_25856.solver);
        range = (uu___1843_25856.range);
        curmodule = (uu___1843_25856.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1843_25856.gamma_sig);
        gamma_cache = (uu___1843_25856.gamma_cache);
        modules = (uu___1843_25856.modules);
        expected_typ = (uu___1843_25856.expected_typ);
        sigtab = (uu___1843_25856.sigtab);
        attrtab = (uu___1843_25856.attrtab);
        instantiate_imp = (uu___1843_25856.instantiate_imp);
        effects = (uu___1843_25856.effects);
        generalize = (uu___1843_25856.generalize);
        letrecs = (uu___1843_25856.letrecs);
        top_level = (uu___1843_25856.top_level);
        check_uvars = (uu___1843_25856.check_uvars);
        use_eq = (uu___1843_25856.use_eq);
        use_eq_strict = (uu___1843_25856.use_eq_strict);
        is_iface = (uu___1843_25856.is_iface);
        admit = (uu___1843_25856.admit);
        lax = (uu___1843_25856.lax);
        lax_universes = (uu___1843_25856.lax_universes);
        phase1 = (uu___1843_25856.phase1);
        failhard = (uu___1843_25856.failhard);
        nosynth = (uu___1843_25856.nosynth);
        uvar_subtyping = (uu___1843_25856.uvar_subtyping);
        tc_term = (uu___1843_25856.tc_term);
        type_of = (uu___1843_25856.type_of);
        universe_of = (uu___1843_25856.universe_of);
        check_type_of = (uu___1843_25856.check_type_of);
        use_bv_sorts = (uu___1843_25856.use_bv_sorts);
        qtbl_name_and_index = (uu___1843_25856.qtbl_name_and_index);
        normalized_eff_names = (uu___1843_25856.normalized_eff_names);
        fv_delta_depths = (uu___1843_25856.fv_delta_depths);
        proof_ns = (uu___1843_25856.proof_ns);
        synth_hook = (uu___1843_25856.synth_hook);
        try_solve_implicits_hook = (uu___1843_25856.try_solve_implicits_hook);
        splice = (uu___1843_25856.splice);
        mpreprocess = (uu___1843_25856.mpreprocess);
        postprocess = (uu___1843_25856.postprocess);
        is_native_tactic = (uu___1843_25856.is_native_tactic);
        identifier_info = (uu___1843_25856.identifier_info);
        tc_hooks = (uu___1843_25856.tc_hooks);
        dsenv = (uu___1843_25856.dsenv);
        nbe = (uu___1843_25856.nbe);
        strict_args_tab = (uu___1843_25856.strict_args_tab);
        erasable_types_tab = (uu___1843_25856.erasable_types_tab)
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
            (let uu___1856_25914 = env  in
             {
               solver = (uu___1856_25914.solver);
               range = (uu___1856_25914.range);
               curmodule = (uu___1856_25914.curmodule);
               gamma = rest;
               gamma_sig = (uu___1856_25914.gamma_sig);
               gamma_cache = (uu___1856_25914.gamma_cache);
               modules = (uu___1856_25914.modules);
               expected_typ = (uu___1856_25914.expected_typ);
               sigtab = (uu___1856_25914.sigtab);
               attrtab = (uu___1856_25914.attrtab);
               instantiate_imp = (uu___1856_25914.instantiate_imp);
               effects = (uu___1856_25914.effects);
               generalize = (uu___1856_25914.generalize);
               letrecs = (uu___1856_25914.letrecs);
               top_level = (uu___1856_25914.top_level);
               check_uvars = (uu___1856_25914.check_uvars);
               use_eq = (uu___1856_25914.use_eq);
               use_eq_strict = (uu___1856_25914.use_eq_strict);
               is_iface = (uu___1856_25914.is_iface);
               admit = (uu___1856_25914.admit);
               lax = (uu___1856_25914.lax);
               lax_universes = (uu___1856_25914.lax_universes);
               phase1 = (uu___1856_25914.phase1);
               failhard = (uu___1856_25914.failhard);
               nosynth = (uu___1856_25914.nosynth);
               uvar_subtyping = (uu___1856_25914.uvar_subtyping);
               tc_term = (uu___1856_25914.tc_term);
               type_of = (uu___1856_25914.type_of);
               universe_of = (uu___1856_25914.universe_of);
               check_type_of = (uu___1856_25914.check_type_of);
               use_bv_sorts = (uu___1856_25914.use_bv_sorts);
               qtbl_name_and_index = (uu___1856_25914.qtbl_name_and_index);
               normalized_eff_names = (uu___1856_25914.normalized_eff_names);
               fv_delta_depths = (uu___1856_25914.fv_delta_depths);
               proof_ns = (uu___1856_25914.proof_ns);
               synth_hook = (uu___1856_25914.synth_hook);
               try_solve_implicits_hook =
                 (uu___1856_25914.try_solve_implicits_hook);
               splice = (uu___1856_25914.splice);
               mpreprocess = (uu___1856_25914.mpreprocess);
               postprocess = (uu___1856_25914.postprocess);
               is_native_tactic = (uu___1856_25914.is_native_tactic);
               identifier_info = (uu___1856_25914.identifier_info);
               tc_hooks = (uu___1856_25914.tc_hooks);
               dsenv = (uu___1856_25914.dsenv);
               nbe = (uu___1856_25914.nbe);
               strict_args_tab = (uu___1856_25914.strict_args_tab);
               erasable_types_tab = (uu___1856_25914.erasable_types_tab)
             }))
    | uu____25915 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25944  ->
             match uu____25944 with | (x,uu____25952) -> push_bv env1 x) env
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
            let uu___1870_25987 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1870_25987.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1870_25987.FStar_Syntax_Syntax.index);
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
        let uu____26060 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26060 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26088 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26088)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1891_26104 = env  in
      {
        solver = (uu___1891_26104.solver);
        range = (uu___1891_26104.range);
        curmodule = (uu___1891_26104.curmodule);
        gamma = (uu___1891_26104.gamma);
        gamma_sig = (uu___1891_26104.gamma_sig);
        gamma_cache = (uu___1891_26104.gamma_cache);
        modules = (uu___1891_26104.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1891_26104.sigtab);
        attrtab = (uu___1891_26104.attrtab);
        instantiate_imp = (uu___1891_26104.instantiate_imp);
        effects = (uu___1891_26104.effects);
        generalize = (uu___1891_26104.generalize);
        letrecs = (uu___1891_26104.letrecs);
        top_level = (uu___1891_26104.top_level);
        check_uvars = (uu___1891_26104.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1891_26104.use_eq_strict);
        is_iface = (uu___1891_26104.is_iface);
        admit = (uu___1891_26104.admit);
        lax = (uu___1891_26104.lax);
        lax_universes = (uu___1891_26104.lax_universes);
        phase1 = (uu___1891_26104.phase1);
        failhard = (uu___1891_26104.failhard);
        nosynth = (uu___1891_26104.nosynth);
        uvar_subtyping = (uu___1891_26104.uvar_subtyping);
        tc_term = (uu___1891_26104.tc_term);
        type_of = (uu___1891_26104.type_of);
        universe_of = (uu___1891_26104.universe_of);
        check_type_of = (uu___1891_26104.check_type_of);
        use_bv_sorts = (uu___1891_26104.use_bv_sorts);
        qtbl_name_and_index = (uu___1891_26104.qtbl_name_and_index);
        normalized_eff_names = (uu___1891_26104.normalized_eff_names);
        fv_delta_depths = (uu___1891_26104.fv_delta_depths);
        proof_ns = (uu___1891_26104.proof_ns);
        synth_hook = (uu___1891_26104.synth_hook);
        try_solve_implicits_hook = (uu___1891_26104.try_solve_implicits_hook);
        splice = (uu___1891_26104.splice);
        mpreprocess = (uu___1891_26104.mpreprocess);
        postprocess = (uu___1891_26104.postprocess);
        is_native_tactic = (uu___1891_26104.is_native_tactic);
        identifier_info = (uu___1891_26104.identifier_info);
        tc_hooks = (uu___1891_26104.tc_hooks);
        dsenv = (uu___1891_26104.dsenv);
        nbe = (uu___1891_26104.nbe);
        strict_args_tab = (uu___1891_26104.strict_args_tab);
        erasable_types_tab = (uu___1891_26104.erasable_types_tab)
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
    let uu____26135 = expected_typ env_  in
    ((let uu___1898_26141 = env_  in
      {
        solver = (uu___1898_26141.solver);
        range = (uu___1898_26141.range);
        curmodule = (uu___1898_26141.curmodule);
        gamma = (uu___1898_26141.gamma);
        gamma_sig = (uu___1898_26141.gamma_sig);
        gamma_cache = (uu___1898_26141.gamma_cache);
        modules = (uu___1898_26141.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1898_26141.sigtab);
        attrtab = (uu___1898_26141.attrtab);
        instantiate_imp = (uu___1898_26141.instantiate_imp);
        effects = (uu___1898_26141.effects);
        generalize = (uu___1898_26141.generalize);
        letrecs = (uu___1898_26141.letrecs);
        top_level = (uu___1898_26141.top_level);
        check_uvars = (uu___1898_26141.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1898_26141.use_eq_strict);
        is_iface = (uu___1898_26141.is_iface);
        admit = (uu___1898_26141.admit);
        lax = (uu___1898_26141.lax);
        lax_universes = (uu___1898_26141.lax_universes);
        phase1 = (uu___1898_26141.phase1);
        failhard = (uu___1898_26141.failhard);
        nosynth = (uu___1898_26141.nosynth);
        uvar_subtyping = (uu___1898_26141.uvar_subtyping);
        tc_term = (uu___1898_26141.tc_term);
        type_of = (uu___1898_26141.type_of);
        universe_of = (uu___1898_26141.universe_of);
        check_type_of = (uu___1898_26141.check_type_of);
        use_bv_sorts = (uu___1898_26141.use_bv_sorts);
        qtbl_name_and_index = (uu___1898_26141.qtbl_name_and_index);
        normalized_eff_names = (uu___1898_26141.normalized_eff_names);
        fv_delta_depths = (uu___1898_26141.fv_delta_depths);
        proof_ns = (uu___1898_26141.proof_ns);
        synth_hook = (uu___1898_26141.synth_hook);
        try_solve_implicits_hook = (uu___1898_26141.try_solve_implicits_hook);
        splice = (uu___1898_26141.splice);
        mpreprocess = (uu___1898_26141.mpreprocess);
        postprocess = (uu___1898_26141.postprocess);
        is_native_tactic = (uu___1898_26141.is_native_tactic);
        identifier_info = (uu___1898_26141.identifier_info);
        tc_hooks = (uu___1898_26141.tc_hooks);
        dsenv = (uu___1898_26141.dsenv);
        nbe = (uu___1898_26141.nbe);
        strict_args_tab = (uu___1898_26141.strict_args_tab);
        erasable_types_tab = (uu___1898_26141.erasable_types_tab)
      }), uu____26135)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26153 =
      let uu____26156 = FStar_Ident.id_of_text ""  in [uu____26156]  in
    FStar_Ident.lid_of_ids uu____26153  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26163 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26163
        then
          let uu____26168 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26168 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1906_26196 = env  in
       {
         solver = (uu___1906_26196.solver);
         range = (uu___1906_26196.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1906_26196.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1906_26196.expected_typ);
         sigtab = (uu___1906_26196.sigtab);
         attrtab = (uu___1906_26196.attrtab);
         instantiate_imp = (uu___1906_26196.instantiate_imp);
         effects = (uu___1906_26196.effects);
         generalize = (uu___1906_26196.generalize);
         letrecs = (uu___1906_26196.letrecs);
         top_level = (uu___1906_26196.top_level);
         check_uvars = (uu___1906_26196.check_uvars);
         use_eq = (uu___1906_26196.use_eq);
         use_eq_strict = (uu___1906_26196.use_eq_strict);
         is_iface = (uu___1906_26196.is_iface);
         admit = (uu___1906_26196.admit);
         lax = (uu___1906_26196.lax);
         lax_universes = (uu___1906_26196.lax_universes);
         phase1 = (uu___1906_26196.phase1);
         failhard = (uu___1906_26196.failhard);
         nosynth = (uu___1906_26196.nosynth);
         uvar_subtyping = (uu___1906_26196.uvar_subtyping);
         tc_term = (uu___1906_26196.tc_term);
         type_of = (uu___1906_26196.type_of);
         universe_of = (uu___1906_26196.universe_of);
         check_type_of = (uu___1906_26196.check_type_of);
         use_bv_sorts = (uu___1906_26196.use_bv_sorts);
         qtbl_name_and_index = (uu___1906_26196.qtbl_name_and_index);
         normalized_eff_names = (uu___1906_26196.normalized_eff_names);
         fv_delta_depths = (uu___1906_26196.fv_delta_depths);
         proof_ns = (uu___1906_26196.proof_ns);
         synth_hook = (uu___1906_26196.synth_hook);
         try_solve_implicits_hook =
           (uu___1906_26196.try_solve_implicits_hook);
         splice = (uu___1906_26196.splice);
         mpreprocess = (uu___1906_26196.mpreprocess);
         postprocess = (uu___1906_26196.postprocess);
         is_native_tactic = (uu___1906_26196.is_native_tactic);
         identifier_info = (uu___1906_26196.identifier_info);
         tc_hooks = (uu___1906_26196.tc_hooks);
         dsenv = (uu___1906_26196.dsenv);
         nbe = (uu___1906_26196.nbe);
         strict_args_tab = (uu___1906_26196.strict_args_tab);
         erasable_types_tab = (uu___1906_26196.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26248)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26252,(uu____26253,t)))::tl1
          ->
          let uu____26274 =
            let uu____26277 = FStar_Syntax_Free.uvars t  in
            ext out uu____26277  in
          aux uu____26274 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26280;
            FStar_Syntax_Syntax.index = uu____26281;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26289 =
            let uu____26292 = FStar_Syntax_Free.uvars t  in
            ext out uu____26292  in
          aux uu____26289 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26350)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26354,(uu____26355,t)))::tl1
          ->
          let uu____26376 =
            let uu____26379 = FStar_Syntax_Free.univs t  in
            ext out uu____26379  in
          aux uu____26376 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26382;
            FStar_Syntax_Syntax.index = uu____26383;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26391 =
            let uu____26394 = FStar_Syntax_Free.univs t  in
            ext out uu____26394  in
          aux uu____26391 tl1
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
          let uu____26456 = FStar_Util.set_add uname out  in
          aux uu____26456 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26459,(uu____26460,t)))::tl1
          ->
          let uu____26481 =
            let uu____26484 = FStar_Syntax_Free.univnames t  in
            ext out uu____26484  in
          aux uu____26481 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26487;
            FStar_Syntax_Syntax.index = uu____26488;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26496 =
            let uu____26499 = FStar_Syntax_Free.univnames t  in
            ext out uu____26499  in
          aux uu____26496 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26520  ->
            match uu___12_26520 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26524 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26537 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26548 =
      let uu____26557 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26557
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26548 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26605 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26618  ->
              match uu___13_26618 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26621 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26621
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26627) ->
                  let uu____26644 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26644))
       in
    FStar_All.pipe_right uu____26605 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26658  ->
    match uu___14_26658 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26664 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26664
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26687  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26742) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26775,uu____26776) -> false  in
      let uu____26790 =
        FStar_List.tryFind
          (fun uu____26812  ->
             match uu____26812 with | (p,uu____26823) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26790 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26842,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26872 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26872
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2049_26894 = e  in
        {
          solver = (uu___2049_26894.solver);
          range = (uu___2049_26894.range);
          curmodule = (uu___2049_26894.curmodule);
          gamma = (uu___2049_26894.gamma);
          gamma_sig = (uu___2049_26894.gamma_sig);
          gamma_cache = (uu___2049_26894.gamma_cache);
          modules = (uu___2049_26894.modules);
          expected_typ = (uu___2049_26894.expected_typ);
          sigtab = (uu___2049_26894.sigtab);
          attrtab = (uu___2049_26894.attrtab);
          instantiate_imp = (uu___2049_26894.instantiate_imp);
          effects = (uu___2049_26894.effects);
          generalize = (uu___2049_26894.generalize);
          letrecs = (uu___2049_26894.letrecs);
          top_level = (uu___2049_26894.top_level);
          check_uvars = (uu___2049_26894.check_uvars);
          use_eq = (uu___2049_26894.use_eq);
          use_eq_strict = (uu___2049_26894.use_eq_strict);
          is_iface = (uu___2049_26894.is_iface);
          admit = (uu___2049_26894.admit);
          lax = (uu___2049_26894.lax);
          lax_universes = (uu___2049_26894.lax_universes);
          phase1 = (uu___2049_26894.phase1);
          failhard = (uu___2049_26894.failhard);
          nosynth = (uu___2049_26894.nosynth);
          uvar_subtyping = (uu___2049_26894.uvar_subtyping);
          tc_term = (uu___2049_26894.tc_term);
          type_of = (uu___2049_26894.type_of);
          universe_of = (uu___2049_26894.universe_of);
          check_type_of = (uu___2049_26894.check_type_of);
          use_bv_sorts = (uu___2049_26894.use_bv_sorts);
          qtbl_name_and_index = (uu___2049_26894.qtbl_name_and_index);
          normalized_eff_names = (uu___2049_26894.normalized_eff_names);
          fv_delta_depths = (uu___2049_26894.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2049_26894.synth_hook);
          try_solve_implicits_hook =
            (uu___2049_26894.try_solve_implicits_hook);
          splice = (uu___2049_26894.splice);
          mpreprocess = (uu___2049_26894.mpreprocess);
          postprocess = (uu___2049_26894.postprocess);
          is_native_tactic = (uu___2049_26894.is_native_tactic);
          identifier_info = (uu___2049_26894.identifier_info);
          tc_hooks = (uu___2049_26894.tc_hooks);
          dsenv = (uu___2049_26894.dsenv);
          nbe = (uu___2049_26894.nbe);
          strict_args_tab = (uu___2049_26894.strict_args_tab);
          erasable_types_tab = (uu___2049_26894.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2058_26942 = e  in
      {
        solver = (uu___2058_26942.solver);
        range = (uu___2058_26942.range);
        curmodule = (uu___2058_26942.curmodule);
        gamma = (uu___2058_26942.gamma);
        gamma_sig = (uu___2058_26942.gamma_sig);
        gamma_cache = (uu___2058_26942.gamma_cache);
        modules = (uu___2058_26942.modules);
        expected_typ = (uu___2058_26942.expected_typ);
        sigtab = (uu___2058_26942.sigtab);
        attrtab = (uu___2058_26942.attrtab);
        instantiate_imp = (uu___2058_26942.instantiate_imp);
        effects = (uu___2058_26942.effects);
        generalize = (uu___2058_26942.generalize);
        letrecs = (uu___2058_26942.letrecs);
        top_level = (uu___2058_26942.top_level);
        check_uvars = (uu___2058_26942.check_uvars);
        use_eq = (uu___2058_26942.use_eq);
        use_eq_strict = (uu___2058_26942.use_eq_strict);
        is_iface = (uu___2058_26942.is_iface);
        admit = (uu___2058_26942.admit);
        lax = (uu___2058_26942.lax);
        lax_universes = (uu___2058_26942.lax_universes);
        phase1 = (uu___2058_26942.phase1);
        failhard = (uu___2058_26942.failhard);
        nosynth = (uu___2058_26942.nosynth);
        uvar_subtyping = (uu___2058_26942.uvar_subtyping);
        tc_term = (uu___2058_26942.tc_term);
        type_of = (uu___2058_26942.type_of);
        universe_of = (uu___2058_26942.universe_of);
        check_type_of = (uu___2058_26942.check_type_of);
        use_bv_sorts = (uu___2058_26942.use_bv_sorts);
        qtbl_name_and_index = (uu___2058_26942.qtbl_name_and_index);
        normalized_eff_names = (uu___2058_26942.normalized_eff_names);
        fv_delta_depths = (uu___2058_26942.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2058_26942.synth_hook);
        try_solve_implicits_hook = (uu___2058_26942.try_solve_implicits_hook);
        splice = (uu___2058_26942.splice);
        mpreprocess = (uu___2058_26942.mpreprocess);
        postprocess = (uu___2058_26942.postprocess);
        is_native_tactic = (uu___2058_26942.is_native_tactic);
        identifier_info = (uu___2058_26942.identifier_info);
        tc_hooks = (uu___2058_26942.tc_hooks);
        dsenv = (uu___2058_26942.dsenv);
        nbe = (uu___2058_26942.nbe);
        strict_args_tab = (uu___2058_26942.strict_args_tab);
        erasable_types_tab = (uu___2058_26942.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26958 = FStar_Syntax_Free.names t  in
      let uu____26961 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26958 uu____26961
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26984 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26984
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26994 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26994
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27015 =
      match uu____27015 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27035 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27035)
       in
    let uu____27043 =
      let uu____27047 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27047 FStar_List.rev  in
    FStar_All.pipe_right uu____27043 (FStar_String.concat " ")
  
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
                  (let uu____27115 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27115 with
                   | FStar_Pervasives_Native.Some uu____27119 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27122 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27132;
        FStar_TypeChecker_Common.univ_ineqs = uu____27133;
        FStar_TypeChecker_Common.implicits = uu____27134;_} -> true
    | uu____27144 -> false
  
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
          let uu___2102_27166 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2102_27166.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2102_27166.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2102_27166.FStar_TypeChecker_Common.implicits)
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
          let uu____27205 = FStar_Options.defensive ()  in
          if uu____27205
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27211 =
              let uu____27213 =
                let uu____27215 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27215  in
              Prims.op_Negation uu____27213  in
            (if uu____27211
             then
               let uu____27222 =
                 let uu____27228 =
                   let uu____27230 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27232 =
                     let uu____27234 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27234
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27230 uu____27232
                    in
                 (FStar_Errors.Warning_Defensive, uu____27228)  in
               FStar_Errors.log_issue rng uu____27222
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
          let uu____27274 =
            let uu____27276 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27276  in
          if uu____27274
          then ()
          else
            (let uu____27281 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27281 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27307 =
            let uu____27309 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27309  in
          if uu____27307
          then ()
          else
            (let uu____27314 = bound_vars e  in
             def_check_closed_in rng msg uu____27314 t)
  
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
          let uu___2139_27353 = g  in
          let uu____27354 =
            let uu____27355 =
              let uu____27356 =
                let uu____27363 =
                  let uu____27364 =
                    let uu____27381 =
                      let uu____27392 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27392]  in
                    (f, uu____27381)  in
                  FStar_Syntax_Syntax.Tm_app uu____27364  in
                FStar_Syntax_Syntax.mk uu____27363  in
              uu____27356 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27429  -> FStar_TypeChecker_Common.NonTrivial _27429)
              uu____27355
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27354;
            FStar_TypeChecker_Common.deferred =
              (uu___2139_27353.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2139_27353.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2139_27353.FStar_TypeChecker_Common.implicits)
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
          let uu___2146_27447 = g  in
          let uu____27448 =
            let uu____27449 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27449  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27448;
            FStar_TypeChecker_Common.deferred =
              (uu___2146_27447.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2146_27447.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2146_27447.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2151_27466 = g  in
          let uu____27467 =
            let uu____27468 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27468  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27467;
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27466.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27466.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27466.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2155_27470 = g  in
          let uu____27471 =
            let uu____27472 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27472  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27471;
            FStar_TypeChecker_Common.deferred =
              (uu___2155_27470.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2155_27470.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2155_27470.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27479 ->
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
                       let uu____27556 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27556
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2178_27563 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2178_27563.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2178_27563.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2178_27563.FStar_TypeChecker_Common.implicits)
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
               let uu____27597 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27597
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
            let uu___2193_27624 = g  in
            let uu____27625 =
              let uu____27626 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27626  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27625;
              FStar_TypeChecker_Common.deferred =
                (uu___2193_27624.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2193_27624.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2193_27624.FStar_TypeChecker_Common.implicits)
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
              let uu____27684 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27684 with
              | FStar_Pervasives_Native.Some
                  (uu____27709::(tm,uu____27711)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27775 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27793 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27793;
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
                      let uu___2215_27825 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2215_27825.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2215_27825.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2215_27825.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27879 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27936  ->
                      fun b  ->
                        match uu____27936 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27978 =
                              let uu____27991 = reason b  in
                              new_implicit_var_aux uu____27991 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27978 with
                             | (t,uu____28008,g_t) ->
                                 let uu____28022 =
                                   let uu____28025 =
                                     let uu____28028 =
                                       let uu____28029 =
                                         let uu____28036 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28036, t)  in
                                       FStar_Syntax_Syntax.NT uu____28029  in
                                     [uu____28028]  in
                                   FStar_List.append substs1 uu____28025  in
                                 let uu____28047 = conj_guard g g_t  in
                                 (uu____28022,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28047))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27879
              (fun uu____28076  ->
                 match uu____28076 with
                 | (uu____28093,uvars1,g) -> (uvars1, g))
  
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
                let uu____28134 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28134 FStar_Util.must  in
              let uu____28151 = inst_tscheme_with post_ts [u]  in
              match uu____28151 with
              | (uu____28156,post) ->
                  let uu____28158 =
                    let uu____28163 =
                      let uu____28164 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28164]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28163  in
                  uu____28158 FStar_Pervasives_Native.None r
               in
            let uu____28197 =
              let uu____28202 =
                let uu____28203 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28203]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28202  in
            uu____28197 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28239  -> ());
    push = (fun uu____28241  -> ());
    pop = (fun uu____28244  -> ());
    snapshot =
      (fun uu____28247  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28266  -> fun uu____28267  -> ());
    encode_sig = (fun uu____28282  -> fun uu____28283  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28289 =
             let uu____28296 = FStar_Options.peek ()  in (e, g, uu____28296)
              in
           [uu____28289]);
    solve = (fun uu____28312  -> fun uu____28313  -> fun uu____28314  -> ());
    finish = (fun uu____28321  -> ());
    refresh = (fun uu____28323  -> ())
  } 