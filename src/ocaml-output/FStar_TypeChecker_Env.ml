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
           (fun uu___0_14362  ->
              match uu___0_14362 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14365 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14365  in
                  let uu____14366 =
                    let uu____14367 = FStar_Syntax_Subst.compress y  in
                    uu____14367.FStar_Syntax_Syntax.n  in
                  (match uu____14366 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14371 =
                         let uu___324_14372 = y1  in
                         let uu____14373 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___324_14372.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___324_14372.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14373
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14371
                   | uu____14376 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___330_14390 = env  in
      let uu____14391 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___330_14390.solver);
        range = (uu___330_14390.range);
        curmodule = (uu___330_14390.curmodule);
        gamma = uu____14391;
        gamma_sig = (uu___330_14390.gamma_sig);
        gamma_cache = (uu___330_14390.gamma_cache);
        modules = (uu___330_14390.modules);
        expected_typ = (uu___330_14390.expected_typ);
        sigtab = (uu___330_14390.sigtab);
        attrtab = (uu___330_14390.attrtab);
        instantiate_imp = (uu___330_14390.instantiate_imp);
        effects = (uu___330_14390.effects);
        generalize = (uu___330_14390.generalize);
        letrecs = (uu___330_14390.letrecs);
        top_level = (uu___330_14390.top_level);
        check_uvars = (uu___330_14390.check_uvars);
        use_eq = (uu___330_14390.use_eq);
        use_eq_strict = (uu___330_14390.use_eq_strict);
        is_iface = (uu___330_14390.is_iface);
        admit = (uu___330_14390.admit);
        lax = (uu___330_14390.lax);
        lax_universes = (uu___330_14390.lax_universes);
        phase1 = (uu___330_14390.phase1);
        failhard = (uu___330_14390.failhard);
        nosynth = (uu___330_14390.nosynth);
        uvar_subtyping = (uu___330_14390.uvar_subtyping);
        tc_term = (uu___330_14390.tc_term);
        type_of = (uu___330_14390.type_of);
        universe_of = (uu___330_14390.universe_of);
        check_type_of = (uu___330_14390.check_type_of);
        use_bv_sorts = (uu___330_14390.use_bv_sorts);
        qtbl_name_and_index = (uu___330_14390.qtbl_name_and_index);
        normalized_eff_names = (uu___330_14390.normalized_eff_names);
        fv_delta_depths = (uu___330_14390.fv_delta_depths);
        proof_ns = (uu___330_14390.proof_ns);
        synth_hook = (uu___330_14390.synth_hook);
        try_solve_implicits_hook = (uu___330_14390.try_solve_implicits_hook);
        splice = (uu___330_14390.splice);
        mpreprocess = (uu___330_14390.mpreprocess);
        postprocess = (uu___330_14390.postprocess);
        is_native_tactic = (uu___330_14390.is_native_tactic);
        identifier_info = (uu___330_14390.identifier_info);
        tc_hooks = (uu___330_14390.tc_hooks);
        dsenv = (uu___330_14390.dsenv);
        nbe = (uu___330_14390.nbe);
        strict_args_tab = (uu___330_14390.strict_args_tab);
        erasable_types_tab = (uu___330_14390.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14399  -> fun uu____14400  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___337_14422 = env  in
      {
        solver = (uu___337_14422.solver);
        range = (uu___337_14422.range);
        curmodule = (uu___337_14422.curmodule);
        gamma = (uu___337_14422.gamma);
        gamma_sig = (uu___337_14422.gamma_sig);
        gamma_cache = (uu___337_14422.gamma_cache);
        modules = (uu___337_14422.modules);
        expected_typ = (uu___337_14422.expected_typ);
        sigtab = (uu___337_14422.sigtab);
        attrtab = (uu___337_14422.attrtab);
        instantiate_imp = (uu___337_14422.instantiate_imp);
        effects = (uu___337_14422.effects);
        generalize = (uu___337_14422.generalize);
        letrecs = (uu___337_14422.letrecs);
        top_level = (uu___337_14422.top_level);
        check_uvars = (uu___337_14422.check_uvars);
        use_eq = (uu___337_14422.use_eq);
        use_eq_strict = (uu___337_14422.use_eq_strict);
        is_iface = (uu___337_14422.is_iface);
        admit = (uu___337_14422.admit);
        lax = (uu___337_14422.lax);
        lax_universes = (uu___337_14422.lax_universes);
        phase1 = (uu___337_14422.phase1);
        failhard = (uu___337_14422.failhard);
        nosynth = (uu___337_14422.nosynth);
        uvar_subtyping = (uu___337_14422.uvar_subtyping);
        tc_term = (uu___337_14422.tc_term);
        type_of = (uu___337_14422.type_of);
        universe_of = (uu___337_14422.universe_of);
        check_type_of = (uu___337_14422.check_type_of);
        use_bv_sorts = (uu___337_14422.use_bv_sorts);
        qtbl_name_and_index = (uu___337_14422.qtbl_name_and_index);
        normalized_eff_names = (uu___337_14422.normalized_eff_names);
        fv_delta_depths = (uu___337_14422.fv_delta_depths);
        proof_ns = (uu___337_14422.proof_ns);
        synth_hook = (uu___337_14422.synth_hook);
        try_solve_implicits_hook = (uu___337_14422.try_solve_implicits_hook);
        splice = (uu___337_14422.splice);
        mpreprocess = (uu___337_14422.mpreprocess);
        postprocess = (uu___337_14422.postprocess);
        is_native_tactic = (uu___337_14422.is_native_tactic);
        identifier_info = (uu___337_14422.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___337_14422.dsenv);
        nbe = (uu___337_14422.nbe);
        strict_args_tab = (uu___337_14422.strict_args_tab);
        erasable_types_tab = (uu___337_14422.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___341_14434 = e  in
      let uu____14435 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___341_14434.solver);
        range = (uu___341_14434.range);
        curmodule = (uu___341_14434.curmodule);
        gamma = (uu___341_14434.gamma);
        gamma_sig = (uu___341_14434.gamma_sig);
        gamma_cache = (uu___341_14434.gamma_cache);
        modules = (uu___341_14434.modules);
        expected_typ = (uu___341_14434.expected_typ);
        sigtab = (uu___341_14434.sigtab);
        attrtab = (uu___341_14434.attrtab);
        instantiate_imp = (uu___341_14434.instantiate_imp);
        effects = (uu___341_14434.effects);
        generalize = (uu___341_14434.generalize);
        letrecs = (uu___341_14434.letrecs);
        top_level = (uu___341_14434.top_level);
        check_uvars = (uu___341_14434.check_uvars);
        use_eq = (uu___341_14434.use_eq);
        use_eq_strict = (uu___341_14434.use_eq_strict);
        is_iface = (uu___341_14434.is_iface);
        admit = (uu___341_14434.admit);
        lax = (uu___341_14434.lax);
        lax_universes = (uu___341_14434.lax_universes);
        phase1 = (uu___341_14434.phase1);
        failhard = (uu___341_14434.failhard);
        nosynth = (uu___341_14434.nosynth);
        uvar_subtyping = (uu___341_14434.uvar_subtyping);
        tc_term = (uu___341_14434.tc_term);
        type_of = (uu___341_14434.type_of);
        universe_of = (uu___341_14434.universe_of);
        check_type_of = (uu___341_14434.check_type_of);
        use_bv_sorts = (uu___341_14434.use_bv_sorts);
        qtbl_name_and_index = (uu___341_14434.qtbl_name_and_index);
        normalized_eff_names = (uu___341_14434.normalized_eff_names);
        fv_delta_depths = (uu___341_14434.fv_delta_depths);
        proof_ns = (uu___341_14434.proof_ns);
        synth_hook = (uu___341_14434.synth_hook);
        try_solve_implicits_hook = (uu___341_14434.try_solve_implicits_hook);
        splice = (uu___341_14434.splice);
        mpreprocess = (uu___341_14434.mpreprocess);
        postprocess = (uu___341_14434.postprocess);
        is_native_tactic = (uu___341_14434.is_native_tactic);
        identifier_info = (uu___341_14434.identifier_info);
        tc_hooks = (uu___341_14434.tc_hooks);
        dsenv = uu____14435;
        nbe = (uu___341_14434.nbe);
        strict_args_tab = (uu___341_14434.strict_args_tab);
        erasable_types_tab = (uu___341_14434.erasable_types_tab)
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
      | (NoDelta ,uu____14464) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14467,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14469,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14472 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14486 . unit -> 'Auu____14486 FStar_Util.smap =
  fun uu____14493  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14499 . unit -> 'Auu____14499 FStar_Util.smap =
  fun uu____14506  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14644 = new_gamma_cache ()  in
                  let uu____14647 = new_sigtab ()  in
                  let uu____14650 = new_sigtab ()  in
                  let uu____14657 =
                    let uu____14672 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14672, FStar_Pervasives_Native.None)  in
                  let uu____14693 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14697 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14701 = FStar_Options.using_facts_from ()  in
                  let uu____14702 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14705 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14706 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14720 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14644;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14647;
                    attrtab = uu____14650;
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
                    qtbl_name_and_index = uu____14657;
                    normalized_eff_names = uu____14693;
                    fv_delta_depths = uu____14697;
                    proof_ns = uu____14701;
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
                    is_native_tactic = (fun uu____14835  -> false);
                    identifier_info = uu____14702;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14705;
                    nbe = nbe1;
                    strict_args_tab = uu____14706;
                    erasable_types_tab = uu____14720
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
  fun uu____14914  ->
    let uu____14915 = FStar_ST.op_Bang query_indices  in
    match uu____14915 with
    | [] -> failwith "Empty query indices!"
    | uu____14970 ->
        let uu____14980 =
          let uu____14990 =
            let uu____14998 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14998  in
          let uu____15052 = FStar_ST.op_Bang query_indices  in uu____14990 ::
            uu____15052
           in
        FStar_ST.op_Colon_Equals query_indices uu____14980
  
let (pop_query_indices : unit -> unit) =
  fun uu____15148  ->
    let uu____15149 = FStar_ST.op_Bang query_indices  in
    match uu____15149 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15276  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15313  ->
    match uu____15313 with
    | (l,n1) ->
        let uu____15323 = FStar_ST.op_Bang query_indices  in
        (match uu____15323 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15445 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15468  ->
    let uu____15469 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15469
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15537 =
       let uu____15540 = FStar_ST.op_Bang stack  in env :: uu____15540  in
     FStar_ST.op_Colon_Equals stack uu____15537);
    (let uu___415_15589 = env  in
     let uu____15590 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15593 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15596 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15603 =
       let uu____15618 =
         let uu____15622 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15622  in
       let uu____15654 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15618, uu____15654)  in
     let uu____15703 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____15706 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____15709 =
       let uu____15712 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____15712  in
     let uu____15732 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15745 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___415_15589.solver);
       range = (uu___415_15589.range);
       curmodule = (uu___415_15589.curmodule);
       gamma = (uu___415_15589.gamma);
       gamma_sig = (uu___415_15589.gamma_sig);
       gamma_cache = uu____15590;
       modules = (uu___415_15589.modules);
       expected_typ = (uu___415_15589.expected_typ);
       sigtab = uu____15593;
       attrtab = uu____15596;
       instantiate_imp = (uu___415_15589.instantiate_imp);
       effects = (uu___415_15589.effects);
       generalize = (uu___415_15589.generalize);
       letrecs = (uu___415_15589.letrecs);
       top_level = (uu___415_15589.top_level);
       check_uvars = (uu___415_15589.check_uvars);
       use_eq = (uu___415_15589.use_eq);
       use_eq_strict = (uu___415_15589.use_eq_strict);
       is_iface = (uu___415_15589.is_iface);
       admit = (uu___415_15589.admit);
       lax = (uu___415_15589.lax);
       lax_universes = (uu___415_15589.lax_universes);
       phase1 = (uu___415_15589.phase1);
       failhard = (uu___415_15589.failhard);
       nosynth = (uu___415_15589.nosynth);
       uvar_subtyping = (uu___415_15589.uvar_subtyping);
       tc_term = (uu___415_15589.tc_term);
       type_of = (uu___415_15589.type_of);
       universe_of = (uu___415_15589.universe_of);
       check_type_of = (uu___415_15589.check_type_of);
       use_bv_sorts = (uu___415_15589.use_bv_sorts);
       qtbl_name_and_index = uu____15603;
       normalized_eff_names = uu____15703;
       fv_delta_depths = uu____15706;
       proof_ns = (uu___415_15589.proof_ns);
       synth_hook = (uu___415_15589.synth_hook);
       try_solve_implicits_hook = (uu___415_15589.try_solve_implicits_hook);
       splice = (uu___415_15589.splice);
       mpreprocess = (uu___415_15589.mpreprocess);
       postprocess = (uu___415_15589.postprocess);
       is_native_tactic = (uu___415_15589.is_native_tactic);
       identifier_info = uu____15709;
       tc_hooks = (uu___415_15589.tc_hooks);
       dsenv = (uu___415_15589.dsenv);
       nbe = (uu___415_15589.nbe);
       strict_args_tab = uu____15732;
       erasable_types_tab = uu____15745
     })
  
let (pop_stack : unit -> env) =
  fun uu____15755  ->
    let uu____15756 = FStar_ST.op_Bang stack  in
    match uu____15756 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15810 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15900  ->
           let uu____15901 = snapshot_stack env  in
           match uu____15901 with
           | (stack_depth,env1) ->
               let uu____15935 = snapshot_query_indices ()  in
               (match uu____15935 with
                | (query_indices_depth,()) ->
                    let uu____15968 = (env1.solver).snapshot msg  in
                    (match uu____15968 with
                     | (solver_depth,()) ->
                         let uu____16025 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____16025 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___440_16092 = env1  in
                                 {
                                   solver = (uu___440_16092.solver);
                                   range = (uu___440_16092.range);
                                   curmodule = (uu___440_16092.curmodule);
                                   gamma = (uu___440_16092.gamma);
                                   gamma_sig = (uu___440_16092.gamma_sig);
                                   gamma_cache = (uu___440_16092.gamma_cache);
                                   modules = (uu___440_16092.modules);
                                   expected_typ =
                                     (uu___440_16092.expected_typ);
                                   sigtab = (uu___440_16092.sigtab);
                                   attrtab = (uu___440_16092.attrtab);
                                   instantiate_imp =
                                     (uu___440_16092.instantiate_imp);
                                   effects = (uu___440_16092.effects);
                                   generalize = (uu___440_16092.generalize);
                                   letrecs = (uu___440_16092.letrecs);
                                   top_level = (uu___440_16092.top_level);
                                   check_uvars = (uu___440_16092.check_uvars);
                                   use_eq = (uu___440_16092.use_eq);
                                   use_eq_strict =
                                     (uu___440_16092.use_eq_strict);
                                   is_iface = (uu___440_16092.is_iface);
                                   admit = (uu___440_16092.admit);
                                   lax = (uu___440_16092.lax);
                                   lax_universes =
                                     (uu___440_16092.lax_universes);
                                   phase1 = (uu___440_16092.phase1);
                                   failhard = (uu___440_16092.failhard);
                                   nosynth = (uu___440_16092.nosynth);
                                   uvar_subtyping =
                                     (uu___440_16092.uvar_subtyping);
                                   tc_term = (uu___440_16092.tc_term);
                                   type_of = (uu___440_16092.type_of);
                                   universe_of = (uu___440_16092.universe_of);
                                   check_type_of =
                                     (uu___440_16092.check_type_of);
                                   use_bv_sorts =
                                     (uu___440_16092.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___440_16092.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___440_16092.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___440_16092.fv_delta_depths);
                                   proof_ns = (uu___440_16092.proof_ns);
                                   synth_hook = (uu___440_16092.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___440_16092.try_solve_implicits_hook);
                                   splice = (uu___440_16092.splice);
                                   mpreprocess = (uu___440_16092.mpreprocess);
                                   postprocess = (uu___440_16092.postprocess);
                                   is_native_tactic =
                                     (uu___440_16092.is_native_tactic);
                                   identifier_info =
                                     (uu___440_16092.identifier_info);
                                   tc_hooks = (uu___440_16092.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___440_16092.nbe);
                                   strict_args_tab =
                                     (uu___440_16092.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___440_16092.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16126  ->
             let uu____16127 =
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
             match uu____16127 with
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
                             ((let uu____16307 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16307
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____16323 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____16323
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16355,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16397 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16427  ->
                  match uu____16427 with
                  | (m,uu____16435) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16397 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___485_16450 = env  in
               {
                 solver = (uu___485_16450.solver);
                 range = (uu___485_16450.range);
                 curmodule = (uu___485_16450.curmodule);
                 gamma = (uu___485_16450.gamma);
                 gamma_sig = (uu___485_16450.gamma_sig);
                 gamma_cache = (uu___485_16450.gamma_cache);
                 modules = (uu___485_16450.modules);
                 expected_typ = (uu___485_16450.expected_typ);
                 sigtab = (uu___485_16450.sigtab);
                 attrtab = (uu___485_16450.attrtab);
                 instantiate_imp = (uu___485_16450.instantiate_imp);
                 effects = (uu___485_16450.effects);
                 generalize = (uu___485_16450.generalize);
                 letrecs = (uu___485_16450.letrecs);
                 top_level = (uu___485_16450.top_level);
                 check_uvars = (uu___485_16450.check_uvars);
                 use_eq = (uu___485_16450.use_eq);
                 use_eq_strict = (uu___485_16450.use_eq_strict);
                 is_iface = (uu___485_16450.is_iface);
                 admit = (uu___485_16450.admit);
                 lax = (uu___485_16450.lax);
                 lax_universes = (uu___485_16450.lax_universes);
                 phase1 = (uu___485_16450.phase1);
                 failhard = (uu___485_16450.failhard);
                 nosynth = (uu___485_16450.nosynth);
                 uvar_subtyping = (uu___485_16450.uvar_subtyping);
                 tc_term = (uu___485_16450.tc_term);
                 type_of = (uu___485_16450.type_of);
                 universe_of = (uu___485_16450.universe_of);
                 check_type_of = (uu___485_16450.check_type_of);
                 use_bv_sorts = (uu___485_16450.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___485_16450.normalized_eff_names);
                 fv_delta_depths = (uu___485_16450.fv_delta_depths);
                 proof_ns = (uu___485_16450.proof_ns);
                 synth_hook = (uu___485_16450.synth_hook);
                 try_solve_implicits_hook =
                   (uu___485_16450.try_solve_implicits_hook);
                 splice = (uu___485_16450.splice);
                 mpreprocess = (uu___485_16450.mpreprocess);
                 postprocess = (uu___485_16450.postprocess);
                 is_native_tactic = (uu___485_16450.is_native_tactic);
                 identifier_info = (uu___485_16450.identifier_info);
                 tc_hooks = (uu___485_16450.tc_hooks);
                 dsenv = (uu___485_16450.dsenv);
                 nbe = (uu___485_16450.nbe);
                 strict_args_tab = (uu___485_16450.strict_args_tab);
                 erasable_types_tab = (uu___485_16450.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16467,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___494_16483 = env  in
               {
                 solver = (uu___494_16483.solver);
                 range = (uu___494_16483.range);
                 curmodule = (uu___494_16483.curmodule);
                 gamma = (uu___494_16483.gamma);
                 gamma_sig = (uu___494_16483.gamma_sig);
                 gamma_cache = (uu___494_16483.gamma_cache);
                 modules = (uu___494_16483.modules);
                 expected_typ = (uu___494_16483.expected_typ);
                 sigtab = (uu___494_16483.sigtab);
                 attrtab = (uu___494_16483.attrtab);
                 instantiate_imp = (uu___494_16483.instantiate_imp);
                 effects = (uu___494_16483.effects);
                 generalize = (uu___494_16483.generalize);
                 letrecs = (uu___494_16483.letrecs);
                 top_level = (uu___494_16483.top_level);
                 check_uvars = (uu___494_16483.check_uvars);
                 use_eq = (uu___494_16483.use_eq);
                 use_eq_strict = (uu___494_16483.use_eq_strict);
                 is_iface = (uu___494_16483.is_iface);
                 admit = (uu___494_16483.admit);
                 lax = (uu___494_16483.lax);
                 lax_universes = (uu___494_16483.lax_universes);
                 phase1 = (uu___494_16483.phase1);
                 failhard = (uu___494_16483.failhard);
                 nosynth = (uu___494_16483.nosynth);
                 uvar_subtyping = (uu___494_16483.uvar_subtyping);
                 tc_term = (uu___494_16483.tc_term);
                 type_of = (uu___494_16483.type_of);
                 universe_of = (uu___494_16483.universe_of);
                 check_type_of = (uu___494_16483.check_type_of);
                 use_bv_sorts = (uu___494_16483.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___494_16483.normalized_eff_names);
                 fv_delta_depths = (uu___494_16483.fv_delta_depths);
                 proof_ns = (uu___494_16483.proof_ns);
                 synth_hook = (uu___494_16483.synth_hook);
                 try_solve_implicits_hook =
                   (uu___494_16483.try_solve_implicits_hook);
                 splice = (uu___494_16483.splice);
                 mpreprocess = (uu___494_16483.mpreprocess);
                 postprocess = (uu___494_16483.postprocess);
                 is_native_tactic = (uu___494_16483.is_native_tactic);
                 identifier_info = (uu___494_16483.identifier_info);
                 tc_hooks = (uu___494_16483.tc_hooks);
                 dsenv = (uu___494_16483.dsenv);
                 nbe = (uu___494_16483.nbe);
                 strict_args_tab = (uu___494_16483.strict_args_tab);
                 erasable_types_tab = (uu___494_16483.erasable_types_tab)
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
        (let uu___501_16526 = e  in
         {
           solver = (uu___501_16526.solver);
           range = r;
           curmodule = (uu___501_16526.curmodule);
           gamma = (uu___501_16526.gamma);
           gamma_sig = (uu___501_16526.gamma_sig);
           gamma_cache = (uu___501_16526.gamma_cache);
           modules = (uu___501_16526.modules);
           expected_typ = (uu___501_16526.expected_typ);
           sigtab = (uu___501_16526.sigtab);
           attrtab = (uu___501_16526.attrtab);
           instantiate_imp = (uu___501_16526.instantiate_imp);
           effects = (uu___501_16526.effects);
           generalize = (uu___501_16526.generalize);
           letrecs = (uu___501_16526.letrecs);
           top_level = (uu___501_16526.top_level);
           check_uvars = (uu___501_16526.check_uvars);
           use_eq = (uu___501_16526.use_eq);
           use_eq_strict = (uu___501_16526.use_eq_strict);
           is_iface = (uu___501_16526.is_iface);
           admit = (uu___501_16526.admit);
           lax = (uu___501_16526.lax);
           lax_universes = (uu___501_16526.lax_universes);
           phase1 = (uu___501_16526.phase1);
           failhard = (uu___501_16526.failhard);
           nosynth = (uu___501_16526.nosynth);
           uvar_subtyping = (uu___501_16526.uvar_subtyping);
           tc_term = (uu___501_16526.tc_term);
           type_of = (uu___501_16526.type_of);
           universe_of = (uu___501_16526.universe_of);
           check_type_of = (uu___501_16526.check_type_of);
           use_bv_sorts = (uu___501_16526.use_bv_sorts);
           qtbl_name_and_index = (uu___501_16526.qtbl_name_and_index);
           normalized_eff_names = (uu___501_16526.normalized_eff_names);
           fv_delta_depths = (uu___501_16526.fv_delta_depths);
           proof_ns = (uu___501_16526.proof_ns);
           synth_hook = (uu___501_16526.synth_hook);
           try_solve_implicits_hook =
             (uu___501_16526.try_solve_implicits_hook);
           splice = (uu___501_16526.splice);
           mpreprocess = (uu___501_16526.mpreprocess);
           postprocess = (uu___501_16526.postprocess);
           is_native_tactic = (uu___501_16526.is_native_tactic);
           identifier_info = (uu___501_16526.identifier_info);
           tc_hooks = (uu___501_16526.tc_hooks);
           dsenv = (uu___501_16526.dsenv);
           nbe = (uu___501_16526.nbe);
           strict_args_tab = (uu___501_16526.strict_args_tab);
           erasable_types_tab = (uu___501_16526.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16546 =
        let uu____16547 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16547 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16546
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16602 =
          let uu____16603 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16603 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16602
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16658 =
          let uu____16659 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16659 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16658
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16714 =
        let uu____16715 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16715 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16714
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___518_16779 = env  in
      {
        solver = (uu___518_16779.solver);
        range = (uu___518_16779.range);
        curmodule = lid;
        gamma = (uu___518_16779.gamma);
        gamma_sig = (uu___518_16779.gamma_sig);
        gamma_cache = (uu___518_16779.gamma_cache);
        modules = (uu___518_16779.modules);
        expected_typ = (uu___518_16779.expected_typ);
        sigtab = (uu___518_16779.sigtab);
        attrtab = (uu___518_16779.attrtab);
        instantiate_imp = (uu___518_16779.instantiate_imp);
        effects = (uu___518_16779.effects);
        generalize = (uu___518_16779.generalize);
        letrecs = (uu___518_16779.letrecs);
        top_level = (uu___518_16779.top_level);
        check_uvars = (uu___518_16779.check_uvars);
        use_eq = (uu___518_16779.use_eq);
        use_eq_strict = (uu___518_16779.use_eq_strict);
        is_iface = (uu___518_16779.is_iface);
        admit = (uu___518_16779.admit);
        lax = (uu___518_16779.lax);
        lax_universes = (uu___518_16779.lax_universes);
        phase1 = (uu___518_16779.phase1);
        failhard = (uu___518_16779.failhard);
        nosynth = (uu___518_16779.nosynth);
        uvar_subtyping = (uu___518_16779.uvar_subtyping);
        tc_term = (uu___518_16779.tc_term);
        type_of = (uu___518_16779.type_of);
        universe_of = (uu___518_16779.universe_of);
        check_type_of = (uu___518_16779.check_type_of);
        use_bv_sorts = (uu___518_16779.use_bv_sorts);
        qtbl_name_and_index = (uu___518_16779.qtbl_name_and_index);
        normalized_eff_names = (uu___518_16779.normalized_eff_names);
        fv_delta_depths = (uu___518_16779.fv_delta_depths);
        proof_ns = (uu___518_16779.proof_ns);
        synth_hook = (uu___518_16779.synth_hook);
        try_solve_implicits_hook = (uu___518_16779.try_solve_implicits_hook);
        splice = (uu___518_16779.splice);
        mpreprocess = (uu___518_16779.mpreprocess);
        postprocess = (uu___518_16779.postprocess);
        is_native_tactic = (uu___518_16779.is_native_tactic);
        identifier_info = (uu___518_16779.identifier_info);
        tc_hooks = (uu___518_16779.tc_hooks);
        dsenv = (uu___518_16779.dsenv);
        nbe = (uu___518_16779.nbe);
        strict_args_tab = (uu___518_16779.strict_args_tab);
        erasable_types_tab = (uu___518_16779.erasable_types_tab)
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
      let uu____16810 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16810
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16823 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16823)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16838 =
      let uu____16840 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16840  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16838)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16849  ->
    let uu____16850 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16850
  
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
      | ((formals,t),uu____16950) ->
          let vs = mk_univ_subst formals us  in
          let uu____16974 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16974)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16991  ->
    match uu___1_16991 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17017  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17037 = inst_tscheme t  in
      match uu____17037 with
      | (us,t1) ->
          let uu____17048 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17048)
  
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
          let uu____17073 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17075 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17073 uu____17075
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
        fun uu____17102  ->
          match uu____17102 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17116 =
                    let uu____17118 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17122 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17126 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17128 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17118 uu____17122 uu____17126 uu____17128
                     in
                  failwith uu____17116)
               else ();
               (let uu____17133 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17133))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17151 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17162 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17173 -> false
  
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
             | ([],uu____17221) -> Maybe
             | (uu____17228,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____17248 -> No  in
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
          let uu____17342 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____17342 with
          | FStar_Pervasives_Native.None  ->
              let uu____17365 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17409  ->
                     match uu___2_17409 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17448 = FStar_Ident.lid_equals lid l  in
                         if uu____17448
                         then
                           let uu____17471 =
                             let uu____17490 =
                               let uu____17505 = inst_tscheme t  in
                               FStar_Util.Inl uu____17505  in
                             let uu____17520 = FStar_Ident.range_of_lid l  in
                             (uu____17490, uu____17520)  in
                           FStar_Pervasives_Native.Some uu____17471
                         else FStar_Pervasives_Native.None
                     | uu____17573 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17365
                (fun uu____17611  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17621  ->
                        match uu___3_17621 with
                        | (uu____17624,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17626);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17627;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17628;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17629;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17630;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17631;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17653 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17653
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
                                  uu____17705 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17712 -> cache t  in
                            let uu____17713 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17713 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17719 =
                                   let uu____17720 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17720)
                                    in
                                 maybe_cache uu____17719)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17791 = find_in_sigtab env lid  in
         match uu____17791 with
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
      let uu____17872 = lookup_qname env lid  in
      match uu____17872 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17893,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____18007 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____18007 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18052 =
          let uu____18055 = lookup_attr env1 attr  in se1 :: uu____18055  in
        FStar_Util.smap_add (attrtab env1) attr uu____18052  in
      FStar_List.iter
        (fun attr  ->
           let uu____18065 =
             let uu____18066 = FStar_Syntax_Subst.compress attr  in
             uu____18066.FStar_Syntax_Syntax.n  in
           match uu____18065 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18070 =
                 let uu____18072 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18072.FStar_Ident.str  in
               add_one1 env se uu____18070
           | uu____18073 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18096) ->
          add_sigelts env ses
      | uu____18105 ->
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
        (fun uu___4_18143  ->
           match uu___4_18143 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18161 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18223,lb::[]),uu____18225) ->
            let uu____18234 =
              let uu____18243 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18252 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18243, uu____18252)  in
            FStar_Pervasives_Native.Some uu____18234
        | FStar_Syntax_Syntax.Sig_let ((uu____18265,lbs),uu____18267) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18299 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18312 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18312
                     then
                       let uu____18325 =
                         let uu____18334 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18343 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18334, uu____18343)  in
                       FStar_Pervasives_Native.Some uu____18325
                     else FStar_Pervasives_Native.None)
        | uu____18366 -> FStar_Pervasives_Native.None
  
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
                    let uu____18458 =
                      let uu____18460 =
                        let uu____18462 =
                          let uu____18464 =
                            let uu____18466 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18472 =
                              let uu____18474 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18474  in
                            Prims.op_Hat uu____18466 uu____18472  in
                          Prims.op_Hat ", expected " uu____18464  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18462
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18460
                       in
                    failwith uu____18458
                  else ());
             (let uu____18481 =
                let uu____18490 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18490, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18481))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18510,uu____18511) ->
            let uu____18516 =
              let uu____18525 =
                let uu____18530 =
                  let uu____18531 =
                    let uu____18534 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18534  in
                  (us, uu____18531)  in
                inst_ts us_opt uu____18530  in
              (uu____18525, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18516
        | uu____18553 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18642 =
          match uu____18642 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18738,uvs,t,uu____18741,uu____18742,uu____18743);
                      FStar_Syntax_Syntax.sigrng = uu____18744;
                      FStar_Syntax_Syntax.sigquals = uu____18745;
                      FStar_Syntax_Syntax.sigmeta = uu____18746;
                      FStar_Syntax_Syntax.sigattrs = uu____18747;
                      FStar_Syntax_Syntax.sigopts = uu____18748;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18773 =
                     let uu____18782 = inst_tscheme1 (uvs, t)  in
                     (uu____18782, rng)  in
                   FStar_Pervasives_Native.Some uu____18773
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18806;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18808;
                      FStar_Syntax_Syntax.sigattrs = uu____18809;
                      FStar_Syntax_Syntax.sigopts = uu____18810;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18829 =
                     let uu____18831 = in_cur_mod env l  in uu____18831 = Yes
                      in
                   if uu____18829
                   then
                     let uu____18843 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18843
                      then
                        let uu____18859 =
                          let uu____18868 = inst_tscheme1 (uvs, t)  in
                          (uu____18868, rng)  in
                        FStar_Pervasives_Native.Some uu____18859
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18901 =
                        let uu____18910 = inst_tscheme1 (uvs, t)  in
                        (uu____18910, rng)  in
                      FStar_Pervasives_Native.Some uu____18901)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18935,uu____18936);
                      FStar_Syntax_Syntax.sigrng = uu____18937;
                      FStar_Syntax_Syntax.sigquals = uu____18938;
                      FStar_Syntax_Syntax.sigmeta = uu____18939;
                      FStar_Syntax_Syntax.sigattrs = uu____18940;
                      FStar_Syntax_Syntax.sigopts = uu____18941;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18984 =
                          let uu____18993 = inst_tscheme1 (uvs, k)  in
                          (uu____18993, rng)  in
                        FStar_Pervasives_Native.Some uu____18984
                    | uu____19014 ->
                        let uu____19015 =
                          let uu____19024 =
                            let uu____19029 =
                              let uu____19030 =
                                let uu____19033 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19033
                                 in
                              (uvs, uu____19030)  in
                            inst_tscheme1 uu____19029  in
                          (uu____19024, rng)  in
                        FStar_Pervasives_Native.Some uu____19015)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19056,uu____19057);
                      FStar_Syntax_Syntax.sigrng = uu____19058;
                      FStar_Syntax_Syntax.sigquals = uu____19059;
                      FStar_Syntax_Syntax.sigmeta = uu____19060;
                      FStar_Syntax_Syntax.sigattrs = uu____19061;
                      FStar_Syntax_Syntax.sigopts = uu____19062;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19106 =
                          let uu____19115 = inst_tscheme_with (uvs, k) us  in
                          (uu____19115, rng)  in
                        FStar_Pervasives_Native.Some uu____19106
                    | uu____19136 ->
                        let uu____19137 =
                          let uu____19146 =
                            let uu____19151 =
                              let uu____19152 =
                                let uu____19155 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19155
                                 in
                              (uvs, uu____19152)  in
                            inst_tscheme_with uu____19151 us  in
                          (uu____19146, rng)  in
                        FStar_Pervasives_Native.Some uu____19137)
               | FStar_Util.Inr se ->
                   let uu____19191 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19212;
                          FStar_Syntax_Syntax.sigrng = uu____19213;
                          FStar_Syntax_Syntax.sigquals = uu____19214;
                          FStar_Syntax_Syntax.sigmeta = uu____19215;
                          FStar_Syntax_Syntax.sigattrs = uu____19216;
                          FStar_Syntax_Syntax.sigopts = uu____19217;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19234 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19191
                     (FStar_Util.map_option
                        (fun uu____19282  ->
                           match uu____19282 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19313 =
          let uu____19324 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19324 mapper  in
        match uu____19313 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19398 =
              let uu____19409 =
                let uu____19416 =
                  let uu___855_19419 = t  in
                  let uu____19420 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_19419.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19420;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_19419.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19416)  in
              (uu____19409, r)  in
            FStar_Pervasives_Native.Some uu____19398
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19469 = lookup_qname env l  in
      match uu____19469 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19490 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19544 = try_lookup_bv env bv  in
      match uu____19544 with
      | FStar_Pervasives_Native.None  ->
          let uu____19559 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19559 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19575 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19576 =
            let uu____19577 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19577  in
          (uu____19575, uu____19576)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19599 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19599 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19665 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19665  in
          let uu____19666 =
            let uu____19675 =
              let uu____19680 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19680)  in
            (uu____19675, r1)  in
          FStar_Pervasives_Native.Some uu____19666
  
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
        let uu____19715 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19715 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19748,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19773 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19773  in
            let uu____19774 =
              let uu____19779 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19779, r1)  in
            FStar_Pervasives_Native.Some uu____19774
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19803 = try_lookup_lid env l  in
      match uu____19803 with
      | FStar_Pervasives_Native.None  ->
          let uu____19830 = name_not_found l  in
          let uu____19836 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19830 uu____19836
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19879  ->
              match uu___5_19879 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19883 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19904 = lookup_qname env lid  in
      match uu____19904 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19913,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19916;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19918;
              FStar_Syntax_Syntax.sigattrs = uu____19919;
              FStar_Syntax_Syntax.sigopts = uu____19920;_},FStar_Pervasives_Native.None
            ),uu____19921)
          ->
          let uu____19972 =
            let uu____19979 =
              let uu____19980 =
                let uu____19983 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19983 t  in
              (uvs, uu____19980)  in
            (uu____19979, q)  in
          FStar_Pervasives_Native.Some uu____19972
      | uu____19996 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20018 = lookup_qname env lid  in
      match uu____20018 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20023,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20026;
              FStar_Syntax_Syntax.sigquals = uu____20027;
              FStar_Syntax_Syntax.sigmeta = uu____20028;
              FStar_Syntax_Syntax.sigattrs = uu____20029;
              FStar_Syntax_Syntax.sigopts = uu____20030;_},FStar_Pervasives_Native.None
            ),uu____20031)
          ->
          let uu____20082 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20082 (uvs, t)
      | uu____20087 ->
          let uu____20088 = name_not_found lid  in
          let uu____20094 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20088 uu____20094
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20114 = lookup_qname env lid  in
      match uu____20114 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20119,uvs,t,uu____20122,uu____20123,uu____20124);
              FStar_Syntax_Syntax.sigrng = uu____20125;
              FStar_Syntax_Syntax.sigquals = uu____20126;
              FStar_Syntax_Syntax.sigmeta = uu____20127;
              FStar_Syntax_Syntax.sigattrs = uu____20128;
              FStar_Syntax_Syntax.sigopts = uu____20129;_},FStar_Pervasives_Native.None
            ),uu____20130)
          ->
          let uu____20187 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20187 (uvs, t)
      | uu____20192 ->
          let uu____20193 = name_not_found lid  in
          let uu____20199 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20193 uu____20199
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20222 = lookup_qname env lid  in
      match uu____20222 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20230,uu____20231,uu____20232,uu____20233,uu____20234,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20236;
              FStar_Syntax_Syntax.sigquals = uu____20237;
              FStar_Syntax_Syntax.sigmeta = uu____20238;
              FStar_Syntax_Syntax.sigattrs = uu____20239;
              FStar_Syntax_Syntax.sigopts = uu____20240;_},uu____20241),uu____20242)
          -> (true, dcs)
      | uu____20307 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20323 = lookup_qname env lid  in
      match uu____20323 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20324,uu____20325,uu____20326,l,uu____20328,uu____20329);
              FStar_Syntax_Syntax.sigrng = uu____20330;
              FStar_Syntax_Syntax.sigquals = uu____20331;
              FStar_Syntax_Syntax.sigmeta = uu____20332;
              FStar_Syntax_Syntax.sigattrs = uu____20333;
              FStar_Syntax_Syntax.sigopts = uu____20334;_},uu____20335),uu____20336)
          -> l
      | uu____20395 ->
          let uu____20396 =
            let uu____20398 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20398  in
          failwith uu____20396
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20468)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20525) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20549 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20549
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20584 -> FStar_Pervasives_Native.None)
          | uu____20593 -> FStar_Pervasives_Native.None
  
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
        let uu____20655 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20655
  
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
        let uu____20688 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20688
  
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
             (FStar_Util.Inl uu____20740,uu____20741) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20790),uu____20791) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20840 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20858 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20868 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20885 ->
                  let uu____20892 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20892
              | FStar_Syntax_Syntax.Sig_let ((uu____20893,lbs),uu____20895)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20911 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20911
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20918 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20934 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20944 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20945 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20952 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20953 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20954 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20967 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20968 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20996 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20996
           (fun d_opt  ->
              let uu____21009 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____21009
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21019 =
                   let uu____21022 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21022  in
                 match uu____21019 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21023 =
                       let uu____21025 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21025
                        in
                     failwith uu____21023
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21030 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21030
                       then
                         let uu____21033 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21035 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21037 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21033 uu____21035 uu____21037
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
        (FStar_Util.Inr (se,uu____21062),uu____21063) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21112 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21134),uu____21135) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21184 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21206 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21206
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21239 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21239 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21261 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21270 =
                        let uu____21271 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21271.FStar_Syntax_Syntax.n  in
                      match uu____21270 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21276 -> false))
               in
            (true, uu____21261)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21299 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21299
  
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
          let uu____21371 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21371.FStar_Ident.str  in
        let uu____21372 = FStar_Util.smap_try_find tab s  in
        match uu____21372 with
        | FStar_Pervasives_Native.None  ->
            let uu____21375 = f ()  in
            (match uu____21375 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21413 =
        let uu____21414 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21414 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21448 =
        let uu____21449 = FStar_Syntax_Util.unrefine t  in
        uu____21449.FStar_Syntax_Syntax.n  in
      match uu____21448 with
      | FStar_Syntax_Syntax.Tm_type uu____21453 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21457) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21483) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21488,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21510 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21543 =
        let attrs =
          let uu____21549 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21549  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21589 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21589)
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
      let uu____21634 = lookup_qname env ftv  in
      match uu____21634 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21638) ->
          let uu____21683 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21683 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21704,t),r) ->
               let uu____21719 =
                 let uu____21720 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21720 t  in
               FStar_Pervasives_Native.Some uu____21719)
      | uu____21721 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21733 = try_lookup_effect_lid env ftv  in
      match uu____21733 with
      | FStar_Pervasives_Native.None  ->
          let uu____21736 = name_not_found ftv  in
          let uu____21742 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21736 uu____21742
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
        let uu____21766 = lookup_qname env lid0  in
        match uu____21766 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21777);
                FStar_Syntax_Syntax.sigrng = uu____21778;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21780;
                FStar_Syntax_Syntax.sigattrs = uu____21781;
                FStar_Syntax_Syntax.sigopts = uu____21782;_},FStar_Pervasives_Native.None
              ),uu____21783)
            ->
            let lid1 =
              let uu____21839 =
                let uu____21840 = FStar_Ident.range_of_lid lid  in
                let uu____21841 =
                  let uu____21842 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21842  in
                FStar_Range.set_use_range uu____21840 uu____21841  in
              FStar_Ident.set_lid_range lid uu____21839  in
            let uu____21843 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21849  ->
                      match uu___6_21849 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21852 -> false))
               in
            if uu____21843
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21871 =
                      let uu____21873 =
                        let uu____21875 = get_range env  in
                        FStar_Range.string_of_range uu____21875  in
                      let uu____21876 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21878 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21873 uu____21876 uu____21878
                       in
                    failwith uu____21871)
                  in
               match (binders, univs1) with
               | ([],uu____21899) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21925,uu____21926::uu____21927::uu____21928) ->
                   let uu____21949 =
                     let uu____21951 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21953 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21951 uu____21953
                      in
                   failwith uu____21949
               | uu____21964 ->
                   let uu____21979 =
                     let uu____21984 =
                       let uu____21985 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21985)  in
                     inst_tscheme_with uu____21984 insts  in
                   (match uu____21979 with
                    | (uu____21998,t) ->
                        let t1 =
                          let uu____22001 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____22001 t  in
                        let uu____22002 =
                          let uu____22003 = FStar_Syntax_Subst.compress t1
                             in
                          uu____22003.FStar_Syntax_Syntax.n  in
                        (match uu____22002 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22038 -> failwith "Impossible")))
        | uu____22046 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22070 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22070 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22083,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22090 = find1 l2  in
            (match uu____22090 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22097 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22097 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22101 = find1 l  in
            (match uu____22101 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22106 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22106
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22127 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22127 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22133) ->
            FStar_List.length bs
        | uu____22172 ->
            let uu____22173 =
              let uu____22179 =
                let uu____22181 = FStar_Ident.string_of_lid name  in
                let uu____22183 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22181 uu____22183
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22179)
               in
            FStar_Errors.raise_error uu____22173 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22202 = lookup_qname env l1  in
      match uu____22202 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22205;
              FStar_Syntax_Syntax.sigrng = uu____22206;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22208;
              FStar_Syntax_Syntax.sigattrs = uu____22209;
              FStar_Syntax_Syntax.sigopts = uu____22210;_},uu____22211),uu____22212)
          -> q
      | uu____22265 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22289 =
          let uu____22290 =
            let uu____22292 = FStar_Util.string_of_int i  in
            let uu____22294 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22292 uu____22294
             in
          failwith uu____22290  in
        let uu____22297 = lookup_datacon env lid  in
        match uu____22297 with
        | (uu____22302,t) ->
            let uu____22304 =
              let uu____22305 = FStar_Syntax_Subst.compress t  in
              uu____22305.FStar_Syntax_Syntax.n  in
            (match uu____22304 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22309) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22355 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22369 = lookup_qname env l  in
      match uu____22369 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22371,uu____22372,uu____22373);
              FStar_Syntax_Syntax.sigrng = uu____22374;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22376;
              FStar_Syntax_Syntax.sigattrs = uu____22377;
              FStar_Syntax_Syntax.sigopts = uu____22378;_},uu____22379),uu____22380)
          ->
          FStar_Util.for_some
            (fun uu___7_22435  ->
               match uu___7_22435 with
               | FStar_Syntax_Syntax.Projector uu____22437 -> true
               | uu____22443 -> false) quals
      | uu____22445 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22459 = lookup_qname env lid  in
      match uu____22459 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22461,uu____22462,uu____22463,uu____22464,uu____22465,uu____22466);
              FStar_Syntax_Syntax.sigrng = uu____22467;
              FStar_Syntax_Syntax.sigquals = uu____22468;
              FStar_Syntax_Syntax.sigmeta = uu____22469;
              FStar_Syntax_Syntax.sigattrs = uu____22470;
              FStar_Syntax_Syntax.sigopts = uu____22471;_},uu____22472),uu____22473)
          -> true
      | uu____22533 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22547 = lookup_qname env lid  in
      match uu____22547 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22549,uu____22550,uu____22551,uu____22552,uu____22553,uu____22554);
              FStar_Syntax_Syntax.sigrng = uu____22555;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22557;
              FStar_Syntax_Syntax.sigattrs = uu____22558;
              FStar_Syntax_Syntax.sigopts = uu____22559;_},uu____22560),uu____22561)
          ->
          FStar_Util.for_some
            (fun uu___8_22624  ->
               match uu___8_22624 with
               | FStar_Syntax_Syntax.RecordType uu____22626 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22636 -> true
               | uu____22646 -> false) quals
      | uu____22648 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22658,uu____22659);
            FStar_Syntax_Syntax.sigrng = uu____22660;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22662;
            FStar_Syntax_Syntax.sigattrs = uu____22663;
            FStar_Syntax_Syntax.sigopts = uu____22664;_},uu____22665),uu____22666)
        ->
        FStar_Util.for_some
          (fun uu___9_22725  ->
             match uu___9_22725 with
             | FStar_Syntax_Syntax.Action uu____22727 -> true
             | uu____22729 -> false) quals
    | uu____22731 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22745 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22745
  
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
      let uu____22762 =
        let uu____22763 = FStar_Syntax_Util.un_uinst head1  in
        uu____22763.FStar_Syntax_Syntax.n  in
      match uu____22762 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22769 ->
               true
           | uu____22772 -> false)
      | uu____22774 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22788 = lookup_qname env l  in
      match uu____22788 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22791),uu____22792) ->
          FStar_Util.for_some
            (fun uu___10_22840  ->
               match uu___10_22840 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22843 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22845 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22921 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22939) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22957 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22965 ->
                 FStar_Pervasives_Native.Some true
             | uu____22984 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22987 =
        let uu____22991 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22991 mapper  in
      match uu____22987 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23051 = lookup_qname env lid  in
      match uu____23051 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23055,uu____23056,tps,uu____23058,uu____23059,uu____23060);
              FStar_Syntax_Syntax.sigrng = uu____23061;
              FStar_Syntax_Syntax.sigquals = uu____23062;
              FStar_Syntax_Syntax.sigmeta = uu____23063;
              FStar_Syntax_Syntax.sigattrs = uu____23064;
              FStar_Syntax_Syntax.sigopts = uu____23065;_},uu____23066),uu____23067)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23135 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23181  ->
              match uu____23181 with
              | (d,uu____23190) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23206 = effect_decl_opt env l  in
      match uu____23206 with
      | FStar_Pervasives_Native.None  ->
          let uu____23221 = name_not_found l  in
          let uu____23227 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23221 uu____23227
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23255 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23255 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23262  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23276  ->
            fun uu____23277  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23311 = FStar_Ident.lid_equals l1 l2  in
        if uu____23311
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23330 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23330
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23349 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23402  ->
                        match uu____23402 with
                        | (m1,m2,uu____23416,uu____23417,uu____23418) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23349 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23443,uu____23444,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23492 = join_opt env l1 l2  in
        match uu____23492 with
        | FStar_Pervasives_Native.None  ->
            let uu____23513 =
              let uu____23519 =
                let uu____23521 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23523 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23521 uu____23523
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23519)  in
            FStar_Errors.raise_error uu____23513 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23566 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23566
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
  'Auu____23586 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23586) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23615 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23641  ->
                match uu____23641 with
                | (d,uu____23648) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23615 with
      | FStar_Pervasives_Native.None  ->
          let uu____23659 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23659
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23674 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23674 with
           | (uu____23685,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23703)::(wp,uu____23705)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23761 -> failwith "Impossible"))
  
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
        | uu____23826 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23839 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23839 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23856 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23856 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23881 =
                     let uu____23887 =
                       let uu____23889 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23897 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23908 =
                         let uu____23910 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23910  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23889 uu____23897 uu____23908
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23887)
                      in
                   FStar_Errors.raise_error uu____23881
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23918 =
                     let uu____23929 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23929 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23966  ->
                        fun uu____23967  ->
                          match (uu____23966, uu____23967) with
                          | ((x,uu____23997),(t,uu____23999)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23918
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____24030 =
                     let uu___1611_24031 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1611_24031.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1611_24031.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1611_24031.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1611_24031.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24030
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24043 .
    'Auu____24043 ->
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
            let uu____24084 =
              let uu____24091 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24091)  in
            match uu____24084 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24115 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24117 = FStar_Util.string_of_int given  in
                     let uu____24119 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24115 uu____24117 uu____24119
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24124 = effect_decl_opt env effect_name  in
          match uu____24124 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24146) ->
              let uu____24157 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24157 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24175 =
                       let uu____24178 = get_range env  in
                       let uu____24179 =
                         let uu____24186 =
                           let uu____24187 =
                             let uu____24204 =
                               let uu____24215 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24215 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24204)  in
                           FStar_Syntax_Syntax.Tm_app uu____24187  in
                         FStar_Syntax_Syntax.mk uu____24186  in
                       uu____24179 FStar_Pervasives_Native.None uu____24178
                        in
                     FStar_Pervasives_Native.Some uu____24175)))
  
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
           (fun uu___11_24315  ->
              match uu___11_24315 with
              | FStar_Syntax_Syntax.Reflectable uu____24317 -> true
              | uu____24319 -> false))
  
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
      | uu____24379 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24394 =
        let uu____24395 = FStar_Syntax_Subst.compress t  in
        uu____24395.FStar_Syntax_Syntax.n  in
      match uu____24394 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24399,c) ->
          is_reifiable_comp env c
      | uu____24421 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24441 =
           let uu____24443 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24443  in
         if uu____24441
         then
           let uu____24446 =
             let uu____24452 =
               let uu____24454 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24454
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24452)  in
           let uu____24458 = get_range env  in
           FStar_Errors.raise_error uu____24446 uu____24458
         else ());
        (let uu____24461 = effect_repr_aux true env c u_c  in
         match uu____24461 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1688_24497 = env  in
        {
          solver = (uu___1688_24497.solver);
          range = (uu___1688_24497.range);
          curmodule = (uu___1688_24497.curmodule);
          gamma = (uu___1688_24497.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1688_24497.gamma_cache);
          modules = (uu___1688_24497.modules);
          expected_typ = (uu___1688_24497.expected_typ);
          sigtab = (uu___1688_24497.sigtab);
          attrtab = (uu___1688_24497.attrtab);
          instantiate_imp = (uu___1688_24497.instantiate_imp);
          effects = (uu___1688_24497.effects);
          generalize = (uu___1688_24497.generalize);
          letrecs = (uu___1688_24497.letrecs);
          top_level = (uu___1688_24497.top_level);
          check_uvars = (uu___1688_24497.check_uvars);
          use_eq = (uu___1688_24497.use_eq);
          use_eq_strict = (uu___1688_24497.use_eq_strict);
          is_iface = (uu___1688_24497.is_iface);
          admit = (uu___1688_24497.admit);
          lax = (uu___1688_24497.lax);
          lax_universes = (uu___1688_24497.lax_universes);
          phase1 = (uu___1688_24497.phase1);
          failhard = (uu___1688_24497.failhard);
          nosynth = (uu___1688_24497.nosynth);
          uvar_subtyping = (uu___1688_24497.uvar_subtyping);
          tc_term = (uu___1688_24497.tc_term);
          type_of = (uu___1688_24497.type_of);
          universe_of = (uu___1688_24497.universe_of);
          check_type_of = (uu___1688_24497.check_type_of);
          use_bv_sorts = (uu___1688_24497.use_bv_sorts);
          qtbl_name_and_index = (uu___1688_24497.qtbl_name_and_index);
          normalized_eff_names = (uu___1688_24497.normalized_eff_names);
          fv_delta_depths = (uu___1688_24497.fv_delta_depths);
          proof_ns = (uu___1688_24497.proof_ns);
          synth_hook = (uu___1688_24497.synth_hook);
          try_solve_implicits_hook =
            (uu___1688_24497.try_solve_implicits_hook);
          splice = (uu___1688_24497.splice);
          mpreprocess = (uu___1688_24497.mpreprocess);
          postprocess = (uu___1688_24497.postprocess);
          is_native_tactic = (uu___1688_24497.is_native_tactic);
          identifier_info = (uu___1688_24497.identifier_info);
          tc_hooks = (uu___1688_24497.tc_hooks);
          dsenv = (uu___1688_24497.dsenv);
          nbe = (uu___1688_24497.nbe);
          strict_args_tab = (uu___1688_24497.strict_args_tab);
          erasable_types_tab = (uu___1688_24497.erasable_types_tab)
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
    fun uu____24516  ->
      match uu____24516 with
      | (ed,quals) ->
          let effects =
            let uu___1697_24530 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1697_24530.order);
              joins = (uu___1697_24530.joins);
              polymonadic_binds = (uu___1697_24530.polymonadic_binds)
            }  in
          let uu___1700_24539 = env  in
          {
            solver = (uu___1700_24539.solver);
            range = (uu___1700_24539.range);
            curmodule = (uu___1700_24539.curmodule);
            gamma = (uu___1700_24539.gamma);
            gamma_sig = (uu___1700_24539.gamma_sig);
            gamma_cache = (uu___1700_24539.gamma_cache);
            modules = (uu___1700_24539.modules);
            expected_typ = (uu___1700_24539.expected_typ);
            sigtab = (uu___1700_24539.sigtab);
            attrtab = (uu___1700_24539.attrtab);
            instantiate_imp = (uu___1700_24539.instantiate_imp);
            effects;
            generalize = (uu___1700_24539.generalize);
            letrecs = (uu___1700_24539.letrecs);
            top_level = (uu___1700_24539.top_level);
            check_uvars = (uu___1700_24539.check_uvars);
            use_eq = (uu___1700_24539.use_eq);
            use_eq_strict = (uu___1700_24539.use_eq_strict);
            is_iface = (uu___1700_24539.is_iface);
            admit = (uu___1700_24539.admit);
            lax = (uu___1700_24539.lax);
            lax_universes = (uu___1700_24539.lax_universes);
            phase1 = (uu___1700_24539.phase1);
            failhard = (uu___1700_24539.failhard);
            nosynth = (uu___1700_24539.nosynth);
            uvar_subtyping = (uu___1700_24539.uvar_subtyping);
            tc_term = (uu___1700_24539.tc_term);
            type_of = (uu___1700_24539.type_of);
            universe_of = (uu___1700_24539.universe_of);
            check_type_of = (uu___1700_24539.check_type_of);
            use_bv_sorts = (uu___1700_24539.use_bv_sorts);
            qtbl_name_and_index = (uu___1700_24539.qtbl_name_and_index);
            normalized_eff_names = (uu___1700_24539.normalized_eff_names);
            fv_delta_depths = (uu___1700_24539.fv_delta_depths);
            proof_ns = (uu___1700_24539.proof_ns);
            synth_hook = (uu___1700_24539.synth_hook);
            try_solve_implicits_hook =
              (uu___1700_24539.try_solve_implicits_hook);
            splice = (uu___1700_24539.splice);
            mpreprocess = (uu___1700_24539.mpreprocess);
            postprocess = (uu___1700_24539.postprocess);
            is_native_tactic = (uu___1700_24539.is_native_tactic);
            identifier_info = (uu___1700_24539.identifier_info);
            tc_hooks = (uu___1700_24539.tc_hooks);
            dsenv = (uu___1700_24539.dsenv);
            nbe = (uu___1700_24539.nbe);
            strict_args_tab = (uu___1700_24539.strict_args_tab);
            erasable_types_tab = (uu___1700_24539.erasable_types_tab)
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
        let uu____24568 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24636  ->
                  match uu____24636 with
                  | (m1,n11,uu____24654,uu____24655) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24568 with
        | FStar_Pervasives_Native.Some (uu____24680,uu____24681,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24726 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24801 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24801
                  (fun uu____24822  ->
                     match uu____24822 with
                     | (c1,g1) ->
                         let uu____24833 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24833
                           (fun uu____24854  ->
                              match uu____24854 with
                              | (c2,g2) ->
                                  let uu____24865 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24865)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24987 = l1 u t e  in
                              l2 u t uu____24987))
                | uu____24988 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25056  ->
                    match uu____25056 with
                    | (e,uu____25064) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25087 =
            match uu____25087 with
            | (i,j) ->
                let uu____25098 = FStar_Ident.lid_equals i j  in
                if uu____25098
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25105  -> FStar_Pervasives_Native.Some _25105)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25134 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25144 = FStar_Ident.lid_equals i k  in
                        if uu____25144
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25158 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25158
                                  then []
                                  else
                                    (let uu____25165 =
                                       let uu____25174 =
                                         find_edge order1 (i, k)  in
                                       let uu____25177 =
                                         find_edge order1 (k, j)  in
                                       (uu____25174, uu____25177)  in
                                     match uu____25165 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25192 =
                                           compose_edges e1 e2  in
                                         [uu____25192]
                                     | uu____25193 -> [])))))
                 in
              FStar_List.append order1 uu____25134  in
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
                  let uu____25223 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25226 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25226
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25223
                  then
                    let uu____25233 =
                      let uu____25239 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25239)
                       in
                    let uu____25243 = get_range env  in
                    FStar_Errors.raise_error uu____25233 uu____25243
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25321 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25321
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25373 =
                                             let uu____25382 =
                                               find_edge order2 (i, k)  in
                                             let uu____25385 =
                                               find_edge order2 (j, k)  in
                                             (uu____25382, uu____25385)  in
                                           match uu____25373 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25427,uu____25428)
                                                    ->
                                                    let uu____25435 =
                                                      let uu____25442 =
                                                        let uu____25444 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25444
                                                         in
                                                      let uu____25447 =
                                                        let uu____25449 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25449
                                                         in
                                                      (uu____25442,
                                                        uu____25447)
                                                       in
                                                    (match uu____25435 with
                                                     | (true ,true ) ->
                                                         let uu____25466 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25466
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
                                           | uu____25509 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25561 =
                                   let uu____25563 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25563
                                     FStar_Util.is_some
                                    in
                                 if uu____25561
                                 then
                                   let uu____25612 =
                                     let uu____25618 =
                                       let uu____25620 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25622 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25624 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25626 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25620 uu____25622 uu____25624
                                         uu____25626
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25618)
                                      in
                                   FStar_Errors.raise_error uu____25612
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1821_25665 = env.effects  in
             {
               decls = (uu___1821_25665.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1821_25665.polymonadic_binds)
             }  in
           let uu___1824_25666 = env  in
           {
             solver = (uu___1824_25666.solver);
             range = (uu___1824_25666.range);
             curmodule = (uu___1824_25666.curmodule);
             gamma = (uu___1824_25666.gamma);
             gamma_sig = (uu___1824_25666.gamma_sig);
             gamma_cache = (uu___1824_25666.gamma_cache);
             modules = (uu___1824_25666.modules);
             expected_typ = (uu___1824_25666.expected_typ);
             sigtab = (uu___1824_25666.sigtab);
             attrtab = (uu___1824_25666.attrtab);
             instantiate_imp = (uu___1824_25666.instantiate_imp);
             effects;
             generalize = (uu___1824_25666.generalize);
             letrecs = (uu___1824_25666.letrecs);
             top_level = (uu___1824_25666.top_level);
             check_uvars = (uu___1824_25666.check_uvars);
             use_eq = (uu___1824_25666.use_eq);
             use_eq_strict = (uu___1824_25666.use_eq_strict);
             is_iface = (uu___1824_25666.is_iface);
             admit = (uu___1824_25666.admit);
             lax = (uu___1824_25666.lax);
             lax_universes = (uu___1824_25666.lax_universes);
             phase1 = (uu___1824_25666.phase1);
             failhard = (uu___1824_25666.failhard);
             nosynth = (uu___1824_25666.nosynth);
             uvar_subtyping = (uu___1824_25666.uvar_subtyping);
             tc_term = (uu___1824_25666.tc_term);
             type_of = (uu___1824_25666.type_of);
             universe_of = (uu___1824_25666.universe_of);
             check_type_of = (uu___1824_25666.check_type_of);
             use_bv_sorts = (uu___1824_25666.use_bv_sorts);
             qtbl_name_and_index = (uu___1824_25666.qtbl_name_and_index);
             normalized_eff_names = (uu___1824_25666.normalized_eff_names);
             fv_delta_depths = (uu___1824_25666.fv_delta_depths);
             proof_ns = (uu___1824_25666.proof_ns);
             synth_hook = (uu___1824_25666.synth_hook);
             try_solve_implicits_hook =
               (uu___1824_25666.try_solve_implicits_hook);
             splice = (uu___1824_25666.splice);
             mpreprocess = (uu___1824_25666.mpreprocess);
             postprocess = (uu___1824_25666.postprocess);
             is_native_tactic = (uu___1824_25666.is_native_tactic);
             identifier_info = (uu___1824_25666.identifier_info);
             tc_hooks = (uu___1824_25666.tc_hooks);
             dsenv = (uu___1824_25666.dsenv);
             nbe = (uu___1824_25666.nbe);
             strict_args_tab = (uu___1824_25666.strict_args_tab);
             erasable_types_tab = (uu___1824_25666.erasable_types_tab)
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
              let uu____25714 = FStar_Ident.string_of_lid m  in
              let uu____25716 = FStar_Ident.string_of_lid n1  in
              let uu____25718 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25714 uu____25716 uu____25718
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25727 =
              let uu____25729 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25729 FStar_Util.is_some  in
            if uu____25727
            then
              let uu____25766 =
                let uu____25772 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25772)
                 in
              FStar_Errors.raise_error uu____25766 env.range
            else
              (let uu____25778 =
                 let uu____25780 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25780 FStar_Util.is_some  in
               if uu____25778
               then
                 let uu____25805 =
                   let uu____25811 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25811)
                    in
                 FStar_Errors.raise_error uu____25805 env.range
               else
                 (let uu___1839_25817 = env  in
                  {
                    solver = (uu___1839_25817.solver);
                    range = (uu___1839_25817.range);
                    curmodule = (uu___1839_25817.curmodule);
                    gamma = (uu___1839_25817.gamma);
                    gamma_sig = (uu___1839_25817.gamma_sig);
                    gamma_cache = (uu___1839_25817.gamma_cache);
                    modules = (uu___1839_25817.modules);
                    expected_typ = (uu___1839_25817.expected_typ);
                    sigtab = (uu___1839_25817.sigtab);
                    attrtab = (uu___1839_25817.attrtab);
                    instantiate_imp = (uu___1839_25817.instantiate_imp);
                    effects =
                      (let uu___1841_25819 = env.effects  in
                       {
                         decls = (uu___1841_25819.decls);
                         order = (uu___1841_25819.order);
                         joins = (uu___1841_25819.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1839_25817.generalize);
                    letrecs = (uu___1839_25817.letrecs);
                    top_level = (uu___1839_25817.top_level);
                    check_uvars = (uu___1839_25817.check_uvars);
                    use_eq = (uu___1839_25817.use_eq);
                    use_eq_strict = (uu___1839_25817.use_eq_strict);
                    is_iface = (uu___1839_25817.is_iface);
                    admit = (uu___1839_25817.admit);
                    lax = (uu___1839_25817.lax);
                    lax_universes = (uu___1839_25817.lax_universes);
                    phase1 = (uu___1839_25817.phase1);
                    failhard = (uu___1839_25817.failhard);
                    nosynth = (uu___1839_25817.nosynth);
                    uvar_subtyping = (uu___1839_25817.uvar_subtyping);
                    tc_term = (uu___1839_25817.tc_term);
                    type_of = (uu___1839_25817.type_of);
                    universe_of = (uu___1839_25817.universe_of);
                    check_type_of = (uu___1839_25817.check_type_of);
                    use_bv_sorts = (uu___1839_25817.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1839_25817.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1839_25817.normalized_eff_names);
                    fv_delta_depths = (uu___1839_25817.fv_delta_depths);
                    proof_ns = (uu___1839_25817.proof_ns);
                    synth_hook = (uu___1839_25817.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1839_25817.try_solve_implicits_hook);
                    splice = (uu___1839_25817.splice);
                    mpreprocess = (uu___1839_25817.mpreprocess);
                    postprocess = (uu___1839_25817.postprocess);
                    is_native_tactic = (uu___1839_25817.is_native_tactic);
                    identifier_info = (uu___1839_25817.identifier_info);
                    tc_hooks = (uu___1839_25817.tc_hooks);
                    dsenv = (uu___1839_25817.dsenv);
                    nbe = (uu___1839_25817.nbe);
                    strict_args_tab = (uu___1839_25817.strict_args_tab);
                    erasable_types_tab = (uu___1839_25817.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1845_25891 = env  in
      {
        solver = (uu___1845_25891.solver);
        range = (uu___1845_25891.range);
        curmodule = (uu___1845_25891.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1845_25891.gamma_sig);
        gamma_cache = (uu___1845_25891.gamma_cache);
        modules = (uu___1845_25891.modules);
        expected_typ = (uu___1845_25891.expected_typ);
        sigtab = (uu___1845_25891.sigtab);
        attrtab = (uu___1845_25891.attrtab);
        instantiate_imp = (uu___1845_25891.instantiate_imp);
        effects = (uu___1845_25891.effects);
        generalize = (uu___1845_25891.generalize);
        letrecs = (uu___1845_25891.letrecs);
        top_level = (uu___1845_25891.top_level);
        check_uvars = (uu___1845_25891.check_uvars);
        use_eq = (uu___1845_25891.use_eq);
        use_eq_strict = (uu___1845_25891.use_eq_strict);
        is_iface = (uu___1845_25891.is_iface);
        admit = (uu___1845_25891.admit);
        lax = (uu___1845_25891.lax);
        lax_universes = (uu___1845_25891.lax_universes);
        phase1 = (uu___1845_25891.phase1);
        failhard = (uu___1845_25891.failhard);
        nosynth = (uu___1845_25891.nosynth);
        uvar_subtyping = (uu___1845_25891.uvar_subtyping);
        tc_term = (uu___1845_25891.tc_term);
        type_of = (uu___1845_25891.type_of);
        universe_of = (uu___1845_25891.universe_of);
        check_type_of = (uu___1845_25891.check_type_of);
        use_bv_sorts = (uu___1845_25891.use_bv_sorts);
        qtbl_name_and_index = (uu___1845_25891.qtbl_name_and_index);
        normalized_eff_names = (uu___1845_25891.normalized_eff_names);
        fv_delta_depths = (uu___1845_25891.fv_delta_depths);
        proof_ns = (uu___1845_25891.proof_ns);
        synth_hook = (uu___1845_25891.synth_hook);
        try_solve_implicits_hook = (uu___1845_25891.try_solve_implicits_hook);
        splice = (uu___1845_25891.splice);
        mpreprocess = (uu___1845_25891.mpreprocess);
        postprocess = (uu___1845_25891.postprocess);
        is_native_tactic = (uu___1845_25891.is_native_tactic);
        identifier_info = (uu___1845_25891.identifier_info);
        tc_hooks = (uu___1845_25891.tc_hooks);
        dsenv = (uu___1845_25891.dsenv);
        nbe = (uu___1845_25891.nbe);
        strict_args_tab = (uu___1845_25891.strict_args_tab);
        erasable_types_tab = (uu___1845_25891.erasable_types_tab)
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
            (let uu___1858_25949 = env  in
             {
               solver = (uu___1858_25949.solver);
               range = (uu___1858_25949.range);
               curmodule = (uu___1858_25949.curmodule);
               gamma = rest;
               gamma_sig = (uu___1858_25949.gamma_sig);
               gamma_cache = (uu___1858_25949.gamma_cache);
               modules = (uu___1858_25949.modules);
               expected_typ = (uu___1858_25949.expected_typ);
               sigtab = (uu___1858_25949.sigtab);
               attrtab = (uu___1858_25949.attrtab);
               instantiate_imp = (uu___1858_25949.instantiate_imp);
               effects = (uu___1858_25949.effects);
               generalize = (uu___1858_25949.generalize);
               letrecs = (uu___1858_25949.letrecs);
               top_level = (uu___1858_25949.top_level);
               check_uvars = (uu___1858_25949.check_uvars);
               use_eq = (uu___1858_25949.use_eq);
               use_eq_strict = (uu___1858_25949.use_eq_strict);
               is_iface = (uu___1858_25949.is_iface);
               admit = (uu___1858_25949.admit);
               lax = (uu___1858_25949.lax);
               lax_universes = (uu___1858_25949.lax_universes);
               phase1 = (uu___1858_25949.phase1);
               failhard = (uu___1858_25949.failhard);
               nosynth = (uu___1858_25949.nosynth);
               uvar_subtyping = (uu___1858_25949.uvar_subtyping);
               tc_term = (uu___1858_25949.tc_term);
               type_of = (uu___1858_25949.type_of);
               universe_of = (uu___1858_25949.universe_of);
               check_type_of = (uu___1858_25949.check_type_of);
               use_bv_sorts = (uu___1858_25949.use_bv_sorts);
               qtbl_name_and_index = (uu___1858_25949.qtbl_name_and_index);
               normalized_eff_names = (uu___1858_25949.normalized_eff_names);
               fv_delta_depths = (uu___1858_25949.fv_delta_depths);
               proof_ns = (uu___1858_25949.proof_ns);
               synth_hook = (uu___1858_25949.synth_hook);
               try_solve_implicits_hook =
                 (uu___1858_25949.try_solve_implicits_hook);
               splice = (uu___1858_25949.splice);
               mpreprocess = (uu___1858_25949.mpreprocess);
               postprocess = (uu___1858_25949.postprocess);
               is_native_tactic = (uu___1858_25949.is_native_tactic);
               identifier_info = (uu___1858_25949.identifier_info);
               tc_hooks = (uu___1858_25949.tc_hooks);
               dsenv = (uu___1858_25949.dsenv);
               nbe = (uu___1858_25949.nbe);
               strict_args_tab = (uu___1858_25949.strict_args_tab);
               erasable_types_tab = (uu___1858_25949.erasable_types_tab)
             }))
    | uu____25950 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25979  ->
             match uu____25979 with | (x,uu____25987) -> push_bv env1 x) env
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
            let uu___1872_26022 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1872_26022.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1872_26022.FStar_Syntax_Syntax.index);
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
        let uu____26095 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26095 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26123 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26123)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1893_26139 = env  in
      {
        solver = (uu___1893_26139.solver);
        range = (uu___1893_26139.range);
        curmodule = (uu___1893_26139.curmodule);
        gamma = (uu___1893_26139.gamma);
        gamma_sig = (uu___1893_26139.gamma_sig);
        gamma_cache = (uu___1893_26139.gamma_cache);
        modules = (uu___1893_26139.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1893_26139.sigtab);
        attrtab = (uu___1893_26139.attrtab);
        instantiate_imp = (uu___1893_26139.instantiate_imp);
        effects = (uu___1893_26139.effects);
        generalize = (uu___1893_26139.generalize);
        letrecs = (uu___1893_26139.letrecs);
        top_level = (uu___1893_26139.top_level);
        check_uvars = (uu___1893_26139.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1893_26139.use_eq_strict);
        is_iface = (uu___1893_26139.is_iface);
        admit = (uu___1893_26139.admit);
        lax = (uu___1893_26139.lax);
        lax_universes = (uu___1893_26139.lax_universes);
        phase1 = (uu___1893_26139.phase1);
        failhard = (uu___1893_26139.failhard);
        nosynth = (uu___1893_26139.nosynth);
        uvar_subtyping = (uu___1893_26139.uvar_subtyping);
        tc_term = (uu___1893_26139.tc_term);
        type_of = (uu___1893_26139.type_of);
        universe_of = (uu___1893_26139.universe_of);
        check_type_of = (uu___1893_26139.check_type_of);
        use_bv_sorts = (uu___1893_26139.use_bv_sorts);
        qtbl_name_and_index = (uu___1893_26139.qtbl_name_and_index);
        normalized_eff_names = (uu___1893_26139.normalized_eff_names);
        fv_delta_depths = (uu___1893_26139.fv_delta_depths);
        proof_ns = (uu___1893_26139.proof_ns);
        synth_hook = (uu___1893_26139.synth_hook);
        try_solve_implicits_hook = (uu___1893_26139.try_solve_implicits_hook);
        splice = (uu___1893_26139.splice);
        mpreprocess = (uu___1893_26139.mpreprocess);
        postprocess = (uu___1893_26139.postprocess);
        is_native_tactic = (uu___1893_26139.is_native_tactic);
        identifier_info = (uu___1893_26139.identifier_info);
        tc_hooks = (uu___1893_26139.tc_hooks);
        dsenv = (uu___1893_26139.dsenv);
        nbe = (uu___1893_26139.nbe);
        strict_args_tab = (uu___1893_26139.strict_args_tab);
        erasable_types_tab = (uu___1893_26139.erasable_types_tab)
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
    let uu____26170 = expected_typ env_  in
    ((let uu___1900_26176 = env_  in
      {
        solver = (uu___1900_26176.solver);
        range = (uu___1900_26176.range);
        curmodule = (uu___1900_26176.curmodule);
        gamma = (uu___1900_26176.gamma);
        gamma_sig = (uu___1900_26176.gamma_sig);
        gamma_cache = (uu___1900_26176.gamma_cache);
        modules = (uu___1900_26176.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1900_26176.sigtab);
        attrtab = (uu___1900_26176.attrtab);
        instantiate_imp = (uu___1900_26176.instantiate_imp);
        effects = (uu___1900_26176.effects);
        generalize = (uu___1900_26176.generalize);
        letrecs = (uu___1900_26176.letrecs);
        top_level = (uu___1900_26176.top_level);
        check_uvars = (uu___1900_26176.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1900_26176.use_eq_strict);
        is_iface = (uu___1900_26176.is_iface);
        admit = (uu___1900_26176.admit);
        lax = (uu___1900_26176.lax);
        lax_universes = (uu___1900_26176.lax_universes);
        phase1 = (uu___1900_26176.phase1);
        failhard = (uu___1900_26176.failhard);
        nosynth = (uu___1900_26176.nosynth);
        uvar_subtyping = (uu___1900_26176.uvar_subtyping);
        tc_term = (uu___1900_26176.tc_term);
        type_of = (uu___1900_26176.type_of);
        universe_of = (uu___1900_26176.universe_of);
        check_type_of = (uu___1900_26176.check_type_of);
        use_bv_sorts = (uu___1900_26176.use_bv_sorts);
        qtbl_name_and_index = (uu___1900_26176.qtbl_name_and_index);
        normalized_eff_names = (uu___1900_26176.normalized_eff_names);
        fv_delta_depths = (uu___1900_26176.fv_delta_depths);
        proof_ns = (uu___1900_26176.proof_ns);
        synth_hook = (uu___1900_26176.synth_hook);
        try_solve_implicits_hook = (uu___1900_26176.try_solve_implicits_hook);
        splice = (uu___1900_26176.splice);
        mpreprocess = (uu___1900_26176.mpreprocess);
        postprocess = (uu___1900_26176.postprocess);
        is_native_tactic = (uu___1900_26176.is_native_tactic);
        identifier_info = (uu___1900_26176.identifier_info);
        tc_hooks = (uu___1900_26176.tc_hooks);
        dsenv = (uu___1900_26176.dsenv);
        nbe = (uu___1900_26176.nbe);
        strict_args_tab = (uu___1900_26176.strict_args_tab);
        erasable_types_tab = (uu___1900_26176.erasable_types_tab)
      }), uu____26170)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26188 =
      let uu____26191 = FStar_Ident.id_of_text ""  in [uu____26191]  in
    FStar_Ident.lid_of_ids uu____26188  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26198 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26198
        then
          let uu____26203 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26203 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1908_26231 = env  in
       {
         solver = (uu___1908_26231.solver);
         range = (uu___1908_26231.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1908_26231.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1908_26231.expected_typ);
         sigtab = (uu___1908_26231.sigtab);
         attrtab = (uu___1908_26231.attrtab);
         instantiate_imp = (uu___1908_26231.instantiate_imp);
         effects = (uu___1908_26231.effects);
         generalize = (uu___1908_26231.generalize);
         letrecs = (uu___1908_26231.letrecs);
         top_level = (uu___1908_26231.top_level);
         check_uvars = (uu___1908_26231.check_uvars);
         use_eq = (uu___1908_26231.use_eq);
         use_eq_strict = (uu___1908_26231.use_eq_strict);
         is_iface = (uu___1908_26231.is_iface);
         admit = (uu___1908_26231.admit);
         lax = (uu___1908_26231.lax);
         lax_universes = (uu___1908_26231.lax_universes);
         phase1 = (uu___1908_26231.phase1);
         failhard = (uu___1908_26231.failhard);
         nosynth = (uu___1908_26231.nosynth);
         uvar_subtyping = (uu___1908_26231.uvar_subtyping);
         tc_term = (uu___1908_26231.tc_term);
         type_of = (uu___1908_26231.type_of);
         universe_of = (uu___1908_26231.universe_of);
         check_type_of = (uu___1908_26231.check_type_of);
         use_bv_sorts = (uu___1908_26231.use_bv_sorts);
         qtbl_name_and_index = (uu___1908_26231.qtbl_name_and_index);
         normalized_eff_names = (uu___1908_26231.normalized_eff_names);
         fv_delta_depths = (uu___1908_26231.fv_delta_depths);
         proof_ns = (uu___1908_26231.proof_ns);
         synth_hook = (uu___1908_26231.synth_hook);
         try_solve_implicits_hook =
           (uu___1908_26231.try_solve_implicits_hook);
         splice = (uu___1908_26231.splice);
         mpreprocess = (uu___1908_26231.mpreprocess);
         postprocess = (uu___1908_26231.postprocess);
         is_native_tactic = (uu___1908_26231.is_native_tactic);
         identifier_info = (uu___1908_26231.identifier_info);
         tc_hooks = (uu___1908_26231.tc_hooks);
         dsenv = (uu___1908_26231.dsenv);
         nbe = (uu___1908_26231.nbe);
         strict_args_tab = (uu___1908_26231.strict_args_tab);
         erasable_types_tab = (uu___1908_26231.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26283)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26287,(uu____26288,t)))::tl1
          ->
          let uu____26309 =
            let uu____26312 = FStar_Syntax_Free.uvars t  in
            ext out uu____26312  in
          aux uu____26309 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26315;
            FStar_Syntax_Syntax.index = uu____26316;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26324 =
            let uu____26327 = FStar_Syntax_Free.uvars t  in
            ext out uu____26327  in
          aux uu____26324 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26385)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26389,(uu____26390,t)))::tl1
          ->
          let uu____26411 =
            let uu____26414 = FStar_Syntax_Free.univs t  in
            ext out uu____26414  in
          aux uu____26411 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26417;
            FStar_Syntax_Syntax.index = uu____26418;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26426 =
            let uu____26429 = FStar_Syntax_Free.univs t  in
            ext out uu____26429  in
          aux uu____26426 tl1
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
          let uu____26491 = FStar_Util.set_add uname out  in
          aux uu____26491 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26494,(uu____26495,t)))::tl1
          ->
          let uu____26516 =
            let uu____26519 = FStar_Syntax_Free.univnames t  in
            ext out uu____26519  in
          aux uu____26516 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26522;
            FStar_Syntax_Syntax.index = uu____26523;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26531 =
            let uu____26534 = FStar_Syntax_Free.univnames t  in
            ext out uu____26534  in
          aux uu____26531 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26555  ->
            match uu___12_26555 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26559 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26572 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26583 =
      let uu____26592 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26592
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26583 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26640 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26653  ->
              match uu___13_26653 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26656 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26656
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26662) ->
                  let uu____26679 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26679))
       in
    FStar_All.pipe_right uu____26640 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26693  ->
    match uu___14_26693 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26699 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26699
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26722  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26777) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26810,uu____26811) -> false  in
      let uu____26825 =
        FStar_List.tryFind
          (fun uu____26847  ->
             match uu____26847 with | (p,uu____26858) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26825 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26877,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26907 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26907
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2051_26929 = e  in
        {
          solver = (uu___2051_26929.solver);
          range = (uu___2051_26929.range);
          curmodule = (uu___2051_26929.curmodule);
          gamma = (uu___2051_26929.gamma);
          gamma_sig = (uu___2051_26929.gamma_sig);
          gamma_cache = (uu___2051_26929.gamma_cache);
          modules = (uu___2051_26929.modules);
          expected_typ = (uu___2051_26929.expected_typ);
          sigtab = (uu___2051_26929.sigtab);
          attrtab = (uu___2051_26929.attrtab);
          instantiate_imp = (uu___2051_26929.instantiate_imp);
          effects = (uu___2051_26929.effects);
          generalize = (uu___2051_26929.generalize);
          letrecs = (uu___2051_26929.letrecs);
          top_level = (uu___2051_26929.top_level);
          check_uvars = (uu___2051_26929.check_uvars);
          use_eq = (uu___2051_26929.use_eq);
          use_eq_strict = (uu___2051_26929.use_eq_strict);
          is_iface = (uu___2051_26929.is_iface);
          admit = (uu___2051_26929.admit);
          lax = (uu___2051_26929.lax);
          lax_universes = (uu___2051_26929.lax_universes);
          phase1 = (uu___2051_26929.phase1);
          failhard = (uu___2051_26929.failhard);
          nosynth = (uu___2051_26929.nosynth);
          uvar_subtyping = (uu___2051_26929.uvar_subtyping);
          tc_term = (uu___2051_26929.tc_term);
          type_of = (uu___2051_26929.type_of);
          universe_of = (uu___2051_26929.universe_of);
          check_type_of = (uu___2051_26929.check_type_of);
          use_bv_sorts = (uu___2051_26929.use_bv_sorts);
          qtbl_name_and_index = (uu___2051_26929.qtbl_name_and_index);
          normalized_eff_names = (uu___2051_26929.normalized_eff_names);
          fv_delta_depths = (uu___2051_26929.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2051_26929.synth_hook);
          try_solve_implicits_hook =
            (uu___2051_26929.try_solve_implicits_hook);
          splice = (uu___2051_26929.splice);
          mpreprocess = (uu___2051_26929.mpreprocess);
          postprocess = (uu___2051_26929.postprocess);
          is_native_tactic = (uu___2051_26929.is_native_tactic);
          identifier_info = (uu___2051_26929.identifier_info);
          tc_hooks = (uu___2051_26929.tc_hooks);
          dsenv = (uu___2051_26929.dsenv);
          nbe = (uu___2051_26929.nbe);
          strict_args_tab = (uu___2051_26929.strict_args_tab);
          erasable_types_tab = (uu___2051_26929.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2060_26977 = e  in
      {
        solver = (uu___2060_26977.solver);
        range = (uu___2060_26977.range);
        curmodule = (uu___2060_26977.curmodule);
        gamma = (uu___2060_26977.gamma);
        gamma_sig = (uu___2060_26977.gamma_sig);
        gamma_cache = (uu___2060_26977.gamma_cache);
        modules = (uu___2060_26977.modules);
        expected_typ = (uu___2060_26977.expected_typ);
        sigtab = (uu___2060_26977.sigtab);
        attrtab = (uu___2060_26977.attrtab);
        instantiate_imp = (uu___2060_26977.instantiate_imp);
        effects = (uu___2060_26977.effects);
        generalize = (uu___2060_26977.generalize);
        letrecs = (uu___2060_26977.letrecs);
        top_level = (uu___2060_26977.top_level);
        check_uvars = (uu___2060_26977.check_uvars);
        use_eq = (uu___2060_26977.use_eq);
        use_eq_strict = (uu___2060_26977.use_eq_strict);
        is_iface = (uu___2060_26977.is_iface);
        admit = (uu___2060_26977.admit);
        lax = (uu___2060_26977.lax);
        lax_universes = (uu___2060_26977.lax_universes);
        phase1 = (uu___2060_26977.phase1);
        failhard = (uu___2060_26977.failhard);
        nosynth = (uu___2060_26977.nosynth);
        uvar_subtyping = (uu___2060_26977.uvar_subtyping);
        tc_term = (uu___2060_26977.tc_term);
        type_of = (uu___2060_26977.type_of);
        universe_of = (uu___2060_26977.universe_of);
        check_type_of = (uu___2060_26977.check_type_of);
        use_bv_sorts = (uu___2060_26977.use_bv_sorts);
        qtbl_name_and_index = (uu___2060_26977.qtbl_name_and_index);
        normalized_eff_names = (uu___2060_26977.normalized_eff_names);
        fv_delta_depths = (uu___2060_26977.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2060_26977.synth_hook);
        try_solve_implicits_hook = (uu___2060_26977.try_solve_implicits_hook);
        splice = (uu___2060_26977.splice);
        mpreprocess = (uu___2060_26977.mpreprocess);
        postprocess = (uu___2060_26977.postprocess);
        is_native_tactic = (uu___2060_26977.is_native_tactic);
        identifier_info = (uu___2060_26977.identifier_info);
        tc_hooks = (uu___2060_26977.tc_hooks);
        dsenv = (uu___2060_26977.dsenv);
        nbe = (uu___2060_26977.nbe);
        strict_args_tab = (uu___2060_26977.strict_args_tab);
        erasable_types_tab = (uu___2060_26977.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26993 = FStar_Syntax_Free.names t  in
      let uu____26996 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26993 uu____26996
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27019 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27019
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27029 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27029
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27050 =
      match uu____27050 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27070 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27070)
       in
    let uu____27078 =
      let uu____27082 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27082 FStar_List.rev  in
    FStar_All.pipe_right uu____27078 (FStar_String.concat " ")
  
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
                  (let uu____27150 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27150 with
                   | FStar_Pervasives_Native.Some uu____27154 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27157 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27167;
        FStar_TypeChecker_Common.univ_ineqs = uu____27168;
        FStar_TypeChecker_Common.implicits = uu____27169;_} -> true
    | uu____27179 -> false
  
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
          let uu___2104_27201 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2104_27201.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2104_27201.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2104_27201.FStar_TypeChecker_Common.implicits)
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
          let uu____27240 = FStar_Options.defensive ()  in
          if uu____27240
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27246 =
              let uu____27248 =
                let uu____27250 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27250  in
              Prims.op_Negation uu____27248  in
            (if uu____27246
             then
               let uu____27257 =
                 let uu____27263 =
                   let uu____27265 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27267 =
                     let uu____27269 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27269
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27265 uu____27267
                    in
                 (FStar_Errors.Warning_Defensive, uu____27263)  in
               FStar_Errors.log_issue rng uu____27257
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
          let uu____27309 =
            let uu____27311 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27311  in
          if uu____27309
          then ()
          else
            (let uu____27316 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27316 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27342 =
            let uu____27344 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27344  in
          if uu____27342
          then ()
          else
            (let uu____27349 = bound_vars e  in
             def_check_closed_in rng msg uu____27349 t)
  
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
          let uu___2141_27388 = g  in
          let uu____27389 =
            let uu____27390 =
              let uu____27391 =
                let uu____27398 =
                  let uu____27399 =
                    let uu____27416 =
                      let uu____27427 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27427]  in
                    (f, uu____27416)  in
                  FStar_Syntax_Syntax.Tm_app uu____27399  in
                FStar_Syntax_Syntax.mk uu____27398  in
              uu____27391 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27464  -> FStar_TypeChecker_Common.NonTrivial _27464)
              uu____27390
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27389;
            FStar_TypeChecker_Common.deferred =
              (uu___2141_27388.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2141_27388.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2141_27388.FStar_TypeChecker_Common.implicits)
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
          let uu___2148_27482 = g  in
          let uu____27483 =
            let uu____27484 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27484  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27483;
            FStar_TypeChecker_Common.deferred =
              (uu___2148_27482.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2148_27482.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2148_27482.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2153_27501 = g  in
          let uu____27502 =
            let uu____27503 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27503  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27502;
            FStar_TypeChecker_Common.deferred =
              (uu___2153_27501.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2153_27501.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2153_27501.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2157_27505 = g  in
          let uu____27506 =
            let uu____27507 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27507  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27506;
            FStar_TypeChecker_Common.deferred =
              (uu___2157_27505.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2157_27505.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2157_27505.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27514 ->
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
                       let uu____27591 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27591
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2180_27598 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2180_27598.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2180_27598.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2180_27598.FStar_TypeChecker_Common.implicits)
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
               let uu____27632 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27632
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
            let uu___2195_27659 = g  in
            let uu____27660 =
              let uu____27661 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27661  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27660;
              FStar_TypeChecker_Common.deferred =
                (uu___2195_27659.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2195_27659.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2195_27659.FStar_TypeChecker_Common.implicits)
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
          fun should_check1  ->
            fun meta  ->
              let uu____27719 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27719 with
              | FStar_Pervasives_Native.Some
                  (uu____27744::(tm,uu____27746)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27810 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27828 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27828;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check1;
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
                    (let uu____27860 =
                       debug env (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27860
                     then
                       let uu____27864 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27864
                     else ());
                    (let g =
                       let uu___2219_27870 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2219_27870.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2219_27870.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2219_27870.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27924 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27981  ->
                      fun b  ->
                        match uu____27981 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____28023 =
                              let uu____28036 = reason b  in
                              new_implicit_var_aux uu____28036 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____28023 with
                             | (t,uu____28053,g_t) ->
                                 let uu____28067 =
                                   let uu____28070 =
                                     let uu____28073 =
                                       let uu____28074 =
                                         let uu____28081 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28081, t)  in
                                       FStar_Syntax_Syntax.NT uu____28074  in
                                     [uu____28073]  in
                                   FStar_List.append substs1 uu____28070  in
                                 let uu____28092 = conj_guard g g_t  in
                                 (uu____28067,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28092))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27924
              (fun uu____28121  ->
                 match uu____28121 with
                 | (uu____28138,uvars1,g) -> (uvars1, g))
  
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
                let uu____28179 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28179 FStar_Util.must  in
              let uu____28196 = inst_tscheme_with post_ts [u]  in
              match uu____28196 with
              | (uu____28201,post) ->
                  let uu____28203 =
                    let uu____28208 =
                      let uu____28209 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28209]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28208  in
                  uu____28203 FStar_Pervasives_Native.None r
               in
            let uu____28242 =
              let uu____28247 =
                let uu____28248 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28248]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28247  in
            uu____28242 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28284  -> ());
    push = (fun uu____28286  -> ());
    pop = (fun uu____28289  -> ());
    snapshot =
      (fun uu____28292  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28311  -> fun uu____28312  -> ());
    encode_sig = (fun uu____28327  -> fun uu____28328  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28334 =
             let uu____28341 = FStar_Options.peek ()  in (e, g, uu____28341)
              in
           [uu____28334]);
    solve = (fun uu____28357  -> fun uu____28358  -> fun uu____28359  -> ());
    finish = (fun uu____28366  -> ());
    refresh = (fun uu____28368  -> ())
  } 