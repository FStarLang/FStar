open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | ZetaFull 
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
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ZetaFull  -> true | uu____139 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____151 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____169 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____180 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____191 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____202 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____213 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____224 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____236 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____257 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____284 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____311 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____335 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____346 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____357 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____368 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____379 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____390 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____401 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____412 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____423 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____434 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____445 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____456 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____467 -> false
  
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
      | (ZetaFull ,ZetaFull ) -> true
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
      | uu____528 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____554 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____565 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____576 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____588 -> false
  
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
           (fun uu___0_14374  ->
              match uu___0_14374 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14377 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14377  in
                  let uu____14378 =
                    let uu____14379 = FStar_Syntax_Subst.compress y  in
                    uu____14379.FStar_Syntax_Syntax.n  in
                  (match uu____14378 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14383 =
                         let uu___327_14384 = y1  in
                         let uu____14385 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14384.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14384.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14385
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14383
                   | uu____14388 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___333_14402 = env  in
      let uu____14403 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___333_14402.solver);
        range = (uu___333_14402.range);
        curmodule = (uu___333_14402.curmodule);
        gamma = uu____14403;
        gamma_sig = (uu___333_14402.gamma_sig);
        gamma_cache = (uu___333_14402.gamma_cache);
        modules = (uu___333_14402.modules);
        expected_typ = (uu___333_14402.expected_typ);
        sigtab = (uu___333_14402.sigtab);
        attrtab = (uu___333_14402.attrtab);
        instantiate_imp = (uu___333_14402.instantiate_imp);
        effects = (uu___333_14402.effects);
        generalize = (uu___333_14402.generalize);
        letrecs = (uu___333_14402.letrecs);
        top_level = (uu___333_14402.top_level);
        check_uvars = (uu___333_14402.check_uvars);
        use_eq = (uu___333_14402.use_eq);
        use_eq_strict = (uu___333_14402.use_eq_strict);
        is_iface = (uu___333_14402.is_iface);
        admit = (uu___333_14402.admit);
        lax = (uu___333_14402.lax);
        lax_universes = (uu___333_14402.lax_universes);
        phase1 = (uu___333_14402.phase1);
        failhard = (uu___333_14402.failhard);
        nosynth = (uu___333_14402.nosynth);
        uvar_subtyping = (uu___333_14402.uvar_subtyping);
        tc_term = (uu___333_14402.tc_term);
        type_of = (uu___333_14402.type_of);
        universe_of = (uu___333_14402.universe_of);
        check_type_of = (uu___333_14402.check_type_of);
        use_bv_sorts = (uu___333_14402.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14402.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14402.normalized_eff_names);
        fv_delta_depths = (uu___333_14402.fv_delta_depths);
        proof_ns = (uu___333_14402.proof_ns);
        synth_hook = (uu___333_14402.synth_hook);
        try_solve_implicits_hook = (uu___333_14402.try_solve_implicits_hook);
        splice = (uu___333_14402.splice);
        mpreprocess = (uu___333_14402.mpreprocess);
        postprocess = (uu___333_14402.postprocess);
        is_native_tactic = (uu___333_14402.is_native_tactic);
        identifier_info = (uu___333_14402.identifier_info);
        tc_hooks = (uu___333_14402.tc_hooks);
        dsenv = (uu___333_14402.dsenv);
        nbe = (uu___333_14402.nbe);
        strict_args_tab = (uu___333_14402.strict_args_tab);
        erasable_types_tab = (uu___333_14402.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14411  -> fun uu____14412  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___340_14434 = env  in
      {
        solver = (uu___340_14434.solver);
        range = (uu___340_14434.range);
        curmodule = (uu___340_14434.curmodule);
        gamma = (uu___340_14434.gamma);
        gamma_sig = (uu___340_14434.gamma_sig);
        gamma_cache = (uu___340_14434.gamma_cache);
        modules = (uu___340_14434.modules);
        expected_typ = (uu___340_14434.expected_typ);
        sigtab = (uu___340_14434.sigtab);
        attrtab = (uu___340_14434.attrtab);
        instantiate_imp = (uu___340_14434.instantiate_imp);
        effects = (uu___340_14434.effects);
        generalize = (uu___340_14434.generalize);
        letrecs = (uu___340_14434.letrecs);
        top_level = (uu___340_14434.top_level);
        check_uvars = (uu___340_14434.check_uvars);
        use_eq = (uu___340_14434.use_eq);
        use_eq_strict = (uu___340_14434.use_eq_strict);
        is_iface = (uu___340_14434.is_iface);
        admit = (uu___340_14434.admit);
        lax = (uu___340_14434.lax);
        lax_universes = (uu___340_14434.lax_universes);
        phase1 = (uu___340_14434.phase1);
        failhard = (uu___340_14434.failhard);
        nosynth = (uu___340_14434.nosynth);
        uvar_subtyping = (uu___340_14434.uvar_subtyping);
        tc_term = (uu___340_14434.tc_term);
        type_of = (uu___340_14434.type_of);
        universe_of = (uu___340_14434.universe_of);
        check_type_of = (uu___340_14434.check_type_of);
        use_bv_sorts = (uu___340_14434.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14434.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14434.normalized_eff_names);
        fv_delta_depths = (uu___340_14434.fv_delta_depths);
        proof_ns = (uu___340_14434.proof_ns);
        synth_hook = (uu___340_14434.synth_hook);
        try_solve_implicits_hook = (uu___340_14434.try_solve_implicits_hook);
        splice = (uu___340_14434.splice);
        mpreprocess = (uu___340_14434.mpreprocess);
        postprocess = (uu___340_14434.postprocess);
        is_native_tactic = (uu___340_14434.is_native_tactic);
        identifier_info = (uu___340_14434.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14434.dsenv);
        nbe = (uu___340_14434.nbe);
        strict_args_tab = (uu___340_14434.strict_args_tab);
        erasable_types_tab = (uu___340_14434.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___344_14446 = e  in
      let uu____14447 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___344_14446.solver);
        range = (uu___344_14446.range);
        curmodule = (uu___344_14446.curmodule);
        gamma = (uu___344_14446.gamma);
        gamma_sig = (uu___344_14446.gamma_sig);
        gamma_cache = (uu___344_14446.gamma_cache);
        modules = (uu___344_14446.modules);
        expected_typ = (uu___344_14446.expected_typ);
        sigtab = (uu___344_14446.sigtab);
        attrtab = (uu___344_14446.attrtab);
        instantiate_imp = (uu___344_14446.instantiate_imp);
        effects = (uu___344_14446.effects);
        generalize = (uu___344_14446.generalize);
        letrecs = (uu___344_14446.letrecs);
        top_level = (uu___344_14446.top_level);
        check_uvars = (uu___344_14446.check_uvars);
        use_eq = (uu___344_14446.use_eq);
        use_eq_strict = (uu___344_14446.use_eq_strict);
        is_iface = (uu___344_14446.is_iface);
        admit = (uu___344_14446.admit);
        lax = (uu___344_14446.lax);
        lax_universes = (uu___344_14446.lax_universes);
        phase1 = (uu___344_14446.phase1);
        failhard = (uu___344_14446.failhard);
        nosynth = (uu___344_14446.nosynth);
        uvar_subtyping = (uu___344_14446.uvar_subtyping);
        tc_term = (uu___344_14446.tc_term);
        type_of = (uu___344_14446.type_of);
        universe_of = (uu___344_14446.universe_of);
        check_type_of = (uu___344_14446.check_type_of);
        use_bv_sorts = (uu___344_14446.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14446.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14446.normalized_eff_names);
        fv_delta_depths = (uu___344_14446.fv_delta_depths);
        proof_ns = (uu___344_14446.proof_ns);
        synth_hook = (uu___344_14446.synth_hook);
        try_solve_implicits_hook = (uu___344_14446.try_solve_implicits_hook);
        splice = (uu___344_14446.splice);
        mpreprocess = (uu___344_14446.mpreprocess);
        postprocess = (uu___344_14446.postprocess);
        is_native_tactic = (uu___344_14446.is_native_tactic);
        identifier_info = (uu___344_14446.identifier_info);
        tc_hooks = (uu___344_14446.tc_hooks);
        dsenv = uu____14447;
        nbe = (uu___344_14446.nbe);
        strict_args_tab = (uu___344_14446.strict_args_tab);
        erasable_types_tab = (uu___344_14446.erasable_types_tab)
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
      | (NoDelta ,uu____14476) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14479,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14481,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14484 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14498 . unit -> 'Auu____14498 FStar_Util.smap =
  fun uu____14505  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14511 . unit -> 'Auu____14511 FStar_Util.smap =
  fun uu____14518  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14656 = new_gamma_cache ()  in
                  let uu____14659 = new_sigtab ()  in
                  let uu____14662 = new_sigtab ()  in
                  let uu____14669 =
                    let uu____14684 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14684, FStar_Pervasives_Native.None)  in
                  let uu____14705 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14709 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14713 = FStar_Options.using_facts_from ()  in
                  let uu____14714 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14717 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14718 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14732 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14656;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14659;
                    attrtab = uu____14662;
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
                    qtbl_name_and_index = uu____14669;
                    normalized_eff_names = uu____14705;
                    fv_delta_depths = uu____14709;
                    proof_ns = uu____14713;
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
                    is_native_tactic = (fun uu____14847  -> false);
                    identifier_info = uu____14714;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14717;
                    nbe = nbe1;
                    strict_args_tab = uu____14718;
                    erasable_types_tab = uu____14732
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
  fun uu____14926  ->
    let uu____14927 = FStar_ST.op_Bang query_indices  in
    match uu____14927 with
    | [] -> failwith "Empty query indices!"
    | uu____14982 ->
        let uu____14992 =
          let uu____15002 =
            let uu____15010 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____15010  in
          let uu____15064 = FStar_ST.op_Bang query_indices  in uu____15002 ::
            uu____15064
           in
        FStar_ST.op_Colon_Equals query_indices uu____14992
  
let (pop_query_indices : unit -> unit) =
  fun uu____15160  ->
    let uu____15161 = FStar_ST.op_Bang query_indices  in
    match uu____15161 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15288  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15325  ->
    match uu____15325 with
    | (l,n1) ->
        let uu____15335 = FStar_ST.op_Bang query_indices  in
        (match uu____15335 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15457 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15480  ->
    let uu____15481 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15481
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15549 =
       let uu____15552 = FStar_ST.op_Bang stack  in env :: uu____15552  in
     FStar_ST.op_Colon_Equals stack uu____15549);
    (let uu___418_15601 = env  in
     let uu____15602 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15605 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15608 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15615 =
       let uu____15630 =
         let uu____15634 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15634  in
       let uu____15666 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15630, uu____15666)  in
     let uu____15715 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____15718 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____15721 =
       let uu____15724 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____15724  in
     let uu____15744 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15757 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___418_15601.solver);
       range = (uu___418_15601.range);
       curmodule = (uu___418_15601.curmodule);
       gamma = (uu___418_15601.gamma);
       gamma_sig = (uu___418_15601.gamma_sig);
       gamma_cache = uu____15602;
       modules = (uu___418_15601.modules);
       expected_typ = (uu___418_15601.expected_typ);
       sigtab = uu____15605;
       attrtab = uu____15608;
       instantiate_imp = (uu___418_15601.instantiate_imp);
       effects = (uu___418_15601.effects);
       generalize = (uu___418_15601.generalize);
       letrecs = (uu___418_15601.letrecs);
       top_level = (uu___418_15601.top_level);
       check_uvars = (uu___418_15601.check_uvars);
       use_eq = (uu___418_15601.use_eq);
       use_eq_strict = (uu___418_15601.use_eq_strict);
       is_iface = (uu___418_15601.is_iface);
       admit = (uu___418_15601.admit);
       lax = (uu___418_15601.lax);
       lax_universes = (uu___418_15601.lax_universes);
       phase1 = (uu___418_15601.phase1);
       failhard = (uu___418_15601.failhard);
       nosynth = (uu___418_15601.nosynth);
       uvar_subtyping = (uu___418_15601.uvar_subtyping);
       tc_term = (uu___418_15601.tc_term);
       type_of = (uu___418_15601.type_of);
       universe_of = (uu___418_15601.universe_of);
       check_type_of = (uu___418_15601.check_type_of);
       use_bv_sorts = (uu___418_15601.use_bv_sorts);
       qtbl_name_and_index = uu____15615;
       normalized_eff_names = uu____15715;
       fv_delta_depths = uu____15718;
       proof_ns = (uu___418_15601.proof_ns);
       synth_hook = (uu___418_15601.synth_hook);
       try_solve_implicits_hook = (uu___418_15601.try_solve_implicits_hook);
       splice = (uu___418_15601.splice);
       mpreprocess = (uu___418_15601.mpreprocess);
       postprocess = (uu___418_15601.postprocess);
       is_native_tactic = (uu___418_15601.is_native_tactic);
       identifier_info = uu____15721;
       tc_hooks = (uu___418_15601.tc_hooks);
       dsenv = (uu___418_15601.dsenv);
       nbe = (uu___418_15601.nbe);
       strict_args_tab = uu____15744;
       erasable_types_tab = uu____15757
     })
  
let (pop_stack : unit -> env) =
  fun uu____15767  ->
    let uu____15768 = FStar_ST.op_Bang stack  in
    match uu____15768 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15822 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15912  ->
           let uu____15913 = snapshot_stack env  in
           match uu____15913 with
           | (stack_depth,env1) ->
               let uu____15947 = snapshot_query_indices ()  in
               (match uu____15947 with
                | (query_indices_depth,()) ->
                    let uu____15980 = (env1.solver).snapshot msg  in
                    (match uu____15980 with
                     | (solver_depth,()) ->
                         let uu____16037 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____16037 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_16104 = env1  in
                                 {
                                   solver = (uu___443_16104.solver);
                                   range = (uu___443_16104.range);
                                   curmodule = (uu___443_16104.curmodule);
                                   gamma = (uu___443_16104.gamma);
                                   gamma_sig = (uu___443_16104.gamma_sig);
                                   gamma_cache = (uu___443_16104.gamma_cache);
                                   modules = (uu___443_16104.modules);
                                   expected_typ =
                                     (uu___443_16104.expected_typ);
                                   sigtab = (uu___443_16104.sigtab);
                                   attrtab = (uu___443_16104.attrtab);
                                   instantiate_imp =
                                     (uu___443_16104.instantiate_imp);
                                   effects = (uu___443_16104.effects);
                                   generalize = (uu___443_16104.generalize);
                                   letrecs = (uu___443_16104.letrecs);
                                   top_level = (uu___443_16104.top_level);
                                   check_uvars = (uu___443_16104.check_uvars);
                                   use_eq = (uu___443_16104.use_eq);
                                   use_eq_strict =
                                     (uu___443_16104.use_eq_strict);
                                   is_iface = (uu___443_16104.is_iface);
                                   admit = (uu___443_16104.admit);
                                   lax = (uu___443_16104.lax);
                                   lax_universes =
                                     (uu___443_16104.lax_universes);
                                   phase1 = (uu___443_16104.phase1);
                                   failhard = (uu___443_16104.failhard);
                                   nosynth = (uu___443_16104.nosynth);
                                   uvar_subtyping =
                                     (uu___443_16104.uvar_subtyping);
                                   tc_term = (uu___443_16104.tc_term);
                                   type_of = (uu___443_16104.type_of);
                                   universe_of = (uu___443_16104.universe_of);
                                   check_type_of =
                                     (uu___443_16104.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_16104.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_16104.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_16104.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_16104.fv_delta_depths);
                                   proof_ns = (uu___443_16104.proof_ns);
                                   synth_hook = (uu___443_16104.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_16104.try_solve_implicits_hook);
                                   splice = (uu___443_16104.splice);
                                   mpreprocess = (uu___443_16104.mpreprocess);
                                   postprocess = (uu___443_16104.postprocess);
                                   is_native_tactic =
                                     (uu___443_16104.is_native_tactic);
                                   identifier_info =
                                     (uu___443_16104.identifier_info);
                                   tc_hooks = (uu___443_16104.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_16104.nbe);
                                   strict_args_tab =
                                     (uu___443_16104.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_16104.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16138  ->
             let uu____16139 =
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
             match uu____16139 with
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
                             ((let uu____16319 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16319
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____16335 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____16335
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16367,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16409 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16439  ->
                  match uu____16439 with
                  | (m,uu____16447) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16409 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___488_16462 = env  in
               {
                 solver = (uu___488_16462.solver);
                 range = (uu___488_16462.range);
                 curmodule = (uu___488_16462.curmodule);
                 gamma = (uu___488_16462.gamma);
                 gamma_sig = (uu___488_16462.gamma_sig);
                 gamma_cache = (uu___488_16462.gamma_cache);
                 modules = (uu___488_16462.modules);
                 expected_typ = (uu___488_16462.expected_typ);
                 sigtab = (uu___488_16462.sigtab);
                 attrtab = (uu___488_16462.attrtab);
                 instantiate_imp = (uu___488_16462.instantiate_imp);
                 effects = (uu___488_16462.effects);
                 generalize = (uu___488_16462.generalize);
                 letrecs = (uu___488_16462.letrecs);
                 top_level = (uu___488_16462.top_level);
                 check_uvars = (uu___488_16462.check_uvars);
                 use_eq = (uu___488_16462.use_eq);
                 use_eq_strict = (uu___488_16462.use_eq_strict);
                 is_iface = (uu___488_16462.is_iface);
                 admit = (uu___488_16462.admit);
                 lax = (uu___488_16462.lax);
                 lax_universes = (uu___488_16462.lax_universes);
                 phase1 = (uu___488_16462.phase1);
                 failhard = (uu___488_16462.failhard);
                 nosynth = (uu___488_16462.nosynth);
                 uvar_subtyping = (uu___488_16462.uvar_subtyping);
                 tc_term = (uu___488_16462.tc_term);
                 type_of = (uu___488_16462.type_of);
                 universe_of = (uu___488_16462.universe_of);
                 check_type_of = (uu___488_16462.check_type_of);
                 use_bv_sorts = (uu___488_16462.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16462.normalized_eff_names);
                 fv_delta_depths = (uu___488_16462.fv_delta_depths);
                 proof_ns = (uu___488_16462.proof_ns);
                 synth_hook = (uu___488_16462.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16462.try_solve_implicits_hook);
                 splice = (uu___488_16462.splice);
                 mpreprocess = (uu___488_16462.mpreprocess);
                 postprocess = (uu___488_16462.postprocess);
                 is_native_tactic = (uu___488_16462.is_native_tactic);
                 identifier_info = (uu___488_16462.identifier_info);
                 tc_hooks = (uu___488_16462.tc_hooks);
                 dsenv = (uu___488_16462.dsenv);
                 nbe = (uu___488_16462.nbe);
                 strict_args_tab = (uu___488_16462.strict_args_tab);
                 erasable_types_tab = (uu___488_16462.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16479,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___497_16495 = env  in
               {
                 solver = (uu___497_16495.solver);
                 range = (uu___497_16495.range);
                 curmodule = (uu___497_16495.curmodule);
                 gamma = (uu___497_16495.gamma);
                 gamma_sig = (uu___497_16495.gamma_sig);
                 gamma_cache = (uu___497_16495.gamma_cache);
                 modules = (uu___497_16495.modules);
                 expected_typ = (uu___497_16495.expected_typ);
                 sigtab = (uu___497_16495.sigtab);
                 attrtab = (uu___497_16495.attrtab);
                 instantiate_imp = (uu___497_16495.instantiate_imp);
                 effects = (uu___497_16495.effects);
                 generalize = (uu___497_16495.generalize);
                 letrecs = (uu___497_16495.letrecs);
                 top_level = (uu___497_16495.top_level);
                 check_uvars = (uu___497_16495.check_uvars);
                 use_eq = (uu___497_16495.use_eq);
                 use_eq_strict = (uu___497_16495.use_eq_strict);
                 is_iface = (uu___497_16495.is_iface);
                 admit = (uu___497_16495.admit);
                 lax = (uu___497_16495.lax);
                 lax_universes = (uu___497_16495.lax_universes);
                 phase1 = (uu___497_16495.phase1);
                 failhard = (uu___497_16495.failhard);
                 nosynth = (uu___497_16495.nosynth);
                 uvar_subtyping = (uu___497_16495.uvar_subtyping);
                 tc_term = (uu___497_16495.tc_term);
                 type_of = (uu___497_16495.type_of);
                 universe_of = (uu___497_16495.universe_of);
                 check_type_of = (uu___497_16495.check_type_of);
                 use_bv_sorts = (uu___497_16495.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16495.normalized_eff_names);
                 fv_delta_depths = (uu___497_16495.fv_delta_depths);
                 proof_ns = (uu___497_16495.proof_ns);
                 synth_hook = (uu___497_16495.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16495.try_solve_implicits_hook);
                 splice = (uu___497_16495.splice);
                 mpreprocess = (uu___497_16495.mpreprocess);
                 postprocess = (uu___497_16495.postprocess);
                 is_native_tactic = (uu___497_16495.is_native_tactic);
                 identifier_info = (uu___497_16495.identifier_info);
                 tc_hooks = (uu___497_16495.tc_hooks);
                 dsenv = (uu___497_16495.dsenv);
                 nbe = (uu___497_16495.nbe);
                 strict_args_tab = (uu___497_16495.strict_args_tab);
                 erasable_types_tab = (uu___497_16495.erasable_types_tab)
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
        (let uu___504_16538 = e  in
         {
           solver = (uu___504_16538.solver);
           range = r;
           curmodule = (uu___504_16538.curmodule);
           gamma = (uu___504_16538.gamma);
           gamma_sig = (uu___504_16538.gamma_sig);
           gamma_cache = (uu___504_16538.gamma_cache);
           modules = (uu___504_16538.modules);
           expected_typ = (uu___504_16538.expected_typ);
           sigtab = (uu___504_16538.sigtab);
           attrtab = (uu___504_16538.attrtab);
           instantiate_imp = (uu___504_16538.instantiate_imp);
           effects = (uu___504_16538.effects);
           generalize = (uu___504_16538.generalize);
           letrecs = (uu___504_16538.letrecs);
           top_level = (uu___504_16538.top_level);
           check_uvars = (uu___504_16538.check_uvars);
           use_eq = (uu___504_16538.use_eq);
           use_eq_strict = (uu___504_16538.use_eq_strict);
           is_iface = (uu___504_16538.is_iface);
           admit = (uu___504_16538.admit);
           lax = (uu___504_16538.lax);
           lax_universes = (uu___504_16538.lax_universes);
           phase1 = (uu___504_16538.phase1);
           failhard = (uu___504_16538.failhard);
           nosynth = (uu___504_16538.nosynth);
           uvar_subtyping = (uu___504_16538.uvar_subtyping);
           tc_term = (uu___504_16538.tc_term);
           type_of = (uu___504_16538.type_of);
           universe_of = (uu___504_16538.universe_of);
           check_type_of = (uu___504_16538.check_type_of);
           use_bv_sorts = (uu___504_16538.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16538.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16538.normalized_eff_names);
           fv_delta_depths = (uu___504_16538.fv_delta_depths);
           proof_ns = (uu___504_16538.proof_ns);
           synth_hook = (uu___504_16538.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16538.try_solve_implicits_hook);
           splice = (uu___504_16538.splice);
           mpreprocess = (uu___504_16538.mpreprocess);
           postprocess = (uu___504_16538.postprocess);
           is_native_tactic = (uu___504_16538.is_native_tactic);
           identifier_info = (uu___504_16538.identifier_info);
           tc_hooks = (uu___504_16538.tc_hooks);
           dsenv = (uu___504_16538.dsenv);
           nbe = (uu___504_16538.nbe);
           strict_args_tab = (uu___504_16538.strict_args_tab);
           erasable_types_tab = (uu___504_16538.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16558 =
        let uu____16559 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16559 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16558
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16614 =
          let uu____16615 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16615 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16614
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16670 =
          let uu____16671 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16671 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16670
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16726 =
        let uu____16727 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16727 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16726
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___521_16791 = env  in
      {
        solver = (uu___521_16791.solver);
        range = (uu___521_16791.range);
        curmodule = lid;
        gamma = (uu___521_16791.gamma);
        gamma_sig = (uu___521_16791.gamma_sig);
        gamma_cache = (uu___521_16791.gamma_cache);
        modules = (uu___521_16791.modules);
        expected_typ = (uu___521_16791.expected_typ);
        sigtab = (uu___521_16791.sigtab);
        attrtab = (uu___521_16791.attrtab);
        instantiate_imp = (uu___521_16791.instantiate_imp);
        effects = (uu___521_16791.effects);
        generalize = (uu___521_16791.generalize);
        letrecs = (uu___521_16791.letrecs);
        top_level = (uu___521_16791.top_level);
        check_uvars = (uu___521_16791.check_uvars);
        use_eq = (uu___521_16791.use_eq);
        use_eq_strict = (uu___521_16791.use_eq_strict);
        is_iface = (uu___521_16791.is_iface);
        admit = (uu___521_16791.admit);
        lax = (uu___521_16791.lax);
        lax_universes = (uu___521_16791.lax_universes);
        phase1 = (uu___521_16791.phase1);
        failhard = (uu___521_16791.failhard);
        nosynth = (uu___521_16791.nosynth);
        uvar_subtyping = (uu___521_16791.uvar_subtyping);
        tc_term = (uu___521_16791.tc_term);
        type_of = (uu___521_16791.type_of);
        universe_of = (uu___521_16791.universe_of);
        check_type_of = (uu___521_16791.check_type_of);
        use_bv_sorts = (uu___521_16791.use_bv_sorts);
        qtbl_name_and_index = (uu___521_16791.qtbl_name_and_index);
        normalized_eff_names = (uu___521_16791.normalized_eff_names);
        fv_delta_depths = (uu___521_16791.fv_delta_depths);
        proof_ns = (uu___521_16791.proof_ns);
        synth_hook = (uu___521_16791.synth_hook);
        try_solve_implicits_hook = (uu___521_16791.try_solve_implicits_hook);
        splice = (uu___521_16791.splice);
        mpreprocess = (uu___521_16791.mpreprocess);
        postprocess = (uu___521_16791.postprocess);
        is_native_tactic = (uu___521_16791.is_native_tactic);
        identifier_info = (uu___521_16791.identifier_info);
        tc_hooks = (uu___521_16791.tc_hooks);
        dsenv = (uu___521_16791.dsenv);
        nbe = (uu___521_16791.nbe);
        strict_args_tab = (uu___521_16791.strict_args_tab);
        erasable_types_tab = (uu___521_16791.erasable_types_tab)
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
      let uu____16822 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16822
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16835 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16835)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16850 =
      let uu____16852 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16852  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16850)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16861  ->
    let uu____16862 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16862
  
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
      | ((formals,t),uu____16962) ->
          let vs = mk_univ_subst formals us  in
          let uu____16986 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16986)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17003  ->
    match uu___1_17003 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17029  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17049 = inst_tscheme t  in
      match uu____17049 with
      | (us,t1) ->
          let uu____17060 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17060)
  
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
          let uu____17085 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17087 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17085 uu____17087
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
        fun uu____17114  ->
          match uu____17114 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17128 =
                    let uu____17130 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17134 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17138 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17140 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17130 uu____17134 uu____17138 uu____17140
                     in
                  failwith uu____17128)
               else ();
               (let uu____17145 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17145))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17163 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17174 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17185 -> false
  
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
             | ([],uu____17233) -> Maybe
             | (uu____17240,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____17260 -> No  in
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
          let uu____17354 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____17354 with
          | FStar_Pervasives_Native.None  ->
              let uu____17377 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17421  ->
                     match uu___2_17421 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17460 = FStar_Ident.lid_equals lid l  in
                         if uu____17460
                         then
                           let uu____17483 =
                             let uu____17502 =
                               let uu____17517 = inst_tscheme t  in
                               FStar_Util.Inl uu____17517  in
                             let uu____17532 = FStar_Ident.range_of_lid l  in
                             (uu____17502, uu____17532)  in
                           FStar_Pervasives_Native.Some uu____17483
                         else FStar_Pervasives_Native.None
                     | uu____17585 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17377
                (fun uu____17623  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17633  ->
                        match uu___3_17633 with
                        | (uu____17636,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17638);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17639;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17640;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17641;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17642;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17643;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17665 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17665
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
                                  uu____17717 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17724 -> cache t  in
                            let uu____17725 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17725 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17731 =
                                   let uu____17732 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17732)
                                    in
                                 maybe_cache uu____17731)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17803 = find_in_sigtab env lid  in
         match uu____17803 with
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
      let uu____17884 = lookup_qname env lid  in
      match uu____17884 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17905,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____18019 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____18019 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18064 =
          let uu____18067 = lookup_attr env1 attr  in se1 :: uu____18067  in
        FStar_Util.smap_add (attrtab env1) attr uu____18064  in
      FStar_List.iter
        (fun attr  ->
           let uu____18077 =
             let uu____18078 = FStar_Syntax_Subst.compress attr  in
             uu____18078.FStar_Syntax_Syntax.n  in
           match uu____18077 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18082 =
                 let uu____18084 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18084.FStar_Ident.str  in
               add_one1 env se uu____18082
           | uu____18085 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18108) ->
          add_sigelts env ses
      | uu____18117 ->
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
        (fun uu___4_18155  ->
           match uu___4_18155 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18173 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18235,lb::[]),uu____18237) ->
            let uu____18246 =
              let uu____18255 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18264 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18255, uu____18264)  in
            FStar_Pervasives_Native.Some uu____18246
        | FStar_Syntax_Syntax.Sig_let ((uu____18277,lbs),uu____18279) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18311 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18324 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18324
                     then
                       let uu____18337 =
                         let uu____18346 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18355 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18346, uu____18355)  in
                       FStar_Pervasives_Native.Some uu____18337
                     else FStar_Pervasives_Native.None)
        | uu____18378 -> FStar_Pervasives_Native.None
  
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
                    let uu____18470 =
                      let uu____18472 =
                        let uu____18474 =
                          let uu____18476 =
                            let uu____18478 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18484 =
                              let uu____18486 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18486  in
                            Prims.op_Hat uu____18478 uu____18484  in
                          Prims.op_Hat ", expected " uu____18476  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18474
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18472
                       in
                    failwith uu____18470
                  else ());
             (let uu____18493 =
                let uu____18502 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18502, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18493))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18522,uu____18523) ->
            let uu____18528 =
              let uu____18537 =
                let uu____18542 =
                  let uu____18543 =
                    let uu____18546 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18546  in
                  (us, uu____18543)  in
                inst_ts us_opt uu____18542  in
              (uu____18537, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18528
        | uu____18565 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18654 =
          match uu____18654 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18750,uvs,t,uu____18753,uu____18754,uu____18755);
                      FStar_Syntax_Syntax.sigrng = uu____18756;
                      FStar_Syntax_Syntax.sigquals = uu____18757;
                      FStar_Syntax_Syntax.sigmeta = uu____18758;
                      FStar_Syntax_Syntax.sigattrs = uu____18759;
                      FStar_Syntax_Syntax.sigopts = uu____18760;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18785 =
                     let uu____18794 = inst_tscheme1 (uvs, t)  in
                     (uu____18794, rng)  in
                   FStar_Pervasives_Native.Some uu____18785
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18818;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18820;
                      FStar_Syntax_Syntax.sigattrs = uu____18821;
                      FStar_Syntax_Syntax.sigopts = uu____18822;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18841 =
                     let uu____18843 = in_cur_mod env l  in uu____18843 = Yes
                      in
                   if uu____18841
                   then
                     let uu____18855 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18855
                      then
                        let uu____18871 =
                          let uu____18880 = inst_tscheme1 (uvs, t)  in
                          (uu____18880, rng)  in
                        FStar_Pervasives_Native.Some uu____18871
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18913 =
                        let uu____18922 = inst_tscheme1 (uvs, t)  in
                        (uu____18922, rng)  in
                      FStar_Pervasives_Native.Some uu____18913)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18947,uu____18948);
                      FStar_Syntax_Syntax.sigrng = uu____18949;
                      FStar_Syntax_Syntax.sigquals = uu____18950;
                      FStar_Syntax_Syntax.sigmeta = uu____18951;
                      FStar_Syntax_Syntax.sigattrs = uu____18952;
                      FStar_Syntax_Syntax.sigopts = uu____18953;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18996 =
                          let uu____19005 = inst_tscheme1 (uvs, k)  in
                          (uu____19005, rng)  in
                        FStar_Pervasives_Native.Some uu____18996
                    | uu____19026 ->
                        let uu____19027 =
                          let uu____19036 =
                            let uu____19041 =
                              let uu____19042 =
                                let uu____19045 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19045
                                 in
                              (uvs, uu____19042)  in
                            inst_tscheme1 uu____19041  in
                          (uu____19036, rng)  in
                        FStar_Pervasives_Native.Some uu____19027)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19068,uu____19069);
                      FStar_Syntax_Syntax.sigrng = uu____19070;
                      FStar_Syntax_Syntax.sigquals = uu____19071;
                      FStar_Syntax_Syntax.sigmeta = uu____19072;
                      FStar_Syntax_Syntax.sigattrs = uu____19073;
                      FStar_Syntax_Syntax.sigopts = uu____19074;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19118 =
                          let uu____19127 = inst_tscheme_with (uvs, k) us  in
                          (uu____19127, rng)  in
                        FStar_Pervasives_Native.Some uu____19118
                    | uu____19148 ->
                        let uu____19149 =
                          let uu____19158 =
                            let uu____19163 =
                              let uu____19164 =
                                let uu____19167 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19167
                                 in
                              (uvs, uu____19164)  in
                            inst_tscheme_with uu____19163 us  in
                          (uu____19158, rng)  in
                        FStar_Pervasives_Native.Some uu____19149)
               | FStar_Util.Inr se ->
                   let uu____19203 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19224;
                          FStar_Syntax_Syntax.sigrng = uu____19225;
                          FStar_Syntax_Syntax.sigquals = uu____19226;
                          FStar_Syntax_Syntax.sigmeta = uu____19227;
                          FStar_Syntax_Syntax.sigattrs = uu____19228;
                          FStar_Syntax_Syntax.sigopts = uu____19229;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19246 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19203
                     (FStar_Util.map_option
                        (fun uu____19294  ->
                           match uu____19294 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19325 =
          let uu____19336 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19336 mapper  in
        match uu____19325 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19410 =
              let uu____19421 =
                let uu____19428 =
                  let uu___858_19431 = t  in
                  let uu____19432 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19431.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19432;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19431.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19428)  in
              (uu____19421, r)  in
            FStar_Pervasives_Native.Some uu____19410
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19481 = lookup_qname env l  in
      match uu____19481 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19502 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19556 = try_lookup_bv env bv  in
      match uu____19556 with
      | FStar_Pervasives_Native.None  ->
          let uu____19571 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19571 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19587 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19588 =
            let uu____19589 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19589  in
          (uu____19587, uu____19588)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19611 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19611 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19677 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19677  in
          let uu____19678 =
            let uu____19687 =
              let uu____19692 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19692)  in
            (uu____19687, r1)  in
          FStar_Pervasives_Native.Some uu____19678
  
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
        let uu____19727 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19727 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19760,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19785 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19785  in
            let uu____19786 =
              let uu____19791 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19791, r1)  in
            FStar_Pervasives_Native.Some uu____19786
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19815 = try_lookup_lid env l  in
      match uu____19815 with
      | FStar_Pervasives_Native.None  ->
          let uu____19842 = name_not_found l  in
          let uu____19848 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19842 uu____19848
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19891  ->
              match uu___5_19891 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19895 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19916 = lookup_qname env lid  in
      match uu____19916 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19925,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19928;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19930;
              FStar_Syntax_Syntax.sigattrs = uu____19931;
              FStar_Syntax_Syntax.sigopts = uu____19932;_},FStar_Pervasives_Native.None
            ),uu____19933)
          ->
          let uu____19984 =
            let uu____19991 =
              let uu____19992 =
                let uu____19995 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19995 t  in
              (uvs, uu____19992)  in
            (uu____19991, q)  in
          FStar_Pervasives_Native.Some uu____19984
      | uu____20008 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20030 = lookup_qname env lid  in
      match uu____20030 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20035,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20038;
              FStar_Syntax_Syntax.sigquals = uu____20039;
              FStar_Syntax_Syntax.sigmeta = uu____20040;
              FStar_Syntax_Syntax.sigattrs = uu____20041;
              FStar_Syntax_Syntax.sigopts = uu____20042;_},FStar_Pervasives_Native.None
            ),uu____20043)
          ->
          let uu____20094 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20094 (uvs, t)
      | uu____20099 ->
          let uu____20100 = name_not_found lid  in
          let uu____20106 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20100 uu____20106
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20126 = lookup_qname env lid  in
      match uu____20126 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20131,uvs,t,uu____20134,uu____20135,uu____20136);
              FStar_Syntax_Syntax.sigrng = uu____20137;
              FStar_Syntax_Syntax.sigquals = uu____20138;
              FStar_Syntax_Syntax.sigmeta = uu____20139;
              FStar_Syntax_Syntax.sigattrs = uu____20140;
              FStar_Syntax_Syntax.sigopts = uu____20141;_},FStar_Pervasives_Native.None
            ),uu____20142)
          ->
          let uu____20199 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20199 (uvs, t)
      | uu____20204 ->
          let uu____20205 = name_not_found lid  in
          let uu____20211 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20205 uu____20211
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20234 = lookup_qname env lid  in
      match uu____20234 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20242,uu____20243,uu____20244,uu____20245,uu____20246,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20248;
              FStar_Syntax_Syntax.sigquals = uu____20249;
              FStar_Syntax_Syntax.sigmeta = uu____20250;
              FStar_Syntax_Syntax.sigattrs = uu____20251;
              FStar_Syntax_Syntax.sigopts = uu____20252;_},uu____20253),uu____20254)
          -> (true, dcs)
      | uu____20319 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20335 = lookup_qname env lid  in
      match uu____20335 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20336,uu____20337,uu____20338,l,uu____20340,uu____20341);
              FStar_Syntax_Syntax.sigrng = uu____20342;
              FStar_Syntax_Syntax.sigquals = uu____20343;
              FStar_Syntax_Syntax.sigmeta = uu____20344;
              FStar_Syntax_Syntax.sigattrs = uu____20345;
              FStar_Syntax_Syntax.sigopts = uu____20346;_},uu____20347),uu____20348)
          -> l
      | uu____20407 ->
          let uu____20408 =
            let uu____20410 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20410  in
          failwith uu____20408
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20480)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20537) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20561 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20561
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20596 -> FStar_Pervasives_Native.None)
          | uu____20605 -> FStar_Pervasives_Native.None
  
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
        let uu____20667 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20667
  
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
        let uu____20700 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20700
  
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
             (FStar_Util.Inl uu____20752,uu____20753) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20802),uu____20803) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20852 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20870 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20880 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20897 ->
                  let uu____20904 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20904
              | FStar_Syntax_Syntax.Sig_let ((uu____20905,lbs),uu____20907)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20923 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20923
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20930 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20946 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20956 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20957 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20964 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20965 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20966 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20979 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20980 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21008 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____21008
           (fun d_opt  ->
              let uu____21021 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____21021
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21031 =
                   let uu____21034 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21034  in
                 match uu____21031 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21035 =
                       let uu____21037 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21037
                        in
                     failwith uu____21035
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21042 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21042
                       then
                         let uu____21045 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21047 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21049 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21045 uu____21047 uu____21049
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
        (FStar_Util.Inr (se,uu____21074),uu____21075) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21124 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21146),uu____21147) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21196 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21218 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21218
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21251 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21251 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21273 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21282 =
                        let uu____21283 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21283.FStar_Syntax_Syntax.n  in
                      match uu____21282 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21288 -> false))
               in
            (true, uu____21273)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21311 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21311
  
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
          let uu____21383 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21383.FStar_Ident.str  in
        let uu____21384 = FStar_Util.smap_try_find tab s  in
        match uu____21384 with
        | FStar_Pervasives_Native.None  ->
            let uu____21387 = f ()  in
            (match uu____21387 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21425 =
        let uu____21426 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21426 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21460 =
        let uu____21461 = FStar_Syntax_Util.unrefine t  in
        uu____21461.FStar_Syntax_Syntax.n  in
      match uu____21460 with
      | FStar_Syntax_Syntax.Tm_type uu____21465 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21469) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21495) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21500,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21522 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21555 =
        let attrs =
          let uu____21561 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21561  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21601 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21601)
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
      let uu____21646 = lookup_qname env ftv  in
      match uu____21646 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21650) ->
          let uu____21695 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21695 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21716,t),r) ->
               let uu____21731 =
                 let uu____21732 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21732 t  in
               FStar_Pervasives_Native.Some uu____21731)
      | uu____21733 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21745 = try_lookup_effect_lid env ftv  in
      match uu____21745 with
      | FStar_Pervasives_Native.None  ->
          let uu____21748 = name_not_found ftv  in
          let uu____21754 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21748 uu____21754
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
        let uu____21778 = lookup_qname env lid0  in
        match uu____21778 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21789);
                FStar_Syntax_Syntax.sigrng = uu____21790;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21792;
                FStar_Syntax_Syntax.sigattrs = uu____21793;
                FStar_Syntax_Syntax.sigopts = uu____21794;_},FStar_Pervasives_Native.None
              ),uu____21795)
            ->
            let lid1 =
              let uu____21851 =
                let uu____21852 = FStar_Ident.range_of_lid lid  in
                let uu____21853 =
                  let uu____21854 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21854  in
                FStar_Range.set_use_range uu____21852 uu____21853  in
              FStar_Ident.set_lid_range lid uu____21851  in
            let uu____21855 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21861  ->
                      match uu___6_21861 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21864 -> false))
               in
            if uu____21855
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21883 =
                      let uu____21885 =
                        let uu____21887 = get_range env  in
                        FStar_Range.string_of_range uu____21887  in
                      let uu____21888 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21890 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21885 uu____21888 uu____21890
                       in
                    failwith uu____21883)
                  in
               match (binders, univs1) with
               | ([],uu____21911) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21937,uu____21938::uu____21939::uu____21940) ->
                   let uu____21961 =
                     let uu____21963 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21965 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21963 uu____21965
                      in
                   failwith uu____21961
               | uu____21976 ->
                   let uu____21991 =
                     let uu____21996 =
                       let uu____21997 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21997)  in
                     inst_tscheme_with uu____21996 insts  in
                   (match uu____21991 with
                    | (uu____22010,t) ->
                        let t1 =
                          let uu____22013 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____22013 t  in
                        let uu____22014 =
                          let uu____22015 = FStar_Syntax_Subst.compress t1
                             in
                          uu____22015.FStar_Syntax_Syntax.n  in
                        (match uu____22014 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22050 -> failwith "Impossible")))
        | uu____22058 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22082 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22082 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22095,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22102 = find1 l2  in
            (match uu____22102 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22109 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22109 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22113 = find1 l  in
            (match uu____22113 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22118 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22118
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22139 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22139 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22145) ->
            FStar_List.length bs
        | uu____22184 ->
            let uu____22185 =
              let uu____22191 =
                let uu____22193 = FStar_Ident.string_of_lid name  in
                let uu____22195 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22193 uu____22195
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22191)
               in
            FStar_Errors.raise_error uu____22185 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22214 = lookup_qname env l1  in
      match uu____22214 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22217;
              FStar_Syntax_Syntax.sigrng = uu____22218;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22220;
              FStar_Syntax_Syntax.sigattrs = uu____22221;
              FStar_Syntax_Syntax.sigopts = uu____22222;_},uu____22223),uu____22224)
          -> q
      | uu____22277 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22301 =
          let uu____22302 =
            let uu____22304 = FStar_Util.string_of_int i  in
            let uu____22306 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22304 uu____22306
             in
          failwith uu____22302  in
        let uu____22309 = lookup_datacon env lid  in
        match uu____22309 with
        | (uu____22314,t) ->
            let uu____22316 =
              let uu____22317 = FStar_Syntax_Subst.compress t  in
              uu____22317.FStar_Syntax_Syntax.n  in
            (match uu____22316 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22321) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22367 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22381 = lookup_qname env l  in
      match uu____22381 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22383,uu____22384,uu____22385);
              FStar_Syntax_Syntax.sigrng = uu____22386;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22388;
              FStar_Syntax_Syntax.sigattrs = uu____22389;
              FStar_Syntax_Syntax.sigopts = uu____22390;_},uu____22391),uu____22392)
          ->
          FStar_Util.for_some
            (fun uu___7_22447  ->
               match uu___7_22447 with
               | FStar_Syntax_Syntax.Projector uu____22449 -> true
               | uu____22455 -> false) quals
      | uu____22457 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22471 = lookup_qname env lid  in
      match uu____22471 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22473,uu____22474,uu____22475,uu____22476,uu____22477,uu____22478);
              FStar_Syntax_Syntax.sigrng = uu____22479;
              FStar_Syntax_Syntax.sigquals = uu____22480;
              FStar_Syntax_Syntax.sigmeta = uu____22481;
              FStar_Syntax_Syntax.sigattrs = uu____22482;
              FStar_Syntax_Syntax.sigopts = uu____22483;_},uu____22484),uu____22485)
          -> true
      | uu____22545 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22559 = lookup_qname env lid  in
      match uu____22559 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22561,uu____22562,uu____22563,uu____22564,uu____22565,uu____22566);
              FStar_Syntax_Syntax.sigrng = uu____22567;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22569;
              FStar_Syntax_Syntax.sigattrs = uu____22570;
              FStar_Syntax_Syntax.sigopts = uu____22571;_},uu____22572),uu____22573)
          ->
          FStar_Util.for_some
            (fun uu___8_22636  ->
               match uu___8_22636 with
               | FStar_Syntax_Syntax.RecordType uu____22638 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22648 -> true
               | uu____22658 -> false) quals
      | uu____22660 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22670,uu____22671);
            FStar_Syntax_Syntax.sigrng = uu____22672;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22674;
            FStar_Syntax_Syntax.sigattrs = uu____22675;
            FStar_Syntax_Syntax.sigopts = uu____22676;_},uu____22677),uu____22678)
        ->
        FStar_Util.for_some
          (fun uu___9_22737  ->
             match uu___9_22737 with
             | FStar_Syntax_Syntax.Action uu____22739 -> true
             | uu____22741 -> false) quals
    | uu____22743 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22757 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22757
  
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
      let uu____22774 =
        let uu____22775 = FStar_Syntax_Util.un_uinst head1  in
        uu____22775.FStar_Syntax_Syntax.n  in
      match uu____22774 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22781 ->
               true
           | uu____22784 -> false)
      | uu____22786 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22800 = lookup_qname env l  in
      match uu____22800 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22803),uu____22804) ->
          FStar_Util.for_some
            (fun uu___10_22852  ->
               match uu___10_22852 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22855 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22857 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22933 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22951) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22969 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22977 ->
                 FStar_Pervasives_Native.Some true
             | uu____22996 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22999 =
        let uu____23003 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____23003 mapper  in
      match uu____22999 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23063 = lookup_qname env lid  in
      match uu____23063 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23067,uu____23068,tps,uu____23070,uu____23071,uu____23072);
              FStar_Syntax_Syntax.sigrng = uu____23073;
              FStar_Syntax_Syntax.sigquals = uu____23074;
              FStar_Syntax_Syntax.sigmeta = uu____23075;
              FStar_Syntax_Syntax.sigattrs = uu____23076;
              FStar_Syntax_Syntax.sigopts = uu____23077;_},uu____23078),uu____23079)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23147 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23193  ->
              match uu____23193 with
              | (d,uu____23202) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23218 = effect_decl_opt env l  in
      match uu____23218 with
      | FStar_Pervasives_Native.None  ->
          let uu____23233 = name_not_found l  in
          let uu____23239 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23233 uu____23239
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23267 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23267 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23274  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23288  ->
            fun uu____23289  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23323 = FStar_Ident.lid_equals l1 l2  in
        if uu____23323
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23342 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23342
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23361 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23414  ->
                        match uu____23414 with
                        | (m1,m2,uu____23428,uu____23429,uu____23430) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23361 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23455,uu____23456,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23504 = join_opt env l1 l2  in
        match uu____23504 with
        | FStar_Pervasives_Native.None  ->
            let uu____23525 =
              let uu____23531 =
                let uu____23533 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23535 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23533 uu____23535
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23531)  in
            FStar_Errors.raise_error uu____23525 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23578 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23578
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
  'Auu____23598 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23598) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23627 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23653  ->
                match uu____23653 with
                | (d,uu____23660) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23627 with
      | FStar_Pervasives_Native.None  ->
          let uu____23671 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23671
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23686 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23686 with
           | (uu____23697,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23715)::(wp,uu____23717)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23773 -> failwith "Impossible"))
  
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
        | uu____23838 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23851 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23851 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23868 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23868 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23893 =
                     let uu____23899 =
                       let uu____23901 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23909 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23920 =
                         let uu____23922 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23922  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23901 uu____23909 uu____23920
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23899)
                      in
                   FStar_Errors.raise_error uu____23893
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23930 =
                     let uu____23941 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23941 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23978  ->
                        fun uu____23979  ->
                          match (uu____23978, uu____23979) with
                          | ((x,uu____24009),(t,uu____24011)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23930
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____24042 =
                     let uu___1614_24043 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1614_24043.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1614_24043.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1614_24043.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1614_24043.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24042
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24055 .
    'Auu____24055 ->
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
            let uu____24096 =
              let uu____24103 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24103)  in
            match uu____24096 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24127 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24129 = FStar_Util.string_of_int given  in
                     let uu____24131 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24127 uu____24129 uu____24131
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24136 = effect_decl_opt env effect_name  in
          match uu____24136 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24158) ->
              let uu____24169 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24169 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24187 =
                       let uu____24190 = get_range env  in
                       let uu____24191 =
                         let uu____24198 =
                           let uu____24199 =
                             let uu____24216 =
                               let uu____24227 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24227 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24216)  in
                           FStar_Syntax_Syntax.Tm_app uu____24199  in
                         FStar_Syntax_Syntax.mk uu____24198  in
                       uu____24191 FStar_Pervasives_Native.None uu____24190
                        in
                     FStar_Pervasives_Native.Some uu____24187)))
  
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
           (fun uu___11_24327  ->
              match uu___11_24327 with
              | FStar_Syntax_Syntax.Reflectable uu____24329 -> true
              | uu____24331 -> false))
  
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
      | uu____24391 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24406 =
        let uu____24407 = FStar_Syntax_Subst.compress t  in
        uu____24407.FStar_Syntax_Syntax.n  in
      match uu____24406 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24411,c) ->
          is_reifiable_comp env c
      | uu____24433 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24453 =
           let uu____24455 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24455  in
         if uu____24453
         then
           let uu____24458 =
             let uu____24464 =
               let uu____24466 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24466
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24464)  in
           let uu____24470 = get_range env  in
           FStar_Errors.raise_error uu____24458 uu____24470
         else ());
        (let uu____24473 = effect_repr_aux true env c u_c  in
         match uu____24473 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1691_24509 = env  in
        {
          solver = (uu___1691_24509.solver);
          range = (uu___1691_24509.range);
          curmodule = (uu___1691_24509.curmodule);
          gamma = (uu___1691_24509.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1691_24509.gamma_cache);
          modules = (uu___1691_24509.modules);
          expected_typ = (uu___1691_24509.expected_typ);
          sigtab = (uu___1691_24509.sigtab);
          attrtab = (uu___1691_24509.attrtab);
          instantiate_imp = (uu___1691_24509.instantiate_imp);
          effects = (uu___1691_24509.effects);
          generalize = (uu___1691_24509.generalize);
          letrecs = (uu___1691_24509.letrecs);
          top_level = (uu___1691_24509.top_level);
          check_uvars = (uu___1691_24509.check_uvars);
          use_eq = (uu___1691_24509.use_eq);
          use_eq_strict = (uu___1691_24509.use_eq_strict);
          is_iface = (uu___1691_24509.is_iface);
          admit = (uu___1691_24509.admit);
          lax = (uu___1691_24509.lax);
          lax_universes = (uu___1691_24509.lax_universes);
          phase1 = (uu___1691_24509.phase1);
          failhard = (uu___1691_24509.failhard);
          nosynth = (uu___1691_24509.nosynth);
          uvar_subtyping = (uu___1691_24509.uvar_subtyping);
          tc_term = (uu___1691_24509.tc_term);
          type_of = (uu___1691_24509.type_of);
          universe_of = (uu___1691_24509.universe_of);
          check_type_of = (uu___1691_24509.check_type_of);
          use_bv_sorts = (uu___1691_24509.use_bv_sorts);
          qtbl_name_and_index = (uu___1691_24509.qtbl_name_and_index);
          normalized_eff_names = (uu___1691_24509.normalized_eff_names);
          fv_delta_depths = (uu___1691_24509.fv_delta_depths);
          proof_ns = (uu___1691_24509.proof_ns);
          synth_hook = (uu___1691_24509.synth_hook);
          try_solve_implicits_hook =
            (uu___1691_24509.try_solve_implicits_hook);
          splice = (uu___1691_24509.splice);
          mpreprocess = (uu___1691_24509.mpreprocess);
          postprocess = (uu___1691_24509.postprocess);
          is_native_tactic = (uu___1691_24509.is_native_tactic);
          identifier_info = (uu___1691_24509.identifier_info);
          tc_hooks = (uu___1691_24509.tc_hooks);
          dsenv = (uu___1691_24509.dsenv);
          nbe = (uu___1691_24509.nbe);
          strict_args_tab = (uu___1691_24509.strict_args_tab);
          erasable_types_tab = (uu___1691_24509.erasable_types_tab)
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
    fun uu____24528  ->
      match uu____24528 with
      | (ed,quals) ->
          let effects =
            let uu___1700_24542 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1700_24542.order);
              joins = (uu___1700_24542.joins);
              polymonadic_binds = (uu___1700_24542.polymonadic_binds)
            }  in
          let uu___1703_24551 = env  in
          {
            solver = (uu___1703_24551.solver);
            range = (uu___1703_24551.range);
            curmodule = (uu___1703_24551.curmodule);
            gamma = (uu___1703_24551.gamma);
            gamma_sig = (uu___1703_24551.gamma_sig);
            gamma_cache = (uu___1703_24551.gamma_cache);
            modules = (uu___1703_24551.modules);
            expected_typ = (uu___1703_24551.expected_typ);
            sigtab = (uu___1703_24551.sigtab);
            attrtab = (uu___1703_24551.attrtab);
            instantiate_imp = (uu___1703_24551.instantiate_imp);
            effects;
            generalize = (uu___1703_24551.generalize);
            letrecs = (uu___1703_24551.letrecs);
            top_level = (uu___1703_24551.top_level);
            check_uvars = (uu___1703_24551.check_uvars);
            use_eq = (uu___1703_24551.use_eq);
            use_eq_strict = (uu___1703_24551.use_eq_strict);
            is_iface = (uu___1703_24551.is_iface);
            admit = (uu___1703_24551.admit);
            lax = (uu___1703_24551.lax);
            lax_universes = (uu___1703_24551.lax_universes);
            phase1 = (uu___1703_24551.phase1);
            failhard = (uu___1703_24551.failhard);
            nosynth = (uu___1703_24551.nosynth);
            uvar_subtyping = (uu___1703_24551.uvar_subtyping);
            tc_term = (uu___1703_24551.tc_term);
            type_of = (uu___1703_24551.type_of);
            universe_of = (uu___1703_24551.universe_of);
            check_type_of = (uu___1703_24551.check_type_of);
            use_bv_sorts = (uu___1703_24551.use_bv_sorts);
            qtbl_name_and_index = (uu___1703_24551.qtbl_name_and_index);
            normalized_eff_names = (uu___1703_24551.normalized_eff_names);
            fv_delta_depths = (uu___1703_24551.fv_delta_depths);
            proof_ns = (uu___1703_24551.proof_ns);
            synth_hook = (uu___1703_24551.synth_hook);
            try_solve_implicits_hook =
              (uu___1703_24551.try_solve_implicits_hook);
            splice = (uu___1703_24551.splice);
            mpreprocess = (uu___1703_24551.mpreprocess);
            postprocess = (uu___1703_24551.postprocess);
            is_native_tactic = (uu___1703_24551.is_native_tactic);
            identifier_info = (uu___1703_24551.identifier_info);
            tc_hooks = (uu___1703_24551.tc_hooks);
            dsenv = (uu___1703_24551.dsenv);
            nbe = (uu___1703_24551.nbe);
            strict_args_tab = (uu___1703_24551.strict_args_tab);
            erasable_types_tab = (uu___1703_24551.erasable_types_tab)
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
        let uu____24580 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24648  ->
                  match uu____24648 with
                  | (m1,n11,uu____24666,uu____24667) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24580 with
        | FStar_Pervasives_Native.Some (uu____24692,uu____24693,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24738 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24813 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24813
                  (fun uu____24834  ->
                     match uu____24834 with
                     | (c1,g1) ->
                         let uu____24845 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24845
                           (fun uu____24866  ->
                              match uu____24866 with
                              | (c2,g2) ->
                                  let uu____24877 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24877)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24999 = l1 u t e  in
                              l2 u t uu____24999))
                | uu____25000 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25068  ->
                    match uu____25068 with
                    | (e,uu____25076) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25099 =
            match uu____25099 with
            | (i,j) ->
                let uu____25110 = FStar_Ident.lid_equals i j  in
                if uu____25110
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25117  -> FStar_Pervasives_Native.Some _25117)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25146 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25156 = FStar_Ident.lid_equals i k  in
                        if uu____25156
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25170 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25170
                                  then []
                                  else
                                    (let uu____25177 =
                                       let uu____25186 =
                                         find_edge order1 (i, k)  in
                                       let uu____25189 =
                                         find_edge order1 (k, j)  in
                                       (uu____25186, uu____25189)  in
                                     match uu____25177 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25204 =
                                           compose_edges e1 e2  in
                                         [uu____25204]
                                     | uu____25205 -> [])))))
                 in
              FStar_List.append order1 uu____25146  in
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
                  let uu____25235 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25238 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25238
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25235
                  then
                    let uu____25245 =
                      let uu____25251 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25251)
                       in
                    let uu____25255 = get_range env  in
                    FStar_Errors.raise_error uu____25245 uu____25255
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25333 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25333
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25385 =
                                             let uu____25394 =
                                               find_edge order2 (i, k)  in
                                             let uu____25397 =
                                               find_edge order2 (j, k)  in
                                             (uu____25394, uu____25397)  in
                                           match uu____25385 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25439,uu____25440)
                                                    ->
                                                    let uu____25447 =
                                                      let uu____25454 =
                                                        let uu____25456 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25456
                                                         in
                                                      let uu____25459 =
                                                        let uu____25461 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25461
                                                         in
                                                      (uu____25454,
                                                        uu____25459)
                                                       in
                                                    (match uu____25447 with
                                                     | (true ,true ) ->
                                                         let uu____25478 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25478
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
                                           | uu____25521 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25573 =
                                   let uu____25575 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25575
                                     FStar_Util.is_some
                                    in
                                 if uu____25573
                                 then
                                   let uu____25624 =
                                     let uu____25630 =
                                       let uu____25632 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25634 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25636 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25638 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25632 uu____25634 uu____25636
                                         uu____25638
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25630)
                                      in
                                   FStar_Errors.raise_error uu____25624
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1824_25677 = env.effects  in
             {
               decls = (uu___1824_25677.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1824_25677.polymonadic_binds)
             }  in
           let uu___1827_25678 = env  in
           {
             solver = (uu___1827_25678.solver);
             range = (uu___1827_25678.range);
             curmodule = (uu___1827_25678.curmodule);
             gamma = (uu___1827_25678.gamma);
             gamma_sig = (uu___1827_25678.gamma_sig);
             gamma_cache = (uu___1827_25678.gamma_cache);
             modules = (uu___1827_25678.modules);
             expected_typ = (uu___1827_25678.expected_typ);
             sigtab = (uu___1827_25678.sigtab);
             attrtab = (uu___1827_25678.attrtab);
             instantiate_imp = (uu___1827_25678.instantiate_imp);
             effects;
             generalize = (uu___1827_25678.generalize);
             letrecs = (uu___1827_25678.letrecs);
             top_level = (uu___1827_25678.top_level);
             check_uvars = (uu___1827_25678.check_uvars);
             use_eq = (uu___1827_25678.use_eq);
             use_eq_strict = (uu___1827_25678.use_eq_strict);
             is_iface = (uu___1827_25678.is_iface);
             admit = (uu___1827_25678.admit);
             lax = (uu___1827_25678.lax);
             lax_universes = (uu___1827_25678.lax_universes);
             phase1 = (uu___1827_25678.phase1);
             failhard = (uu___1827_25678.failhard);
             nosynth = (uu___1827_25678.nosynth);
             uvar_subtyping = (uu___1827_25678.uvar_subtyping);
             tc_term = (uu___1827_25678.tc_term);
             type_of = (uu___1827_25678.type_of);
             universe_of = (uu___1827_25678.universe_of);
             check_type_of = (uu___1827_25678.check_type_of);
             use_bv_sorts = (uu___1827_25678.use_bv_sorts);
             qtbl_name_and_index = (uu___1827_25678.qtbl_name_and_index);
             normalized_eff_names = (uu___1827_25678.normalized_eff_names);
             fv_delta_depths = (uu___1827_25678.fv_delta_depths);
             proof_ns = (uu___1827_25678.proof_ns);
             synth_hook = (uu___1827_25678.synth_hook);
             try_solve_implicits_hook =
               (uu___1827_25678.try_solve_implicits_hook);
             splice = (uu___1827_25678.splice);
             mpreprocess = (uu___1827_25678.mpreprocess);
             postprocess = (uu___1827_25678.postprocess);
             is_native_tactic = (uu___1827_25678.is_native_tactic);
             identifier_info = (uu___1827_25678.identifier_info);
             tc_hooks = (uu___1827_25678.tc_hooks);
             dsenv = (uu___1827_25678.dsenv);
             nbe = (uu___1827_25678.nbe);
             strict_args_tab = (uu___1827_25678.strict_args_tab);
             erasable_types_tab = (uu___1827_25678.erasable_types_tab)
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
              let uu____25726 = FStar_Ident.string_of_lid m  in
              let uu____25728 = FStar_Ident.string_of_lid n1  in
              let uu____25730 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25726 uu____25728 uu____25730
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25739 =
              let uu____25741 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25741 FStar_Util.is_some  in
            if uu____25739
            then
              let uu____25778 =
                let uu____25784 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25784)
                 in
              FStar_Errors.raise_error uu____25778 env.range
            else
              (let uu____25790 =
                 let uu____25792 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25792 FStar_Util.is_some  in
               if uu____25790
               then
                 let uu____25817 =
                   let uu____25823 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25823)
                    in
                 FStar_Errors.raise_error uu____25817 env.range
               else
                 (let uu___1842_25829 = env  in
                  {
                    solver = (uu___1842_25829.solver);
                    range = (uu___1842_25829.range);
                    curmodule = (uu___1842_25829.curmodule);
                    gamma = (uu___1842_25829.gamma);
                    gamma_sig = (uu___1842_25829.gamma_sig);
                    gamma_cache = (uu___1842_25829.gamma_cache);
                    modules = (uu___1842_25829.modules);
                    expected_typ = (uu___1842_25829.expected_typ);
                    sigtab = (uu___1842_25829.sigtab);
                    attrtab = (uu___1842_25829.attrtab);
                    instantiate_imp = (uu___1842_25829.instantiate_imp);
                    effects =
                      (let uu___1844_25831 = env.effects  in
                       {
                         decls = (uu___1844_25831.decls);
                         order = (uu___1844_25831.order);
                         joins = (uu___1844_25831.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1842_25829.generalize);
                    letrecs = (uu___1842_25829.letrecs);
                    top_level = (uu___1842_25829.top_level);
                    check_uvars = (uu___1842_25829.check_uvars);
                    use_eq = (uu___1842_25829.use_eq);
                    use_eq_strict = (uu___1842_25829.use_eq_strict);
                    is_iface = (uu___1842_25829.is_iface);
                    admit = (uu___1842_25829.admit);
                    lax = (uu___1842_25829.lax);
                    lax_universes = (uu___1842_25829.lax_universes);
                    phase1 = (uu___1842_25829.phase1);
                    failhard = (uu___1842_25829.failhard);
                    nosynth = (uu___1842_25829.nosynth);
                    uvar_subtyping = (uu___1842_25829.uvar_subtyping);
                    tc_term = (uu___1842_25829.tc_term);
                    type_of = (uu___1842_25829.type_of);
                    universe_of = (uu___1842_25829.universe_of);
                    check_type_of = (uu___1842_25829.check_type_of);
                    use_bv_sorts = (uu___1842_25829.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1842_25829.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1842_25829.normalized_eff_names);
                    fv_delta_depths = (uu___1842_25829.fv_delta_depths);
                    proof_ns = (uu___1842_25829.proof_ns);
                    synth_hook = (uu___1842_25829.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1842_25829.try_solve_implicits_hook);
                    splice = (uu___1842_25829.splice);
                    mpreprocess = (uu___1842_25829.mpreprocess);
                    postprocess = (uu___1842_25829.postprocess);
                    is_native_tactic = (uu___1842_25829.is_native_tactic);
                    identifier_info = (uu___1842_25829.identifier_info);
                    tc_hooks = (uu___1842_25829.tc_hooks);
                    dsenv = (uu___1842_25829.dsenv);
                    nbe = (uu___1842_25829.nbe);
                    strict_args_tab = (uu___1842_25829.strict_args_tab);
                    erasable_types_tab = (uu___1842_25829.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1848_25903 = env  in
      {
        solver = (uu___1848_25903.solver);
        range = (uu___1848_25903.range);
        curmodule = (uu___1848_25903.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1848_25903.gamma_sig);
        gamma_cache = (uu___1848_25903.gamma_cache);
        modules = (uu___1848_25903.modules);
        expected_typ = (uu___1848_25903.expected_typ);
        sigtab = (uu___1848_25903.sigtab);
        attrtab = (uu___1848_25903.attrtab);
        instantiate_imp = (uu___1848_25903.instantiate_imp);
        effects = (uu___1848_25903.effects);
        generalize = (uu___1848_25903.generalize);
        letrecs = (uu___1848_25903.letrecs);
        top_level = (uu___1848_25903.top_level);
        check_uvars = (uu___1848_25903.check_uvars);
        use_eq = (uu___1848_25903.use_eq);
        use_eq_strict = (uu___1848_25903.use_eq_strict);
        is_iface = (uu___1848_25903.is_iface);
        admit = (uu___1848_25903.admit);
        lax = (uu___1848_25903.lax);
        lax_universes = (uu___1848_25903.lax_universes);
        phase1 = (uu___1848_25903.phase1);
        failhard = (uu___1848_25903.failhard);
        nosynth = (uu___1848_25903.nosynth);
        uvar_subtyping = (uu___1848_25903.uvar_subtyping);
        tc_term = (uu___1848_25903.tc_term);
        type_of = (uu___1848_25903.type_of);
        universe_of = (uu___1848_25903.universe_of);
        check_type_of = (uu___1848_25903.check_type_of);
        use_bv_sorts = (uu___1848_25903.use_bv_sorts);
        qtbl_name_and_index = (uu___1848_25903.qtbl_name_and_index);
        normalized_eff_names = (uu___1848_25903.normalized_eff_names);
        fv_delta_depths = (uu___1848_25903.fv_delta_depths);
        proof_ns = (uu___1848_25903.proof_ns);
        synth_hook = (uu___1848_25903.synth_hook);
        try_solve_implicits_hook = (uu___1848_25903.try_solve_implicits_hook);
        splice = (uu___1848_25903.splice);
        mpreprocess = (uu___1848_25903.mpreprocess);
        postprocess = (uu___1848_25903.postprocess);
        is_native_tactic = (uu___1848_25903.is_native_tactic);
        identifier_info = (uu___1848_25903.identifier_info);
        tc_hooks = (uu___1848_25903.tc_hooks);
        dsenv = (uu___1848_25903.dsenv);
        nbe = (uu___1848_25903.nbe);
        strict_args_tab = (uu___1848_25903.strict_args_tab);
        erasable_types_tab = (uu___1848_25903.erasable_types_tab)
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
            (let uu___1861_25961 = env  in
             {
               solver = (uu___1861_25961.solver);
               range = (uu___1861_25961.range);
               curmodule = (uu___1861_25961.curmodule);
               gamma = rest;
               gamma_sig = (uu___1861_25961.gamma_sig);
               gamma_cache = (uu___1861_25961.gamma_cache);
               modules = (uu___1861_25961.modules);
               expected_typ = (uu___1861_25961.expected_typ);
               sigtab = (uu___1861_25961.sigtab);
               attrtab = (uu___1861_25961.attrtab);
               instantiate_imp = (uu___1861_25961.instantiate_imp);
               effects = (uu___1861_25961.effects);
               generalize = (uu___1861_25961.generalize);
               letrecs = (uu___1861_25961.letrecs);
               top_level = (uu___1861_25961.top_level);
               check_uvars = (uu___1861_25961.check_uvars);
               use_eq = (uu___1861_25961.use_eq);
               use_eq_strict = (uu___1861_25961.use_eq_strict);
               is_iface = (uu___1861_25961.is_iface);
               admit = (uu___1861_25961.admit);
               lax = (uu___1861_25961.lax);
               lax_universes = (uu___1861_25961.lax_universes);
               phase1 = (uu___1861_25961.phase1);
               failhard = (uu___1861_25961.failhard);
               nosynth = (uu___1861_25961.nosynth);
               uvar_subtyping = (uu___1861_25961.uvar_subtyping);
               tc_term = (uu___1861_25961.tc_term);
               type_of = (uu___1861_25961.type_of);
               universe_of = (uu___1861_25961.universe_of);
               check_type_of = (uu___1861_25961.check_type_of);
               use_bv_sorts = (uu___1861_25961.use_bv_sorts);
               qtbl_name_and_index = (uu___1861_25961.qtbl_name_and_index);
               normalized_eff_names = (uu___1861_25961.normalized_eff_names);
               fv_delta_depths = (uu___1861_25961.fv_delta_depths);
               proof_ns = (uu___1861_25961.proof_ns);
               synth_hook = (uu___1861_25961.synth_hook);
               try_solve_implicits_hook =
                 (uu___1861_25961.try_solve_implicits_hook);
               splice = (uu___1861_25961.splice);
               mpreprocess = (uu___1861_25961.mpreprocess);
               postprocess = (uu___1861_25961.postprocess);
               is_native_tactic = (uu___1861_25961.is_native_tactic);
               identifier_info = (uu___1861_25961.identifier_info);
               tc_hooks = (uu___1861_25961.tc_hooks);
               dsenv = (uu___1861_25961.dsenv);
               nbe = (uu___1861_25961.nbe);
               strict_args_tab = (uu___1861_25961.strict_args_tab);
               erasable_types_tab = (uu___1861_25961.erasable_types_tab)
             }))
    | uu____25962 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25991  ->
             match uu____25991 with | (x,uu____25999) -> push_bv env1 x) env
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
            let uu___1875_26034 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1875_26034.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1875_26034.FStar_Syntax_Syntax.index);
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
        let uu____26107 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26107 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26135 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26135)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1896_26151 = env  in
      {
        solver = (uu___1896_26151.solver);
        range = (uu___1896_26151.range);
        curmodule = (uu___1896_26151.curmodule);
        gamma = (uu___1896_26151.gamma);
        gamma_sig = (uu___1896_26151.gamma_sig);
        gamma_cache = (uu___1896_26151.gamma_cache);
        modules = (uu___1896_26151.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1896_26151.sigtab);
        attrtab = (uu___1896_26151.attrtab);
        instantiate_imp = (uu___1896_26151.instantiate_imp);
        effects = (uu___1896_26151.effects);
        generalize = (uu___1896_26151.generalize);
        letrecs = (uu___1896_26151.letrecs);
        top_level = (uu___1896_26151.top_level);
        check_uvars = (uu___1896_26151.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1896_26151.use_eq_strict);
        is_iface = (uu___1896_26151.is_iface);
        admit = (uu___1896_26151.admit);
        lax = (uu___1896_26151.lax);
        lax_universes = (uu___1896_26151.lax_universes);
        phase1 = (uu___1896_26151.phase1);
        failhard = (uu___1896_26151.failhard);
        nosynth = (uu___1896_26151.nosynth);
        uvar_subtyping = (uu___1896_26151.uvar_subtyping);
        tc_term = (uu___1896_26151.tc_term);
        type_of = (uu___1896_26151.type_of);
        universe_of = (uu___1896_26151.universe_of);
        check_type_of = (uu___1896_26151.check_type_of);
        use_bv_sorts = (uu___1896_26151.use_bv_sorts);
        qtbl_name_and_index = (uu___1896_26151.qtbl_name_and_index);
        normalized_eff_names = (uu___1896_26151.normalized_eff_names);
        fv_delta_depths = (uu___1896_26151.fv_delta_depths);
        proof_ns = (uu___1896_26151.proof_ns);
        synth_hook = (uu___1896_26151.synth_hook);
        try_solve_implicits_hook = (uu___1896_26151.try_solve_implicits_hook);
        splice = (uu___1896_26151.splice);
        mpreprocess = (uu___1896_26151.mpreprocess);
        postprocess = (uu___1896_26151.postprocess);
        is_native_tactic = (uu___1896_26151.is_native_tactic);
        identifier_info = (uu___1896_26151.identifier_info);
        tc_hooks = (uu___1896_26151.tc_hooks);
        dsenv = (uu___1896_26151.dsenv);
        nbe = (uu___1896_26151.nbe);
        strict_args_tab = (uu___1896_26151.strict_args_tab);
        erasable_types_tab = (uu___1896_26151.erasable_types_tab)
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
    let uu____26182 = expected_typ env_  in
    ((let uu___1903_26188 = env_  in
      {
        solver = (uu___1903_26188.solver);
        range = (uu___1903_26188.range);
        curmodule = (uu___1903_26188.curmodule);
        gamma = (uu___1903_26188.gamma);
        gamma_sig = (uu___1903_26188.gamma_sig);
        gamma_cache = (uu___1903_26188.gamma_cache);
        modules = (uu___1903_26188.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1903_26188.sigtab);
        attrtab = (uu___1903_26188.attrtab);
        instantiate_imp = (uu___1903_26188.instantiate_imp);
        effects = (uu___1903_26188.effects);
        generalize = (uu___1903_26188.generalize);
        letrecs = (uu___1903_26188.letrecs);
        top_level = (uu___1903_26188.top_level);
        check_uvars = (uu___1903_26188.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1903_26188.use_eq_strict);
        is_iface = (uu___1903_26188.is_iface);
        admit = (uu___1903_26188.admit);
        lax = (uu___1903_26188.lax);
        lax_universes = (uu___1903_26188.lax_universes);
        phase1 = (uu___1903_26188.phase1);
        failhard = (uu___1903_26188.failhard);
        nosynth = (uu___1903_26188.nosynth);
        uvar_subtyping = (uu___1903_26188.uvar_subtyping);
        tc_term = (uu___1903_26188.tc_term);
        type_of = (uu___1903_26188.type_of);
        universe_of = (uu___1903_26188.universe_of);
        check_type_of = (uu___1903_26188.check_type_of);
        use_bv_sorts = (uu___1903_26188.use_bv_sorts);
        qtbl_name_and_index = (uu___1903_26188.qtbl_name_and_index);
        normalized_eff_names = (uu___1903_26188.normalized_eff_names);
        fv_delta_depths = (uu___1903_26188.fv_delta_depths);
        proof_ns = (uu___1903_26188.proof_ns);
        synth_hook = (uu___1903_26188.synth_hook);
        try_solve_implicits_hook = (uu___1903_26188.try_solve_implicits_hook);
        splice = (uu___1903_26188.splice);
        mpreprocess = (uu___1903_26188.mpreprocess);
        postprocess = (uu___1903_26188.postprocess);
        is_native_tactic = (uu___1903_26188.is_native_tactic);
        identifier_info = (uu___1903_26188.identifier_info);
        tc_hooks = (uu___1903_26188.tc_hooks);
        dsenv = (uu___1903_26188.dsenv);
        nbe = (uu___1903_26188.nbe);
        strict_args_tab = (uu___1903_26188.strict_args_tab);
        erasable_types_tab = (uu___1903_26188.erasable_types_tab)
      }), uu____26182)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26200 =
      let uu____26203 = FStar_Ident.id_of_text ""  in [uu____26203]  in
    FStar_Ident.lid_of_ids uu____26200  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26210 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26210
        then
          let uu____26215 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26215 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1911_26243 = env  in
       {
         solver = (uu___1911_26243.solver);
         range = (uu___1911_26243.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1911_26243.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1911_26243.expected_typ);
         sigtab = (uu___1911_26243.sigtab);
         attrtab = (uu___1911_26243.attrtab);
         instantiate_imp = (uu___1911_26243.instantiate_imp);
         effects = (uu___1911_26243.effects);
         generalize = (uu___1911_26243.generalize);
         letrecs = (uu___1911_26243.letrecs);
         top_level = (uu___1911_26243.top_level);
         check_uvars = (uu___1911_26243.check_uvars);
         use_eq = (uu___1911_26243.use_eq);
         use_eq_strict = (uu___1911_26243.use_eq_strict);
         is_iface = (uu___1911_26243.is_iface);
         admit = (uu___1911_26243.admit);
         lax = (uu___1911_26243.lax);
         lax_universes = (uu___1911_26243.lax_universes);
         phase1 = (uu___1911_26243.phase1);
         failhard = (uu___1911_26243.failhard);
         nosynth = (uu___1911_26243.nosynth);
         uvar_subtyping = (uu___1911_26243.uvar_subtyping);
         tc_term = (uu___1911_26243.tc_term);
         type_of = (uu___1911_26243.type_of);
         universe_of = (uu___1911_26243.universe_of);
         check_type_of = (uu___1911_26243.check_type_of);
         use_bv_sorts = (uu___1911_26243.use_bv_sorts);
         qtbl_name_and_index = (uu___1911_26243.qtbl_name_and_index);
         normalized_eff_names = (uu___1911_26243.normalized_eff_names);
         fv_delta_depths = (uu___1911_26243.fv_delta_depths);
         proof_ns = (uu___1911_26243.proof_ns);
         synth_hook = (uu___1911_26243.synth_hook);
         try_solve_implicits_hook =
           (uu___1911_26243.try_solve_implicits_hook);
         splice = (uu___1911_26243.splice);
         mpreprocess = (uu___1911_26243.mpreprocess);
         postprocess = (uu___1911_26243.postprocess);
         is_native_tactic = (uu___1911_26243.is_native_tactic);
         identifier_info = (uu___1911_26243.identifier_info);
         tc_hooks = (uu___1911_26243.tc_hooks);
         dsenv = (uu___1911_26243.dsenv);
         nbe = (uu___1911_26243.nbe);
         strict_args_tab = (uu___1911_26243.strict_args_tab);
         erasable_types_tab = (uu___1911_26243.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26295)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26299,(uu____26300,t)))::tl1
          ->
          let uu____26321 =
            let uu____26324 = FStar_Syntax_Free.uvars t  in
            ext out uu____26324  in
          aux uu____26321 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26327;
            FStar_Syntax_Syntax.index = uu____26328;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26336 =
            let uu____26339 = FStar_Syntax_Free.uvars t  in
            ext out uu____26339  in
          aux uu____26336 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26397)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26401,(uu____26402,t)))::tl1
          ->
          let uu____26423 =
            let uu____26426 = FStar_Syntax_Free.univs t  in
            ext out uu____26426  in
          aux uu____26423 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26429;
            FStar_Syntax_Syntax.index = uu____26430;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26438 =
            let uu____26441 = FStar_Syntax_Free.univs t  in
            ext out uu____26441  in
          aux uu____26438 tl1
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
          let uu____26503 = FStar_Util.set_add uname out  in
          aux uu____26503 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26506,(uu____26507,t)))::tl1
          ->
          let uu____26528 =
            let uu____26531 = FStar_Syntax_Free.univnames t  in
            ext out uu____26531  in
          aux uu____26528 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26534;
            FStar_Syntax_Syntax.index = uu____26535;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26543 =
            let uu____26546 = FStar_Syntax_Free.univnames t  in
            ext out uu____26546  in
          aux uu____26543 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26567  ->
            match uu___12_26567 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26571 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26584 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26595 =
      let uu____26604 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26604
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26595 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26652 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26665  ->
              match uu___13_26665 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26668 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26668
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26674) ->
                  let uu____26691 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26691))
       in
    FStar_All.pipe_right uu____26652 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26705  ->
    match uu___14_26705 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26711 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26711
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26734  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26789) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26822,uu____26823) -> false  in
      let uu____26837 =
        FStar_List.tryFind
          (fun uu____26859  ->
             match uu____26859 with | (p,uu____26870) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26837 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26889,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26919 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26919
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2054_26941 = e  in
        {
          solver = (uu___2054_26941.solver);
          range = (uu___2054_26941.range);
          curmodule = (uu___2054_26941.curmodule);
          gamma = (uu___2054_26941.gamma);
          gamma_sig = (uu___2054_26941.gamma_sig);
          gamma_cache = (uu___2054_26941.gamma_cache);
          modules = (uu___2054_26941.modules);
          expected_typ = (uu___2054_26941.expected_typ);
          sigtab = (uu___2054_26941.sigtab);
          attrtab = (uu___2054_26941.attrtab);
          instantiate_imp = (uu___2054_26941.instantiate_imp);
          effects = (uu___2054_26941.effects);
          generalize = (uu___2054_26941.generalize);
          letrecs = (uu___2054_26941.letrecs);
          top_level = (uu___2054_26941.top_level);
          check_uvars = (uu___2054_26941.check_uvars);
          use_eq = (uu___2054_26941.use_eq);
          use_eq_strict = (uu___2054_26941.use_eq_strict);
          is_iface = (uu___2054_26941.is_iface);
          admit = (uu___2054_26941.admit);
          lax = (uu___2054_26941.lax);
          lax_universes = (uu___2054_26941.lax_universes);
          phase1 = (uu___2054_26941.phase1);
          failhard = (uu___2054_26941.failhard);
          nosynth = (uu___2054_26941.nosynth);
          uvar_subtyping = (uu___2054_26941.uvar_subtyping);
          tc_term = (uu___2054_26941.tc_term);
          type_of = (uu___2054_26941.type_of);
          universe_of = (uu___2054_26941.universe_of);
          check_type_of = (uu___2054_26941.check_type_of);
          use_bv_sorts = (uu___2054_26941.use_bv_sorts);
          qtbl_name_and_index = (uu___2054_26941.qtbl_name_and_index);
          normalized_eff_names = (uu___2054_26941.normalized_eff_names);
          fv_delta_depths = (uu___2054_26941.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2054_26941.synth_hook);
          try_solve_implicits_hook =
            (uu___2054_26941.try_solve_implicits_hook);
          splice = (uu___2054_26941.splice);
          mpreprocess = (uu___2054_26941.mpreprocess);
          postprocess = (uu___2054_26941.postprocess);
          is_native_tactic = (uu___2054_26941.is_native_tactic);
          identifier_info = (uu___2054_26941.identifier_info);
          tc_hooks = (uu___2054_26941.tc_hooks);
          dsenv = (uu___2054_26941.dsenv);
          nbe = (uu___2054_26941.nbe);
          strict_args_tab = (uu___2054_26941.strict_args_tab);
          erasable_types_tab = (uu___2054_26941.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2063_26989 = e  in
      {
        solver = (uu___2063_26989.solver);
        range = (uu___2063_26989.range);
        curmodule = (uu___2063_26989.curmodule);
        gamma = (uu___2063_26989.gamma);
        gamma_sig = (uu___2063_26989.gamma_sig);
        gamma_cache = (uu___2063_26989.gamma_cache);
        modules = (uu___2063_26989.modules);
        expected_typ = (uu___2063_26989.expected_typ);
        sigtab = (uu___2063_26989.sigtab);
        attrtab = (uu___2063_26989.attrtab);
        instantiate_imp = (uu___2063_26989.instantiate_imp);
        effects = (uu___2063_26989.effects);
        generalize = (uu___2063_26989.generalize);
        letrecs = (uu___2063_26989.letrecs);
        top_level = (uu___2063_26989.top_level);
        check_uvars = (uu___2063_26989.check_uvars);
        use_eq = (uu___2063_26989.use_eq);
        use_eq_strict = (uu___2063_26989.use_eq_strict);
        is_iface = (uu___2063_26989.is_iface);
        admit = (uu___2063_26989.admit);
        lax = (uu___2063_26989.lax);
        lax_universes = (uu___2063_26989.lax_universes);
        phase1 = (uu___2063_26989.phase1);
        failhard = (uu___2063_26989.failhard);
        nosynth = (uu___2063_26989.nosynth);
        uvar_subtyping = (uu___2063_26989.uvar_subtyping);
        tc_term = (uu___2063_26989.tc_term);
        type_of = (uu___2063_26989.type_of);
        universe_of = (uu___2063_26989.universe_of);
        check_type_of = (uu___2063_26989.check_type_of);
        use_bv_sorts = (uu___2063_26989.use_bv_sorts);
        qtbl_name_and_index = (uu___2063_26989.qtbl_name_and_index);
        normalized_eff_names = (uu___2063_26989.normalized_eff_names);
        fv_delta_depths = (uu___2063_26989.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2063_26989.synth_hook);
        try_solve_implicits_hook = (uu___2063_26989.try_solve_implicits_hook);
        splice = (uu___2063_26989.splice);
        mpreprocess = (uu___2063_26989.mpreprocess);
        postprocess = (uu___2063_26989.postprocess);
        is_native_tactic = (uu___2063_26989.is_native_tactic);
        identifier_info = (uu___2063_26989.identifier_info);
        tc_hooks = (uu___2063_26989.tc_hooks);
        dsenv = (uu___2063_26989.dsenv);
        nbe = (uu___2063_26989.nbe);
        strict_args_tab = (uu___2063_26989.strict_args_tab);
        erasable_types_tab = (uu___2063_26989.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____27005 = FStar_Syntax_Free.names t  in
      let uu____27008 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____27005 uu____27008
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27031 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27031
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27041 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27041
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27062 =
      match uu____27062 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27082 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27082)
       in
    let uu____27090 =
      let uu____27094 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27094 FStar_List.rev  in
    FStar_All.pipe_right uu____27090 (FStar_String.concat " ")
  
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
                  (let uu____27162 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27162 with
                   | FStar_Pervasives_Native.Some uu____27166 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27169 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27179;
        FStar_TypeChecker_Common.univ_ineqs = uu____27180;
        FStar_TypeChecker_Common.implicits = uu____27181;_} -> true
    | uu____27191 -> false
  
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
          let uu___2107_27213 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2107_27213.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2107_27213.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2107_27213.FStar_TypeChecker_Common.implicits)
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
          let uu____27252 = FStar_Options.defensive ()  in
          if uu____27252
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27258 =
              let uu____27260 =
                let uu____27262 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27262  in
              Prims.op_Negation uu____27260  in
            (if uu____27258
             then
               let uu____27269 =
                 let uu____27275 =
                   let uu____27277 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27279 =
                     let uu____27281 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27281
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27277 uu____27279
                    in
                 (FStar_Errors.Warning_Defensive, uu____27275)  in
               FStar_Errors.log_issue rng uu____27269
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
          let uu____27321 =
            let uu____27323 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27323  in
          if uu____27321
          then ()
          else
            (let uu____27328 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27328 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27354 =
            let uu____27356 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27356  in
          if uu____27354
          then ()
          else
            (let uu____27361 = bound_vars e  in
             def_check_closed_in rng msg uu____27361 t)
  
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
          let uu___2144_27400 = g  in
          let uu____27401 =
            let uu____27402 =
              let uu____27403 =
                let uu____27410 =
                  let uu____27411 =
                    let uu____27428 =
                      let uu____27439 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27439]  in
                    (f, uu____27428)  in
                  FStar_Syntax_Syntax.Tm_app uu____27411  in
                FStar_Syntax_Syntax.mk uu____27410  in
              uu____27403 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27476  -> FStar_TypeChecker_Common.NonTrivial _27476)
              uu____27402
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27401;
            FStar_TypeChecker_Common.deferred =
              (uu___2144_27400.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2144_27400.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2144_27400.FStar_TypeChecker_Common.implicits)
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
          let uu___2151_27494 = g  in
          let uu____27495 =
            let uu____27496 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27496  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27495;
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27494.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27494.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27494.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2156_27513 = g  in
          let uu____27514 =
            let uu____27515 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27515  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27514;
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27513.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27513.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27513.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2160_27517 = g  in
          let uu____27518 =
            let uu____27519 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27519  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27518;
            FStar_TypeChecker_Common.deferred =
              (uu___2160_27517.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2160_27517.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2160_27517.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27526 ->
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
                       let uu____27603 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27603
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2183_27610 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2183_27610.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2183_27610.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2183_27610.FStar_TypeChecker_Common.implicits)
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
               let uu____27644 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27644
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
            let uu___2198_27671 = g  in
            let uu____27672 =
              let uu____27673 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27673  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27672;
              FStar_TypeChecker_Common.deferred =
                (uu___2198_27671.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2198_27671.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2198_27671.FStar_TypeChecker_Common.implicits)
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
              let uu____27731 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27731 with
              | FStar_Pervasives_Native.Some
                  (uu____27756::(tm,uu____27758)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27822 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27840 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27840;
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
                    (let uu____27872 =
                       debug env (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27872
                     then
                       let uu____27876 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27876
                     else ());
                    (let g =
                       let uu___2222_27882 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2222_27882.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2222_27882.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2222_27882.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27936 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27993  ->
                      fun b  ->
                        match uu____27993 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____28035 =
                              let uu____28048 = reason b  in
                              new_implicit_var_aux uu____28048 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____28035 with
                             | (t,uu____28065,g_t) ->
                                 let uu____28079 =
                                   let uu____28082 =
                                     let uu____28085 =
                                       let uu____28086 =
                                         let uu____28093 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28093, t)  in
                                       FStar_Syntax_Syntax.NT uu____28086  in
                                     [uu____28085]  in
                                   FStar_List.append substs1 uu____28082  in
                                 let uu____28104 = conj_guard g g_t  in
                                 (uu____28079,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28104))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27936
              (fun uu____28133  ->
                 match uu____28133 with
                 | (uu____28150,uvars1,g) -> (uvars1, g))
  
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
                let uu____28191 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28191 FStar_Util.must  in
              let uu____28208 = inst_tscheme_with post_ts [u]  in
              match uu____28208 with
              | (uu____28213,post) ->
                  let uu____28215 =
                    let uu____28220 =
                      let uu____28221 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28221]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28220  in
                  uu____28215 FStar_Pervasives_Native.None r
               in
            let uu____28254 =
              let uu____28259 =
                let uu____28260 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28260]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28259  in
            uu____28254 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28296  -> ());
    push = (fun uu____28298  -> ());
    pop = (fun uu____28301  -> ());
    snapshot =
      (fun uu____28304  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28323  -> fun uu____28324  -> ());
    encode_sig = (fun uu____28339  -> fun uu____28340  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28346 =
             let uu____28353 = FStar_Options.peek ()  in (e, g, uu____28353)
              in
           [uu____28346]);
    solve = (fun uu____28369  -> fun uu____28370  -> fun uu____28371  -> ());
    finish = (fun uu____28378  -> ());
    refresh = (fun uu____28380  -> ())
  } 