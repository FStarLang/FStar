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
  fun projectee  -> match projectee with | Beta  -> true | uu____107 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____118 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____129 -> false 
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ZetaFull  -> true | uu____140 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____152 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____170 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____181 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____192 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____203 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____214 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____225 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____237 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____258 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____285 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____312 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____336 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____347 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____358 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____369 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____380 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____391 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____402 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____413 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____424 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____435 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____446 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____457 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____468 -> false
  
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
      | uu____529 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____555 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____566 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____577 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____589 -> false
  
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
    ;
  polymonadic_subcomps:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
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
    (FStar_Syntax_Syntax.lbname * Prims.int * FStar_Syntax_Syntax.typ *
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
    env ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list
    ;
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
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  strict_args_tab:
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap ;
  erasable_types_tab: Prims.bool FStar_Util.smap ;
  enable_defer_to_tac: Prims.bool }
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
    match projectee with | { msource; mtarget; mlift = mlift1;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift = mlift1;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift = mlift1;_} -> mlift1
  
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        joins
  
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
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        polymonadic_binds
  
let (__proj__Mkeffects__item__polymonadic_subcomps :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds; polymonadic_subcomps;_} ->
        polymonadic_subcomps
  
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> effects1
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * Prims.int * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> use_eq
  
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> use_eq_strict
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> admit
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> lax
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> uvar_subtyping
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> tc_term
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> universe_of
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> splice
  
let (__proj__Mkenv__item__mpreprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> mpreprocess
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> postprocess
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> dsenv
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> nbe
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> erasable_types_tab
  
let (__proj__Mkenv__item__enable_defer_to_tac : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects = effects1;
        generalize; letrecs; top_level; check_uvars; use_eq; use_eq_strict;
        is_iface; admit; lax; lax_universes; phase1; failhard; nosynth;
        uvar_subtyping; tc_term; type_of; universe_of; check_type_of;
        use_bv_sorts; qtbl_name_and_index; normalized_eff_names;
        fv_delta_depths; proof_ns; synth_hook; try_solve_implicits_hook;
        splice; mpreprocess; postprocess; identifier_info; tc_hooks; 
        dsenv; nbe; strict_args_tab; erasable_types_tab;
        enable_defer_to_tac;_} -> enable_defer_to_tac
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> pop
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> snapshot
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit)
  =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> rollback
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> finish
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init; push; pop; snapshot; rollback; encode_sig; preprocess; 
        solve; finish; refresh;_} -> refresh
  
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
  = fun env1  -> fun tau  -> fun tm  -> env1.mpreprocess env1 tau tm 
let (postprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun tau  -> fun ty  -> fun tm  -> env1.postprocess env1 tau ty tm
  
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___0_14667  ->
              match uu___0_14667 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14670 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____14670  in
                  let uu____14671 =
                    let uu____14672 = FStar_Syntax_Subst.compress y  in
                    uu____14672.FStar_Syntax_Syntax.n  in
                  (match uu____14671 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14676 =
                         let uu___330_14677 = y1  in
                         let uu____14678 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___330_14677.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___330_14677.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14678
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14676
                   | uu____14681 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst  ->
    fun env1  ->
      let uu___336_14695 = env1  in
      let uu____14696 = rename_gamma subst env1.gamma  in
      {
        solver = (uu___336_14695.solver);
        range = (uu___336_14695.range);
        curmodule = (uu___336_14695.curmodule);
        gamma = uu____14696;
        gamma_sig = (uu___336_14695.gamma_sig);
        gamma_cache = (uu___336_14695.gamma_cache);
        modules = (uu___336_14695.modules);
        expected_typ = (uu___336_14695.expected_typ);
        sigtab = (uu___336_14695.sigtab);
        attrtab = (uu___336_14695.attrtab);
        instantiate_imp = (uu___336_14695.instantiate_imp);
        effects = (uu___336_14695.effects);
        generalize = (uu___336_14695.generalize);
        letrecs = (uu___336_14695.letrecs);
        top_level = (uu___336_14695.top_level);
        check_uvars = (uu___336_14695.check_uvars);
        use_eq = (uu___336_14695.use_eq);
        use_eq_strict = (uu___336_14695.use_eq_strict);
        is_iface = (uu___336_14695.is_iface);
        admit = (uu___336_14695.admit);
        lax = (uu___336_14695.lax);
        lax_universes = (uu___336_14695.lax_universes);
        phase1 = (uu___336_14695.phase1);
        failhard = (uu___336_14695.failhard);
        nosynth = (uu___336_14695.nosynth);
        uvar_subtyping = (uu___336_14695.uvar_subtyping);
        tc_term = (uu___336_14695.tc_term);
        type_of = (uu___336_14695.type_of);
        universe_of = (uu___336_14695.universe_of);
        check_type_of = (uu___336_14695.check_type_of);
        use_bv_sorts = (uu___336_14695.use_bv_sorts);
        qtbl_name_and_index = (uu___336_14695.qtbl_name_and_index);
        normalized_eff_names = (uu___336_14695.normalized_eff_names);
        fv_delta_depths = (uu___336_14695.fv_delta_depths);
        proof_ns = (uu___336_14695.proof_ns);
        synth_hook = (uu___336_14695.synth_hook);
        try_solve_implicits_hook = (uu___336_14695.try_solve_implicits_hook);
        splice = (uu___336_14695.splice);
        mpreprocess = (uu___336_14695.mpreprocess);
        postprocess = (uu___336_14695.postprocess);
        identifier_info = (uu___336_14695.identifier_info);
        tc_hooks = (uu___336_14695.tc_hooks);
        dsenv = (uu___336_14695.dsenv);
        nbe = (uu___336_14695.nbe);
        strict_args_tab = (uu___336_14695.strict_args_tab);
        erasable_types_tab = (uu___336_14695.erasable_types_tab);
        enable_defer_to_tac = (uu___336_14695.enable_defer_to_tac)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14704  -> fun uu____14705  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___343_14727 = env1  in
      {
        solver = (uu___343_14727.solver);
        range = (uu___343_14727.range);
        curmodule = (uu___343_14727.curmodule);
        gamma = (uu___343_14727.gamma);
        gamma_sig = (uu___343_14727.gamma_sig);
        gamma_cache = (uu___343_14727.gamma_cache);
        modules = (uu___343_14727.modules);
        expected_typ = (uu___343_14727.expected_typ);
        sigtab = (uu___343_14727.sigtab);
        attrtab = (uu___343_14727.attrtab);
        instantiate_imp = (uu___343_14727.instantiate_imp);
        effects = (uu___343_14727.effects);
        generalize = (uu___343_14727.generalize);
        letrecs = (uu___343_14727.letrecs);
        top_level = (uu___343_14727.top_level);
        check_uvars = (uu___343_14727.check_uvars);
        use_eq = (uu___343_14727.use_eq);
        use_eq_strict = (uu___343_14727.use_eq_strict);
        is_iface = (uu___343_14727.is_iface);
        admit = (uu___343_14727.admit);
        lax = (uu___343_14727.lax);
        lax_universes = (uu___343_14727.lax_universes);
        phase1 = (uu___343_14727.phase1);
        failhard = (uu___343_14727.failhard);
        nosynth = (uu___343_14727.nosynth);
        uvar_subtyping = (uu___343_14727.uvar_subtyping);
        tc_term = (uu___343_14727.tc_term);
        type_of = (uu___343_14727.type_of);
        universe_of = (uu___343_14727.universe_of);
        check_type_of = (uu___343_14727.check_type_of);
        use_bv_sorts = (uu___343_14727.use_bv_sorts);
        qtbl_name_and_index = (uu___343_14727.qtbl_name_and_index);
        normalized_eff_names = (uu___343_14727.normalized_eff_names);
        fv_delta_depths = (uu___343_14727.fv_delta_depths);
        proof_ns = (uu___343_14727.proof_ns);
        synth_hook = (uu___343_14727.synth_hook);
        try_solve_implicits_hook = (uu___343_14727.try_solve_implicits_hook);
        splice = (uu___343_14727.splice);
        mpreprocess = (uu___343_14727.mpreprocess);
        postprocess = (uu___343_14727.postprocess);
        identifier_info = (uu___343_14727.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___343_14727.dsenv);
        nbe = (uu___343_14727.nbe);
        strict_args_tab = (uu___343_14727.strict_args_tab);
        erasable_types_tab = (uu___343_14727.erasable_types_tab);
        enable_defer_to_tac = (uu___343_14727.enable_defer_to_tac)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___347_14739 = e  in
      let uu____14740 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___347_14739.solver);
        range = (uu___347_14739.range);
        curmodule = (uu___347_14739.curmodule);
        gamma = (uu___347_14739.gamma);
        gamma_sig = (uu___347_14739.gamma_sig);
        gamma_cache = (uu___347_14739.gamma_cache);
        modules = (uu___347_14739.modules);
        expected_typ = (uu___347_14739.expected_typ);
        sigtab = (uu___347_14739.sigtab);
        attrtab = (uu___347_14739.attrtab);
        instantiate_imp = (uu___347_14739.instantiate_imp);
        effects = (uu___347_14739.effects);
        generalize = (uu___347_14739.generalize);
        letrecs = (uu___347_14739.letrecs);
        top_level = (uu___347_14739.top_level);
        check_uvars = (uu___347_14739.check_uvars);
        use_eq = (uu___347_14739.use_eq);
        use_eq_strict = (uu___347_14739.use_eq_strict);
        is_iface = (uu___347_14739.is_iface);
        admit = (uu___347_14739.admit);
        lax = (uu___347_14739.lax);
        lax_universes = (uu___347_14739.lax_universes);
        phase1 = (uu___347_14739.phase1);
        failhard = (uu___347_14739.failhard);
        nosynth = (uu___347_14739.nosynth);
        uvar_subtyping = (uu___347_14739.uvar_subtyping);
        tc_term = (uu___347_14739.tc_term);
        type_of = (uu___347_14739.type_of);
        universe_of = (uu___347_14739.universe_of);
        check_type_of = (uu___347_14739.check_type_of);
        use_bv_sorts = (uu___347_14739.use_bv_sorts);
        qtbl_name_and_index = (uu___347_14739.qtbl_name_and_index);
        normalized_eff_names = (uu___347_14739.normalized_eff_names);
        fv_delta_depths = (uu___347_14739.fv_delta_depths);
        proof_ns = (uu___347_14739.proof_ns);
        synth_hook = (uu___347_14739.synth_hook);
        try_solve_implicits_hook = (uu___347_14739.try_solve_implicits_hook);
        splice = (uu___347_14739.splice);
        mpreprocess = (uu___347_14739.mpreprocess);
        postprocess = (uu___347_14739.postprocess);
        identifier_info = (uu___347_14739.identifier_info);
        tc_hooks = (uu___347_14739.tc_hooks);
        dsenv = uu____14740;
        nbe = (uu___347_14739.nbe);
        strict_args_tab = (uu___347_14739.strict_args_tab);
        erasable_types_tab = (uu___347_14739.erasable_types_tab);
        enable_defer_to_tac = (uu___347_14739.enable_defer_to_tac)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14757 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____14757)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14772) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14775,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14777,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14780 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14794 . unit -> 'uuuuuu14794 FStar_Util.smap =
  fun uu____14801  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14807 . unit -> 'uuuuuu14807 FStar_Util.smap =
  fun uu____14814  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                fun nbe  ->
                  let uu____14952 = new_gamma_cache ()  in
                  let uu____14955 = new_sigtab ()  in
                  let uu____14958 = new_sigtab ()  in
                  let uu____14965 =
                    let uu____14980 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14980, FStar_Pervasives_Native.None)  in
                  let uu____15001 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____15005 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____15009 = FStar_Options.using_facts_from ()  in
                  let uu____15010 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____15013 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____15014 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____15028 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14952;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14955;
                    attrtab = uu____14958;
                    instantiate_imp = true;
                    effects =
                      {
                        decls = [];
                        order = [];
                        joins = [];
                        polymonadic_binds = [];
                        polymonadic_subcomps = []
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
                    qtbl_name_and_index = uu____14965;
                    normalized_eff_names = uu____15001;
                    fv_delta_depths = uu____15005;
                    proof_ns = uu____15009;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    try_solve_implicits_hook =
                      (fun e  ->
                         fun tau  ->
                           fun imps  -> failwith "no implicit hook available");
                    splice =
                      (fun e  ->
                         fun rng  ->
                           fun tau  -> failwith "no splicer available");
                    mpreprocess =
                      (fun e  ->
                         fun tau  ->
                           fun tm  -> failwith "no preprocessor available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    identifier_info = uu____15010;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____15013;
                    nbe;
                    strict_args_tab = uu____15014;
                    erasable_types_tab = uu____15028;
                    enable_defer_to_tac = true
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env1  -> env1.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env1  -> env1.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env1  -> env1.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env1  -> env1.gamma_cache 
let (query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____15231  ->
    let uu____15232 = FStar_ST.op_Bang query_indices  in
    match uu____15232 with
    | [] -> failwith "Empty query indices!"
    | uu____15287 ->
        let uu____15297 =
          let uu____15307 =
            let uu____15315 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____15315  in
          let uu____15369 = FStar_ST.op_Bang query_indices  in uu____15307 ::
            uu____15369
           in
        FStar_ST.op_Colon_Equals query_indices uu____15297
  
let (pop_query_indices : unit -> unit) =
  fun uu____15465  ->
    let uu____15466 = FStar_ST.op_Bang query_indices  in
    match uu____15466 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15593  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15630  ->
    match uu____15630 with
    | (l,n) ->
        let uu____15640 = FStar_ST.op_Bang query_indices  in
        (match uu____15640 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15762 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15785  ->
    let uu____15786 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15786
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15854 =
       let uu____15857 = FStar_ST.op_Bang stack  in env1 :: uu____15857  in
     FStar_ST.op_Colon_Equals stack uu____15854);
    (let uu___421_15906 = env1  in
     let uu____15907 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15910 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15913 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15920 =
       let uu____15935 =
         let uu____15939 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15939  in
       let uu____15971 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15935, uu____15971)  in
     let uu____16020 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____16023 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____16026 =
       let uu____16029 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____16029  in
     let uu____16049 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____16062 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___421_15906.solver);
       range = (uu___421_15906.range);
       curmodule = (uu___421_15906.curmodule);
       gamma = (uu___421_15906.gamma);
       gamma_sig = (uu___421_15906.gamma_sig);
       gamma_cache = uu____15907;
       modules = (uu___421_15906.modules);
       expected_typ = (uu___421_15906.expected_typ);
       sigtab = uu____15910;
       attrtab = uu____15913;
       instantiate_imp = (uu___421_15906.instantiate_imp);
       effects = (uu___421_15906.effects);
       generalize = (uu___421_15906.generalize);
       letrecs = (uu___421_15906.letrecs);
       top_level = (uu___421_15906.top_level);
       check_uvars = (uu___421_15906.check_uvars);
       use_eq = (uu___421_15906.use_eq);
       use_eq_strict = (uu___421_15906.use_eq_strict);
       is_iface = (uu___421_15906.is_iface);
       admit = (uu___421_15906.admit);
       lax = (uu___421_15906.lax);
       lax_universes = (uu___421_15906.lax_universes);
       phase1 = (uu___421_15906.phase1);
       failhard = (uu___421_15906.failhard);
       nosynth = (uu___421_15906.nosynth);
       uvar_subtyping = (uu___421_15906.uvar_subtyping);
       tc_term = (uu___421_15906.tc_term);
       type_of = (uu___421_15906.type_of);
       universe_of = (uu___421_15906.universe_of);
       check_type_of = (uu___421_15906.check_type_of);
       use_bv_sorts = (uu___421_15906.use_bv_sorts);
       qtbl_name_and_index = uu____15920;
       normalized_eff_names = uu____16020;
       fv_delta_depths = uu____16023;
       proof_ns = (uu___421_15906.proof_ns);
       synth_hook = (uu___421_15906.synth_hook);
       try_solve_implicits_hook = (uu___421_15906.try_solve_implicits_hook);
       splice = (uu___421_15906.splice);
       mpreprocess = (uu___421_15906.mpreprocess);
       postprocess = (uu___421_15906.postprocess);
       identifier_info = uu____16026;
       tc_hooks = (uu___421_15906.tc_hooks);
       dsenv = (uu___421_15906.dsenv);
       nbe = (uu___421_15906.nbe);
       strict_args_tab = uu____16049;
       erasable_types_tab = uu____16062;
       enable_defer_to_tac = (uu___421_15906.enable_defer_to_tac)
     })
  
let (pop_stack : unit -> env) =
  fun uu____16072  ->
    let uu____16073 = FStar_ST.op_Bang stack  in
    match uu____16073 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____16127 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____16217  ->
           let uu____16218 = snapshot_stack env1  in
           match uu____16218 with
           | (stack_depth,env2) ->
               let uu____16252 = snapshot_query_indices ()  in
               (match uu____16252 with
                | (query_indices_depth,()) ->
                    let uu____16285 = (env2.solver).snapshot msg  in
                    (match uu____16285 with
                     | (solver_depth,()) ->
                         let uu____16342 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____16342 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___446_16409 = env2  in
                                 {
                                   solver = (uu___446_16409.solver);
                                   range = (uu___446_16409.range);
                                   curmodule = (uu___446_16409.curmodule);
                                   gamma = (uu___446_16409.gamma);
                                   gamma_sig = (uu___446_16409.gamma_sig);
                                   gamma_cache = (uu___446_16409.gamma_cache);
                                   modules = (uu___446_16409.modules);
                                   expected_typ =
                                     (uu___446_16409.expected_typ);
                                   sigtab = (uu___446_16409.sigtab);
                                   attrtab = (uu___446_16409.attrtab);
                                   instantiate_imp =
                                     (uu___446_16409.instantiate_imp);
                                   effects = (uu___446_16409.effects);
                                   generalize = (uu___446_16409.generalize);
                                   letrecs = (uu___446_16409.letrecs);
                                   top_level = (uu___446_16409.top_level);
                                   check_uvars = (uu___446_16409.check_uvars);
                                   use_eq = (uu___446_16409.use_eq);
                                   use_eq_strict =
                                     (uu___446_16409.use_eq_strict);
                                   is_iface = (uu___446_16409.is_iface);
                                   admit = (uu___446_16409.admit);
                                   lax = (uu___446_16409.lax);
                                   lax_universes =
                                     (uu___446_16409.lax_universes);
                                   phase1 = (uu___446_16409.phase1);
                                   failhard = (uu___446_16409.failhard);
                                   nosynth = (uu___446_16409.nosynth);
                                   uvar_subtyping =
                                     (uu___446_16409.uvar_subtyping);
                                   tc_term = (uu___446_16409.tc_term);
                                   type_of = (uu___446_16409.type_of);
                                   universe_of = (uu___446_16409.universe_of);
                                   check_type_of =
                                     (uu___446_16409.check_type_of);
                                   use_bv_sorts =
                                     (uu___446_16409.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___446_16409.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___446_16409.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___446_16409.fv_delta_depths);
                                   proof_ns = (uu___446_16409.proof_ns);
                                   synth_hook = (uu___446_16409.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___446_16409.try_solve_implicits_hook);
                                   splice = (uu___446_16409.splice);
                                   mpreprocess = (uu___446_16409.mpreprocess);
                                   postprocess = (uu___446_16409.postprocess);
                                   identifier_info =
                                     (uu___446_16409.identifier_info);
                                   tc_hooks = (uu___446_16409.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___446_16409.nbe);
                                   strict_args_tab =
                                     (uu___446_16409.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___446_16409.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___446_16409.enable_defer_to_tac)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16443  ->
             let uu____16444 =
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
             match uu____16444 with
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
                             ((let uu____16624 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16624
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____16640 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____16640
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____16672,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____16714 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16744  ->
                  match uu____16744 with
                  | (m,uu____16752) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16714 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16766 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16766 next);
              (let uu___491_16769 = env1  in
               {
                 solver = (uu___491_16769.solver);
                 range = (uu___491_16769.range);
                 curmodule = (uu___491_16769.curmodule);
                 gamma = (uu___491_16769.gamma);
                 gamma_sig = (uu___491_16769.gamma_sig);
                 gamma_cache = (uu___491_16769.gamma_cache);
                 modules = (uu___491_16769.modules);
                 expected_typ = (uu___491_16769.expected_typ);
                 sigtab = (uu___491_16769.sigtab);
                 attrtab = (uu___491_16769.attrtab);
                 instantiate_imp = (uu___491_16769.instantiate_imp);
                 effects = (uu___491_16769.effects);
                 generalize = (uu___491_16769.generalize);
                 letrecs = (uu___491_16769.letrecs);
                 top_level = (uu___491_16769.top_level);
                 check_uvars = (uu___491_16769.check_uvars);
                 use_eq = (uu___491_16769.use_eq);
                 use_eq_strict = (uu___491_16769.use_eq_strict);
                 is_iface = (uu___491_16769.is_iface);
                 admit = (uu___491_16769.admit);
                 lax = (uu___491_16769.lax);
                 lax_universes = (uu___491_16769.lax_universes);
                 phase1 = (uu___491_16769.phase1);
                 failhard = (uu___491_16769.failhard);
                 nosynth = (uu___491_16769.nosynth);
                 uvar_subtyping = (uu___491_16769.uvar_subtyping);
                 tc_term = (uu___491_16769.tc_term);
                 type_of = (uu___491_16769.type_of);
                 universe_of = (uu___491_16769.universe_of);
                 check_type_of = (uu___491_16769.check_type_of);
                 use_bv_sorts = (uu___491_16769.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___491_16769.normalized_eff_names);
                 fv_delta_depths = (uu___491_16769.fv_delta_depths);
                 proof_ns = (uu___491_16769.proof_ns);
                 synth_hook = (uu___491_16769.synth_hook);
                 try_solve_implicits_hook =
                   (uu___491_16769.try_solve_implicits_hook);
                 splice = (uu___491_16769.splice);
                 mpreprocess = (uu___491_16769.mpreprocess);
                 postprocess = (uu___491_16769.postprocess);
                 identifier_info = (uu___491_16769.identifier_info);
                 tc_hooks = (uu___491_16769.tc_hooks);
                 dsenv = (uu___491_16769.dsenv);
                 nbe = (uu___491_16769.nbe);
                 strict_args_tab = (uu___491_16769.strict_args_tab);
                 erasable_types_tab = (uu___491_16769.erasable_types_tab);
                 enable_defer_to_tac = (uu___491_16769.enable_defer_to_tac)
               }))
         | FStar_Pervasives_Native.Some (uu____16786,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16801 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16801 next);
              (let uu___500_16804 = env1  in
               {
                 solver = (uu___500_16804.solver);
                 range = (uu___500_16804.range);
                 curmodule = (uu___500_16804.curmodule);
                 gamma = (uu___500_16804.gamma);
                 gamma_sig = (uu___500_16804.gamma_sig);
                 gamma_cache = (uu___500_16804.gamma_cache);
                 modules = (uu___500_16804.modules);
                 expected_typ = (uu___500_16804.expected_typ);
                 sigtab = (uu___500_16804.sigtab);
                 attrtab = (uu___500_16804.attrtab);
                 instantiate_imp = (uu___500_16804.instantiate_imp);
                 effects = (uu___500_16804.effects);
                 generalize = (uu___500_16804.generalize);
                 letrecs = (uu___500_16804.letrecs);
                 top_level = (uu___500_16804.top_level);
                 check_uvars = (uu___500_16804.check_uvars);
                 use_eq = (uu___500_16804.use_eq);
                 use_eq_strict = (uu___500_16804.use_eq_strict);
                 is_iface = (uu___500_16804.is_iface);
                 admit = (uu___500_16804.admit);
                 lax = (uu___500_16804.lax);
                 lax_universes = (uu___500_16804.lax_universes);
                 phase1 = (uu___500_16804.phase1);
                 failhard = (uu___500_16804.failhard);
                 nosynth = (uu___500_16804.nosynth);
                 uvar_subtyping = (uu___500_16804.uvar_subtyping);
                 tc_term = (uu___500_16804.tc_term);
                 type_of = (uu___500_16804.type_of);
                 universe_of = (uu___500_16804.universe_of);
                 check_type_of = (uu___500_16804.check_type_of);
                 use_bv_sorts = (uu___500_16804.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___500_16804.normalized_eff_names);
                 fv_delta_depths = (uu___500_16804.fv_delta_depths);
                 proof_ns = (uu___500_16804.proof_ns);
                 synth_hook = (uu___500_16804.synth_hook);
                 try_solve_implicits_hook =
                   (uu___500_16804.try_solve_implicits_hook);
                 splice = (uu___500_16804.splice);
                 mpreprocess = (uu___500_16804.mpreprocess);
                 postprocess = (uu___500_16804.postprocess);
                 identifier_info = (uu___500_16804.identifier_info);
                 tc_hooks = (uu___500_16804.tc_hooks);
                 dsenv = (uu___500_16804.dsenv);
                 nbe = (uu___500_16804.nbe);
                 strict_args_tab = (uu___500_16804.strict_args_tab);
                 erasable_types_tab = (uu___500_16804.erasable_types_tab);
                 enable_defer_to_tac = (uu___500_16804.enable_defer_to_tac)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16833 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16833 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___507_16849 = e  in
         {
           solver = (uu___507_16849.solver);
           range = r;
           curmodule = (uu___507_16849.curmodule);
           gamma = (uu___507_16849.gamma);
           gamma_sig = (uu___507_16849.gamma_sig);
           gamma_cache = (uu___507_16849.gamma_cache);
           modules = (uu___507_16849.modules);
           expected_typ = (uu___507_16849.expected_typ);
           sigtab = (uu___507_16849.sigtab);
           attrtab = (uu___507_16849.attrtab);
           instantiate_imp = (uu___507_16849.instantiate_imp);
           effects = (uu___507_16849.effects);
           generalize = (uu___507_16849.generalize);
           letrecs = (uu___507_16849.letrecs);
           top_level = (uu___507_16849.top_level);
           check_uvars = (uu___507_16849.check_uvars);
           use_eq = (uu___507_16849.use_eq);
           use_eq_strict = (uu___507_16849.use_eq_strict);
           is_iface = (uu___507_16849.is_iface);
           admit = (uu___507_16849.admit);
           lax = (uu___507_16849.lax);
           lax_universes = (uu___507_16849.lax_universes);
           phase1 = (uu___507_16849.phase1);
           failhard = (uu___507_16849.failhard);
           nosynth = (uu___507_16849.nosynth);
           uvar_subtyping = (uu___507_16849.uvar_subtyping);
           tc_term = (uu___507_16849.tc_term);
           type_of = (uu___507_16849.type_of);
           universe_of = (uu___507_16849.universe_of);
           check_type_of = (uu___507_16849.check_type_of);
           use_bv_sorts = (uu___507_16849.use_bv_sorts);
           qtbl_name_and_index = (uu___507_16849.qtbl_name_and_index);
           normalized_eff_names = (uu___507_16849.normalized_eff_names);
           fv_delta_depths = (uu___507_16849.fv_delta_depths);
           proof_ns = (uu___507_16849.proof_ns);
           synth_hook = (uu___507_16849.synth_hook);
           try_solve_implicits_hook =
             (uu___507_16849.try_solve_implicits_hook);
           splice = (uu___507_16849.splice);
           mpreprocess = (uu___507_16849.mpreprocess);
           postprocess = (uu___507_16849.postprocess);
           identifier_info = (uu___507_16849.identifier_info);
           tc_hooks = (uu___507_16849.tc_hooks);
           dsenv = (uu___507_16849.dsenv);
           nbe = (uu___507_16849.nbe);
           strict_args_tab = (uu___507_16849.strict_args_tab);
           erasable_types_tab = (uu___507_16849.erasable_types_tab);
           enable_defer_to_tac = (uu___507_16849.enable_defer_to_tac)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16869 =
        let uu____16870 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16870 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16869
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16925 =
          let uu____16926 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16926 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16925
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16981 =
          let uu____16982 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16982 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16981
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____17037 =
        let uu____17038 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____17038 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____17037
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___524_17102 = env1  in
      {
        solver = (uu___524_17102.solver);
        range = (uu___524_17102.range);
        curmodule = lid;
        gamma = (uu___524_17102.gamma);
        gamma_sig = (uu___524_17102.gamma_sig);
        gamma_cache = (uu___524_17102.gamma_cache);
        modules = (uu___524_17102.modules);
        expected_typ = (uu___524_17102.expected_typ);
        sigtab = (uu___524_17102.sigtab);
        attrtab = (uu___524_17102.attrtab);
        instantiate_imp = (uu___524_17102.instantiate_imp);
        effects = (uu___524_17102.effects);
        generalize = (uu___524_17102.generalize);
        letrecs = (uu___524_17102.letrecs);
        top_level = (uu___524_17102.top_level);
        check_uvars = (uu___524_17102.check_uvars);
        use_eq = (uu___524_17102.use_eq);
        use_eq_strict = (uu___524_17102.use_eq_strict);
        is_iface = (uu___524_17102.is_iface);
        admit = (uu___524_17102.admit);
        lax = (uu___524_17102.lax);
        lax_universes = (uu___524_17102.lax_universes);
        phase1 = (uu___524_17102.phase1);
        failhard = (uu___524_17102.failhard);
        nosynth = (uu___524_17102.nosynth);
        uvar_subtyping = (uu___524_17102.uvar_subtyping);
        tc_term = (uu___524_17102.tc_term);
        type_of = (uu___524_17102.type_of);
        universe_of = (uu___524_17102.universe_of);
        check_type_of = (uu___524_17102.check_type_of);
        use_bv_sorts = (uu___524_17102.use_bv_sorts);
        qtbl_name_and_index = (uu___524_17102.qtbl_name_and_index);
        normalized_eff_names = (uu___524_17102.normalized_eff_names);
        fv_delta_depths = (uu___524_17102.fv_delta_depths);
        proof_ns = (uu___524_17102.proof_ns);
        synth_hook = (uu___524_17102.synth_hook);
        try_solve_implicits_hook = (uu___524_17102.try_solve_implicits_hook);
        splice = (uu___524_17102.splice);
        mpreprocess = (uu___524_17102.mpreprocess);
        postprocess = (uu___524_17102.postprocess);
        identifier_info = (uu___524_17102.identifier_info);
        tc_hooks = (uu___524_17102.tc_hooks);
        dsenv = (uu___524_17102.dsenv);
        nbe = (uu___524_17102.nbe);
        strict_args_tab = (uu___524_17102.strict_args_tab);
        erasable_types_tab = (uu___524_17102.erasable_types_tab);
        enable_defer_to_tac = (uu___524_17102.enable_defer_to_tac)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      FStar_All.pipe_right env1.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____17133 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____17133
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____17146 =
      let uu____17148 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____17148  in
    (FStar_Errors.Fatal_NameNotFound, uu____17146)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____17163 =
      let uu____17165 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____17165  in
    (FStar_Errors.Fatal_VariableNotFound, uu____17163)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____17174  ->
    let uu____17175 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
    FStar_Syntax_Syntax.U_unif uu____17175
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n = (FStar_List.length formals) - Prims.int_one  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n - i), u)))
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____17277) ->
          let vs = mk_univ_subst formals us  in
          let uu____17301 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____17301)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17318  ->
    match uu___1_17318 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17344  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17364 = inst_tscheme t  in
      match uu____17364 with
      | (us,t1) ->
          let uu____17375 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17375)
  
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
          let uu____17400 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17402 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17400 uu____17402
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
    fun env1  ->
      fun ed  ->
        fun uu____17429  ->
          match uu____17429 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17443 =
                    let uu____17445 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17449 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17453 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17455 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17445 uu____17449 uu____17453 uu____17455
                     in
                  failwith uu____17443)
               else ();
               (let uu____17460 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17460))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17478 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17489 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17500 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____17514 =
        let uu____17516 = FStar_Ident.nsstr l  in
        let uu____17518 = FStar_Ident.string_of_lid cur  in
        uu____17516 = uu____17518  in
      if uu____17514
      then Yes
      else
        (let uu____17524 =
           let uu____17526 = FStar_Ident.nsstr l  in
           let uu____17528 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____17526 uu____17528  in
         if uu____17524
         then
           let lns =
             let uu____17534 = FStar_Ident.ns_of_lid l  in
             let uu____17537 =
               let uu____17540 = FStar_Ident.ident_of_lid l  in [uu____17540]
                in
             FStar_List.append uu____17534 uu____17537  in
           let cur1 =
             let uu____17544 = FStar_Ident.ns_of_lid cur  in
             let uu____17547 =
               let uu____17550 = FStar_Ident.ident_of_lid cur  in
               [uu____17550]  in
             FStar_List.append uu____17544 uu____17547  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____17574) -> Maybe
             | (uu____17581,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____17600 = FStar_Ident.string_of_id hd  in
                 let uu____17602 = FStar_Ident.string_of_id hd'  in
                 uu____17600 = uu____17602 -> aux tl tl'
             | uu____17605 -> No  in
           aux cur1 lns
         else No)
  
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env1  ->
    fun lid  ->
      let cur_mod = in_cur_mod env1 lid  in
      let cache t =
        (let uu____17657 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17657 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17701 =
            let uu____17704 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17704  in
          match uu____17701 with
          | FStar_Pervasives_Native.None  ->
              let uu____17726 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17770  ->
                     match uu___2_17770 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17809 = FStar_Ident.lid_equals lid l  in
                         if uu____17809
                         then
                           let uu____17832 =
                             let uu____17851 =
                               let uu____17866 = inst_tscheme t  in
                               FStar_Util.Inl uu____17866  in
                             let uu____17881 = FStar_Ident.range_of_lid l  in
                             (uu____17851, uu____17881)  in
                           FStar_Pervasives_Native.Some uu____17832
                         else FStar_Pervasives_Native.None
                     | uu____17934 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17726
                (fun uu____17972  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17982  ->
                        match uu___3_17982 with
                        | (uu____17985,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17987);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17988;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17989;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17990;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17991;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17992;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____18014 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____18014
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
                                  uu____18066 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____18073 -> cache t  in
                            let uu____18074 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____18074 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____18080 =
                                   let uu____18081 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____18081)
                                    in
                                 maybe_cache uu____18080)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____18152 = find_in_sigtab env1 lid  in
         match uu____18152 with
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
  fun env1  ->
    fun lid  ->
      let uu____18233 = lookup_qname env1 lid  in
      match uu____18233 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____18254,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____18368 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____18368 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____18413 =
          let uu____18416 = lookup_attr env2 attr  in se1 :: uu____18416  in
        FStar_Util.smap_add (attrtab env2) attr uu____18413  in
      FStar_List.iter
        (fun attr  ->
           let uu____18426 =
             let uu____18427 = FStar_Syntax_Subst.compress attr  in
             uu____18427.FStar_Syntax_Syntax.n  in
           match uu____18426 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18431 =
                 let uu____18433 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____18433  in
               add_one env1 se uu____18431
           | uu____18434 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18457) ->
          add_sigelts env1 ses
      | uu____18466 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____18474 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____18474 se) lids;
           add_se_to_attrtab env1 se)

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env1  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env1))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Range.range)
        FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun bv  ->
      FStar_Util.find_map env1.gamma
        (fun uu___4_18508  ->
           match uu___4_18508 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____18518 =
                 let uu____18525 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____18525)  in
               FStar_Pervasives_Native.Some uu____18518
           | uu____18534 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18596,lb::[]),uu____18598) ->
            let uu____18607 =
              let uu____18616 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18625 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18616, uu____18625)  in
            FStar_Pervasives_Native.Some uu____18607
        | FStar_Syntax_Syntax.Sig_let ((uu____18638,lbs),uu____18640) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18672 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18685 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18685
                     then
                       let uu____18698 =
                         let uu____18707 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18716 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18707, uu____18716)  in
                       FStar_Pervasives_Native.Some uu____18698
                     else FStar_Pervasives_Native.None)
        | uu____18739 -> FStar_Pervasives_Native.None
  
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
                    let uu____18831 =
                      let uu____18833 =
                        let uu____18835 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18837 =
                          let uu____18839 =
                            let uu____18841 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18847 =
                              let uu____18849 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18849  in
                            Prims.op_Hat uu____18841 uu____18847  in
                          Prims.op_Hat ", expected " uu____18839  in
                        Prims.op_Hat uu____18835 uu____18837  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18833
                       in
                    failwith uu____18831
                  else ());
             (let uu____18856 =
                let uu____18865 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18865, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18856))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18885,uu____18886) ->
            let uu____18891 =
              let uu____18900 =
                let uu____18905 =
                  let uu____18906 =
                    let uu____18909 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18909  in
                  (us, uu____18906)  in
                inst_ts us_opt uu____18905  in
              (uu____18900, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18891
        | uu____18928 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env1  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____19017 =
          match uu____19017 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____19113,uvs,t,uu____19116,uu____19117,uu____19118);
                      FStar_Syntax_Syntax.sigrng = uu____19119;
                      FStar_Syntax_Syntax.sigquals = uu____19120;
                      FStar_Syntax_Syntax.sigmeta = uu____19121;
                      FStar_Syntax_Syntax.sigattrs = uu____19122;
                      FStar_Syntax_Syntax.sigopts = uu____19123;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____19148 =
                     let uu____19157 = inst_tscheme1 (uvs, t)  in
                     (uu____19157, rng)  in
                   FStar_Pervasives_Native.Some uu____19148
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____19181;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____19183;
                      FStar_Syntax_Syntax.sigattrs = uu____19184;
                      FStar_Syntax_Syntax.sigopts = uu____19185;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____19204 =
                     let uu____19206 = in_cur_mod env1 l  in
                     uu____19206 = Yes  in
                   if uu____19204
                   then
                     let uu____19218 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____19218
                      then
                        let uu____19234 =
                          let uu____19243 = inst_tscheme1 (uvs, t)  in
                          (uu____19243, rng)  in
                        FStar_Pervasives_Native.Some uu____19234
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____19276 =
                        let uu____19285 = inst_tscheme1 (uvs, t)  in
                        (uu____19285, rng)  in
                      FStar_Pervasives_Native.Some uu____19276)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19310,uu____19311);
                      FStar_Syntax_Syntax.sigrng = uu____19312;
                      FStar_Syntax_Syntax.sigquals = uu____19313;
                      FStar_Syntax_Syntax.sigmeta = uu____19314;
                      FStar_Syntax_Syntax.sigattrs = uu____19315;
                      FStar_Syntax_Syntax.sigopts = uu____19316;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____19359 =
                          let uu____19368 = inst_tscheme1 (uvs, k)  in
                          (uu____19368, rng)  in
                        FStar_Pervasives_Native.Some uu____19359
                    | uu____19389 ->
                        let uu____19390 =
                          let uu____19399 =
                            let uu____19404 =
                              let uu____19405 =
                                let uu____19408 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19408
                                 in
                              (uvs, uu____19405)  in
                            inst_tscheme1 uu____19404  in
                          (uu____19399, rng)  in
                        FStar_Pervasives_Native.Some uu____19390)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19431,uu____19432);
                      FStar_Syntax_Syntax.sigrng = uu____19433;
                      FStar_Syntax_Syntax.sigquals = uu____19434;
                      FStar_Syntax_Syntax.sigmeta = uu____19435;
                      FStar_Syntax_Syntax.sigattrs = uu____19436;
                      FStar_Syntax_Syntax.sigopts = uu____19437;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19481 =
                          let uu____19490 = inst_tscheme_with (uvs, k) us  in
                          (uu____19490, rng)  in
                        FStar_Pervasives_Native.Some uu____19481
                    | uu____19511 ->
                        let uu____19512 =
                          let uu____19521 =
                            let uu____19526 =
                              let uu____19527 =
                                let uu____19530 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19530
                                 in
                              (uvs, uu____19527)  in
                            inst_tscheme_with uu____19526 us  in
                          (uu____19521, rng)  in
                        FStar_Pervasives_Native.Some uu____19512)
               | FStar_Util.Inr se ->
                   let uu____19566 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19587;
                          FStar_Syntax_Syntax.sigrng = uu____19588;
                          FStar_Syntax_Syntax.sigquals = uu____19589;
                          FStar_Syntax_Syntax.sigmeta = uu____19590;
                          FStar_Syntax_Syntax.sigattrs = uu____19591;
                          FStar_Syntax_Syntax.sigopts = uu____19592;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19609 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____19566
                     (FStar_Util.map_option
                        (fun uu____19657  ->
                           match uu____19657 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19688 =
          let uu____19699 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19699 mapper  in
        match uu____19688 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19773 =
              let uu____19784 =
                let uu____19791 =
                  let uu___861_19794 = t  in
                  let uu____19795 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___861_19794.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19795;
                    FStar_Syntax_Syntax.vars =
                      (uu___861_19794.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19791)  in
              (uu____19784, r)  in
            FStar_Pervasives_Native.Some uu____19773
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19844 = lookup_qname env1 l  in
      match uu____19844 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19865 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19919 = try_lookup_bv env1 bv  in
      match uu____19919 with
      | FStar_Pervasives_Native.None  ->
          let uu____19934 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19934 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19950 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19951 =
            let uu____19952 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19952  in
          (uu____19950, uu____19951)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19974 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19974 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____20040 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____20040  in
          let uu____20041 =
            let uu____20050 =
              let uu____20055 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____20055)  in
            (uu____20050, r1)  in
          FStar_Pervasives_Native.Some uu____20041
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun us  ->
      fun l  ->
        let uu____20090 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____20090 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____20123,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____20148 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____20148  in
            let uu____20149 =
              let uu____20154 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____20154, r1)  in
            FStar_Pervasives_Native.Some uu____20149
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____20178 = try_lookup_lid env1 l  in
      match uu____20178 with
      | FStar_Pervasives_Native.None  ->
          let uu____20205 = name_not_found l  in
          let uu____20211 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20205 uu____20211
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_20256  ->
              match uu___5_20256 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____20259 = FStar_Ident.string_of_id x  in
                  let uu____20261 = FStar_Ident.string_of_id y  in
                  uu____20259 = uu____20261
              | uu____20264 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20285 = lookup_qname env1 lid  in
      match uu____20285 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20294,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20297;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20299;
              FStar_Syntax_Syntax.sigattrs = uu____20300;
              FStar_Syntax_Syntax.sigopts = uu____20301;_},FStar_Pervasives_Native.None
            ),uu____20302)
          ->
          let uu____20353 =
            let uu____20360 =
              let uu____20361 =
                let uu____20364 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____20364 t  in
              (uvs, uu____20361)  in
            (uu____20360, q)  in
          FStar_Pervasives_Native.Some uu____20353
      | uu____20377 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____20399 = lookup_qname env1 lid  in
      match uu____20399 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20404,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20407;
              FStar_Syntax_Syntax.sigquals = uu____20408;
              FStar_Syntax_Syntax.sigmeta = uu____20409;
              FStar_Syntax_Syntax.sigattrs = uu____20410;
              FStar_Syntax_Syntax.sigopts = uu____20411;_},FStar_Pervasives_Native.None
            ),uu____20412)
          ->
          let uu____20463 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20463 (uvs, t)
      | uu____20468 ->
          let uu____20469 = name_not_found lid  in
          let uu____20475 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20469 uu____20475
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____20495 = lookup_qname env1 lid  in
      match uu____20495 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20500,uvs,t,uu____20503,uu____20504,uu____20505);
              FStar_Syntax_Syntax.sigrng = uu____20506;
              FStar_Syntax_Syntax.sigquals = uu____20507;
              FStar_Syntax_Syntax.sigmeta = uu____20508;
              FStar_Syntax_Syntax.sigattrs = uu____20509;
              FStar_Syntax_Syntax.sigopts = uu____20510;_},FStar_Pervasives_Native.None
            ),uu____20511)
          ->
          let uu____20568 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20568 (uvs, t)
      | uu____20573 ->
          let uu____20574 = name_not_found lid  in
          let uu____20580 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20574 uu____20580
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____20603 = lookup_qname env1 lid  in
      match uu____20603 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20611,uu____20612,uu____20613,uu____20614,uu____20615,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20617;
              FStar_Syntax_Syntax.sigquals = uu____20618;
              FStar_Syntax_Syntax.sigmeta = uu____20619;
              FStar_Syntax_Syntax.sigattrs = uu____20620;
              FStar_Syntax_Syntax.sigopts = uu____20621;_},uu____20622),uu____20623)
          -> (true, dcs)
      | uu____20688 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20704 = lookup_qname env1 lid  in
      match uu____20704 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20705,uu____20706,uu____20707,l,uu____20709,uu____20710);
              FStar_Syntax_Syntax.sigrng = uu____20711;
              FStar_Syntax_Syntax.sigquals = uu____20712;
              FStar_Syntax_Syntax.sigmeta = uu____20713;
              FStar_Syntax_Syntax.sigattrs = uu____20714;
              FStar_Syntax_Syntax.sigopts = uu____20715;_},uu____20716),uu____20717)
          -> l
      | uu____20776 ->
          let uu____20777 =
            let uu____20779 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20779  in
          failwith uu____20777
  
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
        fun qninfo1  ->
          let visible quals =
            FStar_All.pipe_right delta_levels
              (FStar_Util.for_some
                 (fun dl  ->
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some (visible_at dl))))
             in
          match qninfo1 with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20849)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20906) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20930 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20930
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20965 -> FStar_Pervasives_Native.None)
          | uu____20974 -> FStar_Pervasives_Native.None
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo1  ->
        lookup_definition_qninfo_aux true delta_levels lid qninfo1
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env1  ->
      fun lid  ->
        let uu____21036 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____21036
  
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env1  ->
      fun lid  ->
        let uu____21069 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____21069
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____21093 =
        let uu____21095 = FStar_Ident.nsstr lid  in uu____21095 = "Prims"  in
      if uu____21093
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____21125,uu____21126) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____21175),uu____21176) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____21225 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____21243 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____21253 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____21270 ->
                  let uu____21277 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____21277
              | FStar_Syntax_Syntax.Sig_let ((uu____21278,lbs),uu____21280)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____21296 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____21296
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____21303 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____21319 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____21329 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____21336 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____21337 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21338 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____21351 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____21352 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____21375 =
        let uu____21377 = FStar_Ident.nsstr lid  in uu____21377 = "Prims"  in
      if uu____21375
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21384 =
           let uu____21387 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____21387
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____21384
           (fun d_opt  ->
              let uu____21399 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____21399
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21409 =
                   let uu____21412 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21412  in
                 match uu____21409 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21413 =
                       let uu____21415 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21415
                        in
                     failwith uu____21413
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21420 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21420
                       then
                         let uu____21423 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21425 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21427 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21423 uu____21425 uu____21427
                       else ());
                      (let uu____21433 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____21433 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21454),uu____21455) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21504 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21526),uu____21527) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21576 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____21598 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21598
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21631 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____21631 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21653 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21662 =
                        let uu____21663 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21663.FStar_Syntax_Syntax.n  in
                      match uu____21662 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21668 -> false))
               in
            (true, uu____21653)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21691 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21691
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env1
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
          let uu____21763 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21763  in
        let uu____21764 = FStar_Util.smap_try_find tab s  in
        match uu____21764 with
        | FStar_Pervasives_Native.None  ->
            let uu____21767 = f ()  in
            (match uu____21767 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21805 =
        let uu____21806 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21806 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21840 =
        let uu____21841 = FStar_Syntax_Util.unrefine t  in
        uu____21841.FStar_Syntax_Syntax.n  in
      match uu____21840 with
      | FStar_Syntax_Syntax.Tm_type uu____21845 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21849) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21875) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21880,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21902 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21935 =
        let attrs =
          let uu____21941 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21941  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21981 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21981)
               in
            (true, res)
         in
      cache_in_fv_tab env1.strict_args_tab fv f
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun ftv  ->
      let uu____22026 = lookup_qname env1 ftv  in
      match uu____22026 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____22030) ->
          let uu____22075 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____22075 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____22096,t),r) ->
               let uu____22111 =
                 let uu____22112 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____22112 t  in
               FStar_Pervasives_Native.Some uu____22111)
      | uu____22113 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____22125 = try_lookup_effect_lid env1 ftv  in
      match uu____22125 with
      | FStar_Pervasives_Native.None  ->
          let uu____22128 = name_not_found ftv  in
          let uu____22134 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____22128 uu____22134
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____22158 = lookup_qname env1 lid0  in
        match uu____22158 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____22169);
                FStar_Syntax_Syntax.sigrng = uu____22170;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____22172;
                FStar_Syntax_Syntax.sigattrs = uu____22173;
                FStar_Syntax_Syntax.sigopts = uu____22174;_},FStar_Pervasives_Native.None
              ),uu____22175)
            ->
            let lid1 =
              let uu____22231 =
                let uu____22232 = FStar_Ident.range_of_lid lid  in
                let uu____22233 =
                  let uu____22234 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____22234  in
                FStar_Range.set_use_range uu____22232 uu____22233  in
              FStar_Ident.set_lid_range lid uu____22231  in
            let uu____22235 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_22241  ->
                      match uu___6_22241 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22244 -> false))
               in
            if uu____22235
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____22263 =
                      let uu____22265 =
                        let uu____22267 = get_range env1  in
                        FStar_Range.string_of_range uu____22267  in
                      let uu____22268 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____22270 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____22265 uu____22268 uu____22270
                       in
                    failwith uu____22263)
                  in
               match (binders, univs) with
               | ([],uu____22291) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____22317,uu____22318::uu____22319::uu____22320) ->
                   let uu____22341 =
                     let uu____22343 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____22345 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____22343 uu____22345
                      in
                   failwith uu____22341
               | uu____22356 ->
                   let uu____22371 =
                     let uu____22376 =
                       let uu____22377 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____22377)  in
                     inst_tscheme_with uu____22376 insts  in
                   (match uu____22371 with
                    | (uu____22390,t) ->
                        let t1 =
                          let uu____22393 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____22393 t  in
                        let uu____22394 =
                          let uu____22395 = FStar_Syntax_Subst.compress t1
                             in
                          uu____22395.FStar_Syntax_Syntax.n  in
                        (match uu____22394 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22430 -> failwith "Impossible")))
        | uu____22438 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____22462 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22462 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22475,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22482 = find l2  in
            (match uu____22482 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22489 =
          let uu____22492 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____22492  in
        match uu____22489 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22495 = find l  in
            (match uu____22495 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____22500 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____22500
                     m);
                  m))
         in
      let uu____22502 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22502
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22523 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____22523 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22529) ->
            FStar_List.length bs
        | uu____22568 ->
            let uu____22569 =
              let uu____22575 =
                let uu____22577 = FStar_Ident.string_of_lid name  in
                let uu____22579 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22577 uu____22579
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22575)
               in
            FStar_Errors.raise_error uu____22569 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____22598 = lookup_qname env1 l1  in
      match uu____22598 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22601;
              FStar_Syntax_Syntax.sigrng = uu____22602;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22604;
              FStar_Syntax_Syntax.sigattrs = uu____22605;
              FStar_Syntax_Syntax.sigopts = uu____22606;_},uu____22607),uu____22608)
          -> q
      | uu____22661 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22685 =
          let uu____22686 =
            let uu____22688 = FStar_Util.string_of_int i  in
            let uu____22690 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22688 uu____22690
             in
          failwith uu____22686  in
        let uu____22693 = lookup_datacon env1 lid  in
        match uu____22693 with
        | (uu____22698,t) ->
            let uu____22700 =
              let uu____22701 = FStar_Syntax_Subst.compress t  in
              uu____22701.FStar_Syntax_Syntax.n  in
            (match uu____22700 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22705) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22751 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22765 = lookup_qname env1 l  in
      match uu____22765 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22767,uu____22768,uu____22769);
              FStar_Syntax_Syntax.sigrng = uu____22770;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22772;
              FStar_Syntax_Syntax.sigattrs = uu____22773;
              FStar_Syntax_Syntax.sigopts = uu____22774;_},uu____22775),uu____22776)
          ->
          FStar_Util.for_some
            (fun uu___7_22831  ->
               match uu___7_22831 with
               | FStar_Syntax_Syntax.Projector uu____22833 -> true
               | uu____22839 -> false) quals
      | uu____22841 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22855 = lookup_qname env1 lid  in
      match uu____22855 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22857,uu____22858,uu____22859,uu____22860,uu____22861,uu____22862);
              FStar_Syntax_Syntax.sigrng = uu____22863;
              FStar_Syntax_Syntax.sigquals = uu____22864;
              FStar_Syntax_Syntax.sigmeta = uu____22865;
              FStar_Syntax_Syntax.sigattrs = uu____22866;
              FStar_Syntax_Syntax.sigopts = uu____22867;_},uu____22868),uu____22869)
          -> true
      | uu____22929 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22943 = lookup_qname env1 lid  in
      match uu____22943 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22945,uu____22946,uu____22947,uu____22948,uu____22949,uu____22950);
              FStar_Syntax_Syntax.sigrng = uu____22951;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22953;
              FStar_Syntax_Syntax.sigattrs = uu____22954;
              FStar_Syntax_Syntax.sigopts = uu____22955;_},uu____22956),uu____22957)
          ->
          FStar_Util.for_some
            (fun uu___8_23020  ->
               match uu___8_23020 with
               | FStar_Syntax_Syntax.RecordType uu____23022 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____23032 -> true
               | uu____23042 -> false) quals
      | uu____23044 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____23054,uu____23055);
            FStar_Syntax_Syntax.sigrng = uu____23056;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____23058;
            FStar_Syntax_Syntax.sigattrs = uu____23059;
            FStar_Syntax_Syntax.sigopts = uu____23060;_},uu____23061),uu____23062)
        ->
        FStar_Util.for_some
          (fun uu___9_23121  ->
             match uu___9_23121 with
             | FStar_Syntax_Syntax.Action uu____23123 -> true
             | uu____23125 -> false) quals
    | uu____23127 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____23141 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____23141
  
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
  fun env1  ->
    fun head  ->
      let uu____23158 =
        let uu____23159 = FStar_Syntax_Util.un_uinst head  in
        uu____23159.FStar_Syntax_Syntax.n  in
      match uu____23158 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____23165 ->
               true
           | uu____23168 -> false)
      | uu____23170 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23184 = lookup_qname env1 l  in
      match uu____23184 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____23187),uu____23188) ->
          FStar_Util.for_some
            (fun uu___10_23236  ->
               match uu___10_23236 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____23239 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____23241 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____23317 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____23335) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____23353 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____23361 ->
                 FStar_Pervasives_Native.Some true
             | uu____23380 -> FStar_Pervasives_Native.Some false)
         in
      let uu____23383 =
        let uu____23387 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____23387 mapper  in
      match uu____23383 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____23447 = lookup_qname env1 lid  in
      match uu____23447 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23451,uu____23452,tps,uu____23454,uu____23455,uu____23456);
              FStar_Syntax_Syntax.sigrng = uu____23457;
              FStar_Syntax_Syntax.sigquals = uu____23458;
              FStar_Syntax_Syntax.sigmeta = uu____23459;
              FStar_Syntax_Syntax.sigattrs = uu____23460;
              FStar_Syntax_Syntax.sigopts = uu____23461;_},uu____23462),uu____23463)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23531 -> FStar_Pervasives_Native.None
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      FStar_All.pipe_right (env1.effects).decls
        (FStar_Util.find_opt
           (fun uu____23577  ->
              match uu____23577 with
              | (d,uu____23586) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____23602 = effect_decl_opt env1 l  in
      match uu____23602 with
      | FStar_Pervasives_Native.None  ->
          let uu____23617 = name_not_found l  in
          let uu____23623 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23617 uu____23623
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23651 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23651 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23658  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23672  ->
            fun uu____23673  -> fun e  -> FStar_Util.return_all e))
  } 
let (join_opt :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23707 = FStar_Ident.lid_equals l1 l2  in
        if uu____23707
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23726 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23726
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23745 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23798  ->
                        match uu____23798 with
                        | (m1,m2,uu____23812,uu____23813,uu____23814) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23745 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23839,uu____23840,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23888 = join_opt env1 l1 l2  in
        match uu____23888 with
        | FStar_Pervasives_Native.None  ->
            let uu____23909 =
              let uu____23915 =
                let uu____23917 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23919 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23917 uu____23919
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23915)  in
            FStar_Errors.raise_error uu____23909 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23962 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23962
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env1.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'uuuuuu23982 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23982) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____24011 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____24037  ->
                match uu____24037 with
                | (d,uu____24044) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____24011 with
      | FStar_Pervasives_Native.None  ->
          let uu____24055 =
            let uu____24057 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____24057
             in
          failwith uu____24055
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____24072 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____24072 with
           | (uu____24083,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____24101)::(wp,uu____24103)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____24159 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env1  -> fun m  -> wp_sig_aux (env1.effects).decls m 
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env1.universe_of env1 t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env1.universe_of env1 t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____24224 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____24237 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____24237 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____24254 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____24254 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____24279 =
                     let uu____24285 =
                       let uu____24287 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____24295 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____24306 =
                         let uu____24308 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____24308  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____24287 uu____24295 uu____24306
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____24285)
                      in
                   FStar_Errors.raise_error uu____24279
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____24316 =
                     let uu____24327 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____24327 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____24364  ->
                        fun uu____24365  ->
                          match (uu____24364, uu____24365) with
                          | ((x,uu____24395),(t,uu____24397)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____24316
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____24428 =
                     let uu___1615_24429 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1615_24429.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1615_24429.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1615_24429.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1615_24429.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24428
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu24441 .
    'uuuuuu24441 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env1  ->
      fun c  ->
        fun u_res  ->
          let check_partial_application eff_name args =
            let r = get_range env1  in
            let uu____24482 =
              let uu____24489 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____24489)  in
            match uu____24482 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24513 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24515 = FStar_Util.string_of_int given  in
                     let uu____24517 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24513 uu____24515 uu____24517
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24522 = effect_decl_opt env1 effect_name  in
          match uu____24522 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24544) ->
              let uu____24555 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24555 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24573 =
                       let uu____24576 =
                         let uu____24577 =
                           let uu____24594 =
                             let uu____24605 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg
                                in
                             uu____24605 ::
                               (c1.FStar_Syntax_Syntax.effect_args)
                              in
                           (repr, uu____24594)  in
                         FStar_Syntax_Syntax.Tm_app uu____24577  in
                       let uu____24642 = get_range env1  in
                       FStar_Syntax_Syntax.mk uu____24576 uu____24642  in
                     FStar_Pervasives_Native.Some uu____24573)))
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env1  -> fun c  -> fun u_res  -> effect_repr_aux false env1 c u_res 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env1 effect_lid  in
      let quals = lookup_effect_quals env1 effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env1 effect_lid  in
      let quals = lookup_effect_quals env1 effect_lid1  in
      FStar_All.pipe_right quals
        (FStar_List.existsb
           (fun uu___11_24706  ->
              match uu___11_24706 with
              | FStar_Syntax_Syntax.Reflectable uu____24708 -> true
              | uu____24710 -> false))
  
let (is_total_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env1 effect_lid  in
      let quals = lookup_effect_quals env1 effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env1 effect_lid  in
      (is_user_reifiable_effect env1 effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
  
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env1  ->
    fun c  -> is_reifiable_effect env1 c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env1  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env1 ct.FStar_Syntax_Syntax.effect_name
      | uu____24770 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24785 =
        let uu____24786 = FStar_Syntax_Subst.compress t  in
        uu____24786.FStar_Syntax_Syntax.n  in
      match uu____24785 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24790,c) ->
          is_reifiable_comp env1 c
      | uu____24812 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24832 =
           let uu____24834 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24834  in
         if uu____24832
         then
           let uu____24837 =
             let uu____24843 =
               let uu____24845 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24845
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24843)  in
           let uu____24849 = get_range env1  in
           FStar_Errors.raise_error uu____24837 uu____24849
         else ());
        (let uu____24852 = effect_repr_aux true env1 c u_c  in
         match uu____24852 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1692_24888 = env1  in
        {
          solver = (uu___1692_24888.solver);
          range = (uu___1692_24888.range);
          curmodule = (uu___1692_24888.curmodule);
          gamma = (uu___1692_24888.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1692_24888.gamma_cache);
          modules = (uu___1692_24888.modules);
          expected_typ = (uu___1692_24888.expected_typ);
          sigtab = (uu___1692_24888.sigtab);
          attrtab = (uu___1692_24888.attrtab);
          instantiate_imp = (uu___1692_24888.instantiate_imp);
          effects = (uu___1692_24888.effects);
          generalize = (uu___1692_24888.generalize);
          letrecs = (uu___1692_24888.letrecs);
          top_level = (uu___1692_24888.top_level);
          check_uvars = (uu___1692_24888.check_uvars);
          use_eq = (uu___1692_24888.use_eq);
          use_eq_strict = (uu___1692_24888.use_eq_strict);
          is_iface = (uu___1692_24888.is_iface);
          admit = (uu___1692_24888.admit);
          lax = (uu___1692_24888.lax);
          lax_universes = (uu___1692_24888.lax_universes);
          phase1 = (uu___1692_24888.phase1);
          failhard = (uu___1692_24888.failhard);
          nosynth = (uu___1692_24888.nosynth);
          uvar_subtyping = (uu___1692_24888.uvar_subtyping);
          tc_term = (uu___1692_24888.tc_term);
          type_of = (uu___1692_24888.type_of);
          universe_of = (uu___1692_24888.universe_of);
          check_type_of = (uu___1692_24888.check_type_of);
          use_bv_sorts = (uu___1692_24888.use_bv_sorts);
          qtbl_name_and_index = (uu___1692_24888.qtbl_name_and_index);
          normalized_eff_names = (uu___1692_24888.normalized_eff_names);
          fv_delta_depths = (uu___1692_24888.fv_delta_depths);
          proof_ns = (uu___1692_24888.proof_ns);
          synth_hook = (uu___1692_24888.synth_hook);
          try_solve_implicits_hook =
            (uu___1692_24888.try_solve_implicits_hook);
          splice = (uu___1692_24888.splice);
          mpreprocess = (uu___1692_24888.mpreprocess);
          postprocess = (uu___1692_24888.postprocess);
          identifier_info = (uu___1692_24888.identifier_info);
          tc_hooks = (uu___1692_24888.tc_hooks);
          dsenv = (uu___1692_24888.dsenv);
          nbe = (uu___1692_24888.nbe);
          strict_args_tab = (uu___1692_24888.strict_args_tab);
          erasable_types_tab = (uu___1692_24888.erasable_types_tab);
          enable_defer_to_tac = (uu___1692_24888.enable_defer_to_tac)
        }  in
      add_sigelt env2 s;
      (env2.tc_hooks).tc_push_in_gamma_hook env2 (FStar_Util.Inr sb);
      env2
  
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env1  ->
    fun uu____24907  ->
      match uu____24907 with
      | (ed,quals) ->
          let effects1 =
            let uu___1701_24921 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1701_24921.order);
              joins = (uu___1701_24921.joins);
              polymonadic_binds = (uu___1701_24921.polymonadic_binds);
              polymonadic_subcomps = (uu___1701_24921.polymonadic_subcomps)
            }  in
          let uu___1704_24930 = env1  in
          {
            solver = (uu___1704_24930.solver);
            range = (uu___1704_24930.range);
            curmodule = (uu___1704_24930.curmodule);
            gamma = (uu___1704_24930.gamma);
            gamma_sig = (uu___1704_24930.gamma_sig);
            gamma_cache = (uu___1704_24930.gamma_cache);
            modules = (uu___1704_24930.modules);
            expected_typ = (uu___1704_24930.expected_typ);
            sigtab = (uu___1704_24930.sigtab);
            attrtab = (uu___1704_24930.attrtab);
            instantiate_imp = (uu___1704_24930.instantiate_imp);
            effects = effects1;
            generalize = (uu___1704_24930.generalize);
            letrecs = (uu___1704_24930.letrecs);
            top_level = (uu___1704_24930.top_level);
            check_uvars = (uu___1704_24930.check_uvars);
            use_eq = (uu___1704_24930.use_eq);
            use_eq_strict = (uu___1704_24930.use_eq_strict);
            is_iface = (uu___1704_24930.is_iface);
            admit = (uu___1704_24930.admit);
            lax = (uu___1704_24930.lax);
            lax_universes = (uu___1704_24930.lax_universes);
            phase1 = (uu___1704_24930.phase1);
            failhard = (uu___1704_24930.failhard);
            nosynth = (uu___1704_24930.nosynth);
            uvar_subtyping = (uu___1704_24930.uvar_subtyping);
            tc_term = (uu___1704_24930.tc_term);
            type_of = (uu___1704_24930.type_of);
            universe_of = (uu___1704_24930.universe_of);
            check_type_of = (uu___1704_24930.check_type_of);
            use_bv_sorts = (uu___1704_24930.use_bv_sorts);
            qtbl_name_and_index = (uu___1704_24930.qtbl_name_and_index);
            normalized_eff_names = (uu___1704_24930.normalized_eff_names);
            fv_delta_depths = (uu___1704_24930.fv_delta_depths);
            proof_ns = (uu___1704_24930.proof_ns);
            synth_hook = (uu___1704_24930.synth_hook);
            try_solve_implicits_hook =
              (uu___1704_24930.try_solve_implicits_hook);
            splice = (uu___1704_24930.splice);
            mpreprocess = (uu___1704_24930.mpreprocess);
            postprocess = (uu___1704_24930.postprocess);
            identifier_info = (uu___1704_24930.identifier_info);
            tc_hooks = (uu___1704_24930.tc_hooks);
            dsenv = (uu___1704_24930.dsenv);
            nbe = (uu___1704_24930.nbe);
            strict_args_tab = (uu___1704_24930.strict_args_tab);
            erasable_types_tab = (uu___1704_24930.erasable_types_tab);
            enable_defer_to_tac = (uu___1704_24930.enable_defer_to_tac)
          }
  
let (exists_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * polymonadic_bind_t)
          FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        let uu____24959 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____25027  ->
                  match uu____25027 with
                  | (m1,n1,uu____25045,uu____25046) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24959 with
        | FStar_Pervasives_Native.Some (uu____25071,uu____25072,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____25117 -> FStar_Pervasives_Native.None
  
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        let uu____25162 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____25197  ->
                  match uu____25197 with
                  | (m1,n1,uu____25207) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____25162 with
        | FStar_Pervasives_Native.Some (uu____25210,uu____25211,ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____25219 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____25276 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____25276
                  (fun uu____25297  ->
                     match uu____25297 with
                     | (c1,g1) ->
                         let uu____25308 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____25308
                           (fun uu____25329  ->
                              match uu____25329 with
                              | (c2,g2) ->
                                  let uu____25340 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____25340)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____25462 = l1 u t e  in
                              l2 u t uu____25462))
                | uu____25463 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let edge1 = { msource = src; mtarget = tgt; mlift = st_mlift }  in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift }  in
          let order = edge1 :: ((env1.effects).order)  in
          let ms =
            FStar_All.pipe_right (env1.effects).decls
              (FStar_List.map
                 (fun uu____25531  ->
                    match uu____25531 with
                    | (e,uu____25539) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25562 =
            match uu____25562 with
            | (i,j) ->
                let uu____25573 = FStar_Ident.lid_equals i j  in
                if uu____25573
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____25580  ->
                       FStar_Pervasives_Native.Some uu____25580)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25609 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25619 = FStar_Ident.lid_equals i k  in
                        if uu____25619
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25633 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25633
                                  then []
                                  else
                                    (let uu____25640 =
                                       let uu____25649 =
                                         find_edge order1 (i, k)  in
                                       let uu____25652 =
                                         find_edge order1 (k, j)  in
                                       (uu____25649, uu____25652)  in
                                     match uu____25640 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25667 =
                                           compose_edges e1 e2  in
                                         [uu____25667]
                                     | uu____25668 -> [])))))
                 in
              FStar_List.append order1 uu____25609  in
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
               (fun edge2  ->
                  let uu____25698 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25701 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____25701
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25698
                  then
                    let uu____25708 =
                      let uu____25714 =
                        let uu____25716 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25716
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25714)
                       in
                    let uu____25720 = get_range env1  in
                    FStar_Errors.raise_error uu____25708 uu____25720
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25798 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25798
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25850 =
                                             let uu____25859 =
                                               find_edge order2 (i, k)  in
                                             let uu____25862 =
                                               find_edge order2 (j, k)  in
                                             (uu____25859, uu____25862)  in
                                           match uu____25850 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25904,uu____25905)
                                                    ->
                                                    let uu____25912 =
                                                      let uu____25919 =
                                                        let uu____25921 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25921
                                                         in
                                                      let uu____25924 =
                                                        let uu____25926 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25926
                                                         in
                                                      (uu____25919,
                                                        uu____25924)
                                                       in
                                                    (match uu____25912 with
                                                     | (true ,true ) ->
                                                         let uu____25943 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25943
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
                                           | uu____25986 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____26038 =
                                   let uu____26040 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____26040
                                     FStar_Util.is_some
                                    in
                                 if uu____26038
                                 then
                                   let uu____26089 =
                                     let uu____26095 =
                                       let uu____26097 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____26099 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____26101 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____26103 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____26097 uu____26099 uu____26101
                                         uu____26103
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____26095)
                                      in
                                   FStar_Errors.raise_error uu____26089
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1838_26142 = env1.effects  in
             {
               decls = (uu___1838_26142.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1838_26142.polymonadic_binds);
               polymonadic_subcomps = (uu___1838_26142.polymonadic_subcomps)
             }  in
           let uu___1841_26143 = env1  in
           {
             solver = (uu___1841_26143.solver);
             range = (uu___1841_26143.range);
             curmodule = (uu___1841_26143.curmodule);
             gamma = (uu___1841_26143.gamma);
             gamma_sig = (uu___1841_26143.gamma_sig);
             gamma_cache = (uu___1841_26143.gamma_cache);
             modules = (uu___1841_26143.modules);
             expected_typ = (uu___1841_26143.expected_typ);
             sigtab = (uu___1841_26143.sigtab);
             attrtab = (uu___1841_26143.attrtab);
             instantiate_imp = (uu___1841_26143.instantiate_imp);
             effects = effects1;
             generalize = (uu___1841_26143.generalize);
             letrecs = (uu___1841_26143.letrecs);
             top_level = (uu___1841_26143.top_level);
             check_uvars = (uu___1841_26143.check_uvars);
             use_eq = (uu___1841_26143.use_eq);
             use_eq_strict = (uu___1841_26143.use_eq_strict);
             is_iface = (uu___1841_26143.is_iface);
             admit = (uu___1841_26143.admit);
             lax = (uu___1841_26143.lax);
             lax_universes = (uu___1841_26143.lax_universes);
             phase1 = (uu___1841_26143.phase1);
             failhard = (uu___1841_26143.failhard);
             nosynth = (uu___1841_26143.nosynth);
             uvar_subtyping = (uu___1841_26143.uvar_subtyping);
             tc_term = (uu___1841_26143.tc_term);
             type_of = (uu___1841_26143.type_of);
             universe_of = (uu___1841_26143.universe_of);
             check_type_of = (uu___1841_26143.check_type_of);
             use_bv_sorts = (uu___1841_26143.use_bv_sorts);
             qtbl_name_and_index = (uu___1841_26143.qtbl_name_and_index);
             normalized_eff_names = (uu___1841_26143.normalized_eff_names);
             fv_delta_depths = (uu___1841_26143.fv_delta_depths);
             proof_ns = (uu___1841_26143.proof_ns);
             synth_hook = (uu___1841_26143.synth_hook);
             try_solve_implicits_hook =
               (uu___1841_26143.try_solve_implicits_hook);
             splice = (uu___1841_26143.splice);
             mpreprocess = (uu___1841_26143.mpreprocess);
             postprocess = (uu___1841_26143.postprocess);
             identifier_info = (uu___1841_26143.identifier_info);
             tc_hooks = (uu___1841_26143.tc_hooks);
             dsenv = (uu___1841_26143.dsenv);
             nbe = (uu___1841_26143.nbe);
             strict_args_tab = (uu___1841_26143.strict_args_tab);
             erasable_types_tab = (uu___1841_26143.erasable_types_tab);
             enable_defer_to_tac = (uu___1841_26143.enable_defer_to_tac)
           })
  
let (add_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Ident.lident -> polymonadic_bind_t -> env)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        fun p  ->
          fun ty  ->
            let err_msg poly =
              let uu____26191 = FStar_Ident.string_of_lid m  in
              let uu____26193 = FStar_Ident.string_of_lid n  in
              let uu____26195 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____26191 uu____26193 uu____26195
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____26204 =
              let uu____26206 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____26206 FStar_Util.is_some  in
            if uu____26204
            then
              let uu____26243 =
                let uu____26249 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26249)
                 in
              FStar_Errors.raise_error uu____26243 env1.range
            else
              (let uu____26255 =
                 (let uu____26259 = join_opt env1 m n  in
                  FStar_All.pipe_right uu____26259 FStar_Util.is_some) &&
                   (let uu____26284 = FStar_Ident.lid_equals m n  in
                    Prims.op_Negation uu____26284)
                  in
               if uu____26255
               then
                 let uu____26287 =
                   let uu____26293 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26293)
                    in
                 FStar_Errors.raise_error uu____26287 env1.range
               else
                 (let uu___1856_26299 = env1  in
                  {
                    solver = (uu___1856_26299.solver);
                    range = (uu___1856_26299.range);
                    curmodule = (uu___1856_26299.curmodule);
                    gamma = (uu___1856_26299.gamma);
                    gamma_sig = (uu___1856_26299.gamma_sig);
                    gamma_cache = (uu___1856_26299.gamma_cache);
                    modules = (uu___1856_26299.modules);
                    expected_typ = (uu___1856_26299.expected_typ);
                    sigtab = (uu___1856_26299.sigtab);
                    attrtab = (uu___1856_26299.attrtab);
                    instantiate_imp = (uu___1856_26299.instantiate_imp);
                    effects =
                      (let uu___1858_26301 = env1.effects  in
                       {
                         decls = (uu___1858_26301.decls);
                         order = (uu___1858_26301.order);
                         joins = (uu___1858_26301.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1858_26301.polymonadic_subcomps)
                       });
                    generalize = (uu___1856_26299.generalize);
                    letrecs = (uu___1856_26299.letrecs);
                    top_level = (uu___1856_26299.top_level);
                    check_uvars = (uu___1856_26299.check_uvars);
                    use_eq = (uu___1856_26299.use_eq);
                    use_eq_strict = (uu___1856_26299.use_eq_strict);
                    is_iface = (uu___1856_26299.is_iface);
                    admit = (uu___1856_26299.admit);
                    lax = (uu___1856_26299.lax);
                    lax_universes = (uu___1856_26299.lax_universes);
                    phase1 = (uu___1856_26299.phase1);
                    failhard = (uu___1856_26299.failhard);
                    nosynth = (uu___1856_26299.nosynth);
                    uvar_subtyping = (uu___1856_26299.uvar_subtyping);
                    tc_term = (uu___1856_26299.tc_term);
                    type_of = (uu___1856_26299.type_of);
                    universe_of = (uu___1856_26299.universe_of);
                    check_type_of = (uu___1856_26299.check_type_of);
                    use_bv_sorts = (uu___1856_26299.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1856_26299.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1856_26299.normalized_eff_names);
                    fv_delta_depths = (uu___1856_26299.fv_delta_depths);
                    proof_ns = (uu___1856_26299.proof_ns);
                    synth_hook = (uu___1856_26299.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1856_26299.try_solve_implicits_hook);
                    splice = (uu___1856_26299.splice);
                    mpreprocess = (uu___1856_26299.mpreprocess);
                    postprocess = (uu___1856_26299.postprocess);
                    identifier_info = (uu___1856_26299.identifier_info);
                    tc_hooks = (uu___1856_26299.tc_hooks);
                    dsenv = (uu___1856_26299.dsenv);
                    nbe = (uu___1856_26299.nbe);
                    strict_args_tab = (uu___1856_26299.strict_args_tab);
                    erasable_types_tab = (uu___1856_26299.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1856_26299.enable_defer_to_tac)
                  }))
  
let (add_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Syntax_Syntax.tscheme -> env)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        fun ts  ->
          let err_msg poly =
            let uu____26392 = FStar_Ident.string_of_lid m  in
            let uu____26394 = FStar_Ident.string_of_lid n  in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu____26392 uu____26394
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice")
             in
          let uu____26403 =
            let uu____26405 = exists_polymonadic_subcomp env1 m n  in
            FStar_All.pipe_right uu____26405 FStar_Util.is_some  in
          if uu____26403
          then
            let uu____26412 =
              let uu____26418 = err_msg true  in
              (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26418)  in
            FStar_Errors.raise_error uu____26412 env1.range
          else
            (let uu____26424 =
               let uu____26426 = join_opt env1 m n  in
               FStar_All.pipe_right uu____26426 FStar_Util.is_some  in
             if uu____26424
             then
               let uu____26451 =
                 let uu____26457 = err_msg false  in
                 (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____26457)
                  in
               FStar_Errors.raise_error uu____26451 env1.range
             else
               (let uu___1871_26463 = env1  in
                {
                  solver = (uu___1871_26463.solver);
                  range = (uu___1871_26463.range);
                  curmodule = (uu___1871_26463.curmodule);
                  gamma = (uu___1871_26463.gamma);
                  gamma_sig = (uu___1871_26463.gamma_sig);
                  gamma_cache = (uu___1871_26463.gamma_cache);
                  modules = (uu___1871_26463.modules);
                  expected_typ = (uu___1871_26463.expected_typ);
                  sigtab = (uu___1871_26463.sigtab);
                  attrtab = (uu___1871_26463.attrtab);
                  instantiate_imp = (uu___1871_26463.instantiate_imp);
                  effects =
                    (let uu___1873_26465 = env1.effects  in
                     {
                       decls = (uu___1873_26465.decls);
                       order = (uu___1873_26465.order);
                       joins = (uu___1873_26465.joins);
                       polymonadic_binds =
                         (uu___1873_26465.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___1871_26463.generalize);
                  letrecs = (uu___1871_26463.letrecs);
                  top_level = (uu___1871_26463.top_level);
                  check_uvars = (uu___1871_26463.check_uvars);
                  use_eq = (uu___1871_26463.use_eq);
                  use_eq_strict = (uu___1871_26463.use_eq_strict);
                  is_iface = (uu___1871_26463.is_iface);
                  admit = (uu___1871_26463.admit);
                  lax = (uu___1871_26463.lax);
                  lax_universes = (uu___1871_26463.lax_universes);
                  phase1 = (uu___1871_26463.phase1);
                  failhard = (uu___1871_26463.failhard);
                  nosynth = (uu___1871_26463.nosynth);
                  uvar_subtyping = (uu___1871_26463.uvar_subtyping);
                  tc_term = (uu___1871_26463.tc_term);
                  type_of = (uu___1871_26463.type_of);
                  universe_of = (uu___1871_26463.universe_of);
                  check_type_of = (uu___1871_26463.check_type_of);
                  use_bv_sorts = (uu___1871_26463.use_bv_sorts);
                  qtbl_name_and_index = (uu___1871_26463.qtbl_name_and_index);
                  normalized_eff_names =
                    (uu___1871_26463.normalized_eff_names);
                  fv_delta_depths = (uu___1871_26463.fv_delta_depths);
                  proof_ns = (uu___1871_26463.proof_ns);
                  synth_hook = (uu___1871_26463.synth_hook);
                  try_solve_implicits_hook =
                    (uu___1871_26463.try_solve_implicits_hook);
                  splice = (uu___1871_26463.splice);
                  mpreprocess = (uu___1871_26463.mpreprocess);
                  postprocess = (uu___1871_26463.postprocess);
                  identifier_info = (uu___1871_26463.identifier_info);
                  tc_hooks = (uu___1871_26463.tc_hooks);
                  dsenv = (uu___1871_26463.dsenv);
                  nbe = (uu___1871_26463.nbe);
                  strict_args_tab = (uu___1871_26463.strict_args_tab);
                  erasable_types_tab = (uu___1871_26463.erasable_types_tab);
                  enable_defer_to_tac = (uu___1871_26463.enable_defer_to_tac)
                }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1877_26483 = env1  in
      {
        solver = (uu___1877_26483.solver);
        range = (uu___1877_26483.range);
        curmodule = (uu___1877_26483.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1877_26483.gamma_sig);
        gamma_cache = (uu___1877_26483.gamma_cache);
        modules = (uu___1877_26483.modules);
        expected_typ = (uu___1877_26483.expected_typ);
        sigtab = (uu___1877_26483.sigtab);
        attrtab = (uu___1877_26483.attrtab);
        instantiate_imp = (uu___1877_26483.instantiate_imp);
        effects = (uu___1877_26483.effects);
        generalize = (uu___1877_26483.generalize);
        letrecs = (uu___1877_26483.letrecs);
        top_level = (uu___1877_26483.top_level);
        check_uvars = (uu___1877_26483.check_uvars);
        use_eq = (uu___1877_26483.use_eq);
        use_eq_strict = (uu___1877_26483.use_eq_strict);
        is_iface = (uu___1877_26483.is_iface);
        admit = (uu___1877_26483.admit);
        lax = (uu___1877_26483.lax);
        lax_universes = (uu___1877_26483.lax_universes);
        phase1 = (uu___1877_26483.phase1);
        failhard = (uu___1877_26483.failhard);
        nosynth = (uu___1877_26483.nosynth);
        uvar_subtyping = (uu___1877_26483.uvar_subtyping);
        tc_term = (uu___1877_26483.tc_term);
        type_of = (uu___1877_26483.type_of);
        universe_of = (uu___1877_26483.universe_of);
        check_type_of = (uu___1877_26483.check_type_of);
        use_bv_sorts = (uu___1877_26483.use_bv_sorts);
        qtbl_name_and_index = (uu___1877_26483.qtbl_name_and_index);
        normalized_eff_names = (uu___1877_26483.normalized_eff_names);
        fv_delta_depths = (uu___1877_26483.fv_delta_depths);
        proof_ns = (uu___1877_26483.proof_ns);
        synth_hook = (uu___1877_26483.synth_hook);
        try_solve_implicits_hook = (uu___1877_26483.try_solve_implicits_hook);
        splice = (uu___1877_26483.splice);
        mpreprocess = (uu___1877_26483.mpreprocess);
        postprocess = (uu___1877_26483.postprocess);
        identifier_info = (uu___1877_26483.identifier_info);
        tc_hooks = (uu___1877_26483.tc_hooks);
        dsenv = (uu___1877_26483.dsenv);
        nbe = (uu___1877_26483.nbe);
        strict_args_tab = (uu___1877_26483.strict_args_tab);
        erasable_types_tab = (uu___1877_26483.erasable_types_tab);
        enable_defer_to_tac = (uu___1877_26483.enable_defer_to_tac)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env1  ->
    fun x  -> push_local_binding env1 (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env1  ->
    fun bvs  ->
      FStar_List.fold_left (fun env2  -> fun bv  -> push_bv env2 bv) env1 bvs
  
let (pop_bv :
  env -> (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option) =
  fun env1  ->
    match env1.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___1890_26541 = env1  in
             {
               solver = (uu___1890_26541.solver);
               range = (uu___1890_26541.range);
               curmodule = (uu___1890_26541.curmodule);
               gamma = rest;
               gamma_sig = (uu___1890_26541.gamma_sig);
               gamma_cache = (uu___1890_26541.gamma_cache);
               modules = (uu___1890_26541.modules);
               expected_typ = (uu___1890_26541.expected_typ);
               sigtab = (uu___1890_26541.sigtab);
               attrtab = (uu___1890_26541.attrtab);
               instantiate_imp = (uu___1890_26541.instantiate_imp);
               effects = (uu___1890_26541.effects);
               generalize = (uu___1890_26541.generalize);
               letrecs = (uu___1890_26541.letrecs);
               top_level = (uu___1890_26541.top_level);
               check_uvars = (uu___1890_26541.check_uvars);
               use_eq = (uu___1890_26541.use_eq);
               use_eq_strict = (uu___1890_26541.use_eq_strict);
               is_iface = (uu___1890_26541.is_iface);
               admit = (uu___1890_26541.admit);
               lax = (uu___1890_26541.lax);
               lax_universes = (uu___1890_26541.lax_universes);
               phase1 = (uu___1890_26541.phase1);
               failhard = (uu___1890_26541.failhard);
               nosynth = (uu___1890_26541.nosynth);
               uvar_subtyping = (uu___1890_26541.uvar_subtyping);
               tc_term = (uu___1890_26541.tc_term);
               type_of = (uu___1890_26541.type_of);
               universe_of = (uu___1890_26541.universe_of);
               check_type_of = (uu___1890_26541.check_type_of);
               use_bv_sorts = (uu___1890_26541.use_bv_sorts);
               qtbl_name_and_index = (uu___1890_26541.qtbl_name_and_index);
               normalized_eff_names = (uu___1890_26541.normalized_eff_names);
               fv_delta_depths = (uu___1890_26541.fv_delta_depths);
               proof_ns = (uu___1890_26541.proof_ns);
               synth_hook = (uu___1890_26541.synth_hook);
               try_solve_implicits_hook =
                 (uu___1890_26541.try_solve_implicits_hook);
               splice = (uu___1890_26541.splice);
               mpreprocess = (uu___1890_26541.mpreprocess);
               postprocess = (uu___1890_26541.postprocess);
               identifier_info = (uu___1890_26541.identifier_info);
               tc_hooks = (uu___1890_26541.tc_hooks);
               dsenv = (uu___1890_26541.dsenv);
               nbe = (uu___1890_26541.nbe);
               strict_args_tab = (uu___1890_26541.strict_args_tab);
               erasable_types_tab = (uu___1890_26541.erasable_types_tab);
               enable_defer_to_tac = (uu___1890_26541.enable_defer_to_tac)
             }))
    | uu____26542 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____26571  ->
             match uu____26571 with | (x,uu____26579) -> push_bv env2 x) env1
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
            let uu___1904_26614 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1904_26614.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1904_26614.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env1  ->
    fun lb  -> fun ts  -> push_local_binding env1 (binding_of_lb lb ts)
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env1  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun x  ->
             push_local_binding env2 (FStar_Syntax_Syntax.Binding_univ x))
        env1 xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list))
  =
  fun env1  ->
    fun uvs  ->
      fun terms  ->
        let uu____26687 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26687 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____26715 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26715)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1925_26731 = env1  in
      {
        solver = (uu___1925_26731.solver);
        range = (uu___1925_26731.range);
        curmodule = (uu___1925_26731.curmodule);
        gamma = (uu___1925_26731.gamma);
        gamma_sig = (uu___1925_26731.gamma_sig);
        gamma_cache = (uu___1925_26731.gamma_cache);
        modules = (uu___1925_26731.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1925_26731.sigtab);
        attrtab = (uu___1925_26731.attrtab);
        instantiate_imp = (uu___1925_26731.instantiate_imp);
        effects = (uu___1925_26731.effects);
        generalize = (uu___1925_26731.generalize);
        letrecs = (uu___1925_26731.letrecs);
        top_level = (uu___1925_26731.top_level);
        check_uvars = (uu___1925_26731.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1925_26731.use_eq_strict);
        is_iface = (uu___1925_26731.is_iface);
        admit = (uu___1925_26731.admit);
        lax = (uu___1925_26731.lax);
        lax_universes = (uu___1925_26731.lax_universes);
        phase1 = (uu___1925_26731.phase1);
        failhard = (uu___1925_26731.failhard);
        nosynth = (uu___1925_26731.nosynth);
        uvar_subtyping = (uu___1925_26731.uvar_subtyping);
        tc_term = (uu___1925_26731.tc_term);
        type_of = (uu___1925_26731.type_of);
        universe_of = (uu___1925_26731.universe_of);
        check_type_of = (uu___1925_26731.check_type_of);
        use_bv_sorts = (uu___1925_26731.use_bv_sorts);
        qtbl_name_and_index = (uu___1925_26731.qtbl_name_and_index);
        normalized_eff_names = (uu___1925_26731.normalized_eff_names);
        fv_delta_depths = (uu___1925_26731.fv_delta_depths);
        proof_ns = (uu___1925_26731.proof_ns);
        synth_hook = (uu___1925_26731.synth_hook);
        try_solve_implicits_hook = (uu___1925_26731.try_solve_implicits_hook);
        splice = (uu___1925_26731.splice);
        mpreprocess = (uu___1925_26731.mpreprocess);
        postprocess = (uu___1925_26731.postprocess);
        identifier_info = (uu___1925_26731.identifier_info);
        tc_hooks = (uu___1925_26731.tc_hooks);
        dsenv = (uu___1925_26731.dsenv);
        nbe = (uu___1925_26731.nbe);
        strict_args_tab = (uu___1925_26731.strict_args_tab);
        erasable_types_tab = (uu___1925_26731.erasable_types_tab);
        enable_defer_to_tac = (uu___1925_26731.enable_defer_to_tac)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env1  ->
    match env1.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env -> (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)) =
  fun env_  ->
    let uu____26762 = expected_typ env_  in
    ((let uu___1932_26768 = env_  in
      {
        solver = (uu___1932_26768.solver);
        range = (uu___1932_26768.range);
        curmodule = (uu___1932_26768.curmodule);
        gamma = (uu___1932_26768.gamma);
        gamma_sig = (uu___1932_26768.gamma_sig);
        gamma_cache = (uu___1932_26768.gamma_cache);
        modules = (uu___1932_26768.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1932_26768.sigtab);
        attrtab = (uu___1932_26768.attrtab);
        instantiate_imp = (uu___1932_26768.instantiate_imp);
        effects = (uu___1932_26768.effects);
        generalize = (uu___1932_26768.generalize);
        letrecs = (uu___1932_26768.letrecs);
        top_level = (uu___1932_26768.top_level);
        check_uvars = (uu___1932_26768.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1932_26768.use_eq_strict);
        is_iface = (uu___1932_26768.is_iface);
        admit = (uu___1932_26768.admit);
        lax = (uu___1932_26768.lax);
        lax_universes = (uu___1932_26768.lax_universes);
        phase1 = (uu___1932_26768.phase1);
        failhard = (uu___1932_26768.failhard);
        nosynth = (uu___1932_26768.nosynth);
        uvar_subtyping = (uu___1932_26768.uvar_subtyping);
        tc_term = (uu___1932_26768.tc_term);
        type_of = (uu___1932_26768.type_of);
        universe_of = (uu___1932_26768.universe_of);
        check_type_of = (uu___1932_26768.check_type_of);
        use_bv_sorts = (uu___1932_26768.use_bv_sorts);
        qtbl_name_and_index = (uu___1932_26768.qtbl_name_and_index);
        normalized_eff_names = (uu___1932_26768.normalized_eff_names);
        fv_delta_depths = (uu___1932_26768.fv_delta_depths);
        proof_ns = (uu___1932_26768.proof_ns);
        synth_hook = (uu___1932_26768.synth_hook);
        try_solve_implicits_hook = (uu___1932_26768.try_solve_implicits_hook);
        splice = (uu___1932_26768.splice);
        mpreprocess = (uu___1932_26768.mpreprocess);
        postprocess = (uu___1932_26768.postprocess);
        identifier_info = (uu___1932_26768.identifier_info);
        tc_hooks = (uu___1932_26768.tc_hooks);
        dsenv = (uu___1932_26768.dsenv);
        nbe = (uu___1932_26768.nbe);
        strict_args_tab = (uu___1932_26768.strict_args_tab);
        erasable_types_tab = (uu___1932_26768.erasable_types_tab);
        enable_defer_to_tac = (uu___1932_26768.enable_defer_to_tac)
      }), uu____26762)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26780 =
      let uu____26781 = FStar_Ident.id_of_text ""  in [uu____26781]  in
    FStar_Ident.lid_of_ids uu____26780  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____26788 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26788
        then
          let uu____26793 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26793 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1940_26821 = env1  in
       {
         solver = (uu___1940_26821.solver);
         range = (uu___1940_26821.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1940_26821.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1940_26821.expected_typ);
         sigtab = (uu___1940_26821.sigtab);
         attrtab = (uu___1940_26821.attrtab);
         instantiate_imp = (uu___1940_26821.instantiate_imp);
         effects = (uu___1940_26821.effects);
         generalize = (uu___1940_26821.generalize);
         letrecs = (uu___1940_26821.letrecs);
         top_level = (uu___1940_26821.top_level);
         check_uvars = (uu___1940_26821.check_uvars);
         use_eq = (uu___1940_26821.use_eq);
         use_eq_strict = (uu___1940_26821.use_eq_strict);
         is_iface = (uu___1940_26821.is_iface);
         admit = (uu___1940_26821.admit);
         lax = (uu___1940_26821.lax);
         lax_universes = (uu___1940_26821.lax_universes);
         phase1 = (uu___1940_26821.phase1);
         failhard = (uu___1940_26821.failhard);
         nosynth = (uu___1940_26821.nosynth);
         uvar_subtyping = (uu___1940_26821.uvar_subtyping);
         tc_term = (uu___1940_26821.tc_term);
         type_of = (uu___1940_26821.type_of);
         universe_of = (uu___1940_26821.universe_of);
         check_type_of = (uu___1940_26821.check_type_of);
         use_bv_sorts = (uu___1940_26821.use_bv_sorts);
         qtbl_name_and_index = (uu___1940_26821.qtbl_name_and_index);
         normalized_eff_names = (uu___1940_26821.normalized_eff_names);
         fv_delta_depths = (uu___1940_26821.fv_delta_depths);
         proof_ns = (uu___1940_26821.proof_ns);
         synth_hook = (uu___1940_26821.synth_hook);
         try_solve_implicits_hook =
           (uu___1940_26821.try_solve_implicits_hook);
         splice = (uu___1940_26821.splice);
         mpreprocess = (uu___1940_26821.mpreprocess);
         postprocess = (uu___1940_26821.postprocess);
         identifier_info = (uu___1940_26821.identifier_info);
         tc_hooks = (uu___1940_26821.tc_hooks);
         dsenv = (uu___1940_26821.dsenv);
         nbe = (uu___1940_26821.nbe);
         strict_args_tab = (uu___1940_26821.strict_args_tab);
         erasable_types_tab = (uu___1940_26821.erasable_types_tab);
         enable_defer_to_tac = (uu___1940_26821.enable_defer_to_tac)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26873)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26877,(uu____26878,t)))::tl
          ->
          let uu____26899 =
            let uu____26902 = FStar_Syntax_Free.uvars t  in
            ext out uu____26902  in
          aux uu____26899 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26905;
            FStar_Syntax_Syntax.index = uu____26906;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26914 =
            let uu____26917 = FStar_Syntax_Free.uvars t  in
            ext out uu____26917  in
          aux uu____26914 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26975)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26979,(uu____26980,t)))::tl
          ->
          let uu____27001 =
            let uu____27004 = FStar_Syntax_Free.univs t  in
            ext out uu____27004  in
          aux uu____27001 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____27007;
            FStar_Syntax_Syntax.index = uu____27008;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____27016 =
            let uu____27019 = FStar_Syntax_Free.univs t  in
            ext out uu____27019  in
          aux uu____27016 tl
       in
    aux no_univs env1.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env1  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl ->
          let uu____27081 = FStar_Util.set_add uname out  in
          aux uu____27081 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____27084,(uu____27085,t)))::tl
          ->
          let uu____27106 =
            let uu____27109 = FStar_Syntax_Free.univnames t  in
            ext out uu____27109  in
          aux uu____27106 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____27112;
            FStar_Syntax_Syntax.index = uu____27113;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____27121 =
            let uu____27124 = FStar_Syntax_Free.univnames t  in
            ext out uu____27124  in
          aux uu____27121 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_27145  ->
            match uu___12_27145 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____27149 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____27162 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____27173 =
      let uu____27182 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____27182
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____27173 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____27230 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_27243  ->
              match uu___13_27243 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____27246 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____27246
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____27250 = FStar_Ident.string_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____27250
              | FStar_Syntax_Syntax.Binding_lid (l,uu____27254) ->
                  let uu____27271 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____27271))
       in
    FStar_All.pipe_right uu____27230 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_27285  ->
    match uu___14_27285 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____27291 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____27291
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____27314  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____27369) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____27402,uu____27403) -> false  in
      let uu____27417 =
        FStar_List.tryFind
          (fun uu____27439  ->
             match uu____27439 with | (p,uu____27450) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____27417 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____27469,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____27499 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____27499
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2083_27521 = e  in
        {
          solver = (uu___2083_27521.solver);
          range = (uu___2083_27521.range);
          curmodule = (uu___2083_27521.curmodule);
          gamma = (uu___2083_27521.gamma);
          gamma_sig = (uu___2083_27521.gamma_sig);
          gamma_cache = (uu___2083_27521.gamma_cache);
          modules = (uu___2083_27521.modules);
          expected_typ = (uu___2083_27521.expected_typ);
          sigtab = (uu___2083_27521.sigtab);
          attrtab = (uu___2083_27521.attrtab);
          instantiate_imp = (uu___2083_27521.instantiate_imp);
          effects = (uu___2083_27521.effects);
          generalize = (uu___2083_27521.generalize);
          letrecs = (uu___2083_27521.letrecs);
          top_level = (uu___2083_27521.top_level);
          check_uvars = (uu___2083_27521.check_uvars);
          use_eq = (uu___2083_27521.use_eq);
          use_eq_strict = (uu___2083_27521.use_eq_strict);
          is_iface = (uu___2083_27521.is_iface);
          admit = (uu___2083_27521.admit);
          lax = (uu___2083_27521.lax);
          lax_universes = (uu___2083_27521.lax_universes);
          phase1 = (uu___2083_27521.phase1);
          failhard = (uu___2083_27521.failhard);
          nosynth = (uu___2083_27521.nosynth);
          uvar_subtyping = (uu___2083_27521.uvar_subtyping);
          tc_term = (uu___2083_27521.tc_term);
          type_of = (uu___2083_27521.type_of);
          universe_of = (uu___2083_27521.universe_of);
          check_type_of = (uu___2083_27521.check_type_of);
          use_bv_sorts = (uu___2083_27521.use_bv_sorts);
          qtbl_name_and_index = (uu___2083_27521.qtbl_name_and_index);
          normalized_eff_names = (uu___2083_27521.normalized_eff_names);
          fv_delta_depths = (uu___2083_27521.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2083_27521.synth_hook);
          try_solve_implicits_hook =
            (uu___2083_27521.try_solve_implicits_hook);
          splice = (uu___2083_27521.splice);
          mpreprocess = (uu___2083_27521.mpreprocess);
          postprocess = (uu___2083_27521.postprocess);
          identifier_info = (uu___2083_27521.identifier_info);
          tc_hooks = (uu___2083_27521.tc_hooks);
          dsenv = (uu___2083_27521.dsenv);
          nbe = (uu___2083_27521.nbe);
          strict_args_tab = (uu___2083_27521.strict_args_tab);
          erasable_types_tab = (uu___2083_27521.erasable_types_tab);
          enable_defer_to_tac = (uu___2083_27521.enable_defer_to_tac)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2092_27569 = e  in
      {
        solver = (uu___2092_27569.solver);
        range = (uu___2092_27569.range);
        curmodule = (uu___2092_27569.curmodule);
        gamma = (uu___2092_27569.gamma);
        gamma_sig = (uu___2092_27569.gamma_sig);
        gamma_cache = (uu___2092_27569.gamma_cache);
        modules = (uu___2092_27569.modules);
        expected_typ = (uu___2092_27569.expected_typ);
        sigtab = (uu___2092_27569.sigtab);
        attrtab = (uu___2092_27569.attrtab);
        instantiate_imp = (uu___2092_27569.instantiate_imp);
        effects = (uu___2092_27569.effects);
        generalize = (uu___2092_27569.generalize);
        letrecs = (uu___2092_27569.letrecs);
        top_level = (uu___2092_27569.top_level);
        check_uvars = (uu___2092_27569.check_uvars);
        use_eq = (uu___2092_27569.use_eq);
        use_eq_strict = (uu___2092_27569.use_eq_strict);
        is_iface = (uu___2092_27569.is_iface);
        admit = (uu___2092_27569.admit);
        lax = (uu___2092_27569.lax);
        lax_universes = (uu___2092_27569.lax_universes);
        phase1 = (uu___2092_27569.phase1);
        failhard = (uu___2092_27569.failhard);
        nosynth = (uu___2092_27569.nosynth);
        uvar_subtyping = (uu___2092_27569.uvar_subtyping);
        tc_term = (uu___2092_27569.tc_term);
        type_of = (uu___2092_27569.type_of);
        universe_of = (uu___2092_27569.universe_of);
        check_type_of = (uu___2092_27569.check_type_of);
        use_bv_sorts = (uu___2092_27569.use_bv_sorts);
        qtbl_name_and_index = (uu___2092_27569.qtbl_name_and_index);
        normalized_eff_names = (uu___2092_27569.normalized_eff_names);
        fv_delta_depths = (uu___2092_27569.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2092_27569.synth_hook);
        try_solve_implicits_hook = (uu___2092_27569.try_solve_implicits_hook);
        splice = (uu___2092_27569.splice);
        mpreprocess = (uu___2092_27569.mpreprocess);
        postprocess = (uu___2092_27569.postprocess);
        identifier_info = (uu___2092_27569.identifier_info);
        tc_hooks = (uu___2092_27569.tc_hooks);
        dsenv = (uu___2092_27569.dsenv);
        nbe = (uu___2092_27569.nbe);
        strict_args_tab = (uu___2092_27569.strict_args_tab);
        erasable_types_tab = (uu___2092_27569.erasable_types_tab);
        enable_defer_to_tac = (uu___2092_27569.enable_defer_to_tac)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____27585 = FStar_Syntax_Free.names t  in
      let uu____27588 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____27585 uu____27588
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27611 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27611
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27621 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27621
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____27642 =
      match uu____27642 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27662 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27662)
       in
    let uu____27670 =
      let uu____27674 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____27674 FStar_List.rev  in
    FStar_All.pipe_right uu____27670 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Common.guard_f = g;
      FStar_TypeChecker_Common.deferred_to_tac = [];
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
        FStar_TypeChecker_Common.deferred_to_tac = uu____27730;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([],[]);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27748 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27748 with
                   | FStar_Pervasives_Native.Some uu____27752 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27755 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred_to_tac = uu____27765;
        FStar_TypeChecker_Common.deferred = uu____27766;
        FStar_TypeChecker_Common.univ_ineqs = uu____27767;
        FStar_TypeChecker_Common.implicits = uu____27768;_} -> true
    | uu____27778 -> false
  
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
          let uu___2138_27800 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2138_27800.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2138_27800.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2138_27800.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2138_27800.FStar_TypeChecker_Common.implicits)
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
          let uu____27839 = FStar_Options.defensive ()  in
          if uu____27839
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27845 =
              let uu____27847 =
                let uu____27849 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27849  in
              Prims.op_Negation uu____27847  in
            (if uu____27845
             then
               let uu____27856 =
                 let uu____27862 =
                   let uu____27864 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27866 =
                     let uu____27868 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27868
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27864 uu____27866
                    in
                 (FStar_Errors.Warning_Defensive, uu____27862)  in
               FStar_Errors.log_issue rng uu____27856
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
          let uu____27908 =
            let uu____27910 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27910  in
          if uu____27908
          then ()
          else
            (let uu____27915 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27915 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27941 =
            let uu____27943 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27943  in
          if uu____27941
          then ()
          else
            (let uu____27948 = bound_vars e  in
             def_check_closed_in rng msg uu____27948 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env1  ->
        fun g  ->
          match g.FStar_TypeChecker_Common.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env1 f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2175_27987 = g  in
          let uu____27988 =
            let uu____27989 =
              let uu____27990 =
                let uu____27991 =
                  let uu____28008 =
                    let uu____28019 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____28019]  in
                  (f, uu____28008)  in
                FStar_Syntax_Syntax.Tm_app uu____27991  in
              FStar_Syntax_Syntax.mk uu____27990 f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____28056  ->
                 FStar_TypeChecker_Common.NonTrivial uu____28056) uu____27989
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27988;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2175_27987.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2175_27987.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2175_27987.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2175_27987.FStar_TypeChecker_Common.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2182_28074 = g  in
          let uu____28075 =
            let uu____28076 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____28076  in
          {
            FStar_TypeChecker_Common.guard_f = uu____28075;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2182_28074.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2182_28074.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2182_28074.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2182_28074.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2187_28093 = g  in
          let uu____28094 =
            let uu____28095 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____28095  in
          {
            FStar_TypeChecker_Common.guard_f = uu____28094;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2187_28093.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2187_28093.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2187_28093.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2187_28093.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2191_28097 = g  in
          let uu____28098 =
            let uu____28099 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____28099  in
          {
            FStar_TypeChecker_Common.guard_f = uu____28098;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2191_28097.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2191_28097.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2191_28097.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2191_28097.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____28106 ->
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
                       let uu____28183 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____28183
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2214_28190 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2214_28190.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2214_28190.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2214_28190.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2214_28190.FStar_TypeChecker_Common.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____28224 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____28224
               then f1
               else
                 (let u =
                    env1.universe_of env1
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env1  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2229_28251 = g  in
            let uu____28252 =
              let uu____28253 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____28253  in
            {
              FStar_TypeChecker_Common.guard_f = uu____28252;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2229_28251.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2229_28251.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2229_28251.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2229_28251.FStar_TypeChecker_Common.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            FStar_Syntax_Syntax.ctx_uvar_meta_t
              FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
                FStar_Range.range) Prims.list * guard_t))
  =
  fun reason  ->
    fun r  ->
      fun env1  ->
        fun k  ->
          fun should_check  ->
            fun meta  ->
              let uu____28303 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____28303 with
              | FStar_Pervasives_Native.Some
                  (uu____28328::(tm,uu____28330)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____28394 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____28412 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____28412;
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
                        r
                       in
                    let imp =
                      {
                        FStar_TypeChecker_Common.imp_reason = reason;
                        FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                        FStar_TypeChecker_Common.imp_tm = t;
                        FStar_TypeChecker_Common.imp_range = r
                      }  in
                    (let uu____28446 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____28446
                     then
                       let uu____28450 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____28450
                     else ());
                    (let g =
                       let uu___2253_28456 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2253_28456.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2253_28456.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2253_28456.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2253_28456.FStar_TypeChecker_Common.univ_ineqs);
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
  fun env1  ->
    fun bs  ->
      fun substs  ->
        fun reason  ->
          fun r  ->
            let uu____28510 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28569  ->
                      fun b  ->
                        match uu____28569 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let ctx_uvar_meta_t =
                              match FStar_Pervasives_Native.snd b with
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
                                  t)) ->
                                  let uu____28621 =
                                    let uu____28622 =
                                      let uu____28629 = FStar_Dyn.mkdyn env1
                                         in
                                      (uu____28629, t)  in
                                    FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                      uu____28622
                                     in
                                  FStar_Pervasives_Native.Some uu____28621
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr t)
                              | uu____28635 -> FStar_Pervasives_Native.None
                               in
                            let uu____28638 =
                              new_implicit_var_aux "" r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                ctx_uvar_meta_t
                               in
                            (match uu____28638 with
                             | (t,l_ctx_uvars,g_t) ->
                                 ((let uu____28678 =
                                     FStar_All.pipe_left (debug env1)
                                       (FStar_Options.Other
                                          "LayeredEffectsEqns")
                                      in
                                   if uu____28678
                                   then
                                     FStar_List.iter
                                       (fun uu____28691  ->
                                          match uu____28691 with
                                          | (ctx_uvar,uu____28697) ->
                                              let uu____28698 =
                                                FStar_Syntax_Print.ctx_uvar_to_string_no_reason
                                                  ctx_uvar
                                                 in
                                              FStar_Util.print1
                                                "Layered Effect uvar : %s\n"
                                                uu____28698) l_ctx_uvars
                                   else ());
                                  (let uu____28703 =
                                     let uu____28706 =
                                       let uu____28709 =
                                         let uu____28710 =
                                           let uu____28717 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____28717, t)  in
                                         FStar_Syntax_Syntax.NT uu____28710
                                          in
                                       [uu____28709]  in
                                     FStar_List.append substs1 uu____28706
                                      in
                                   let uu____28728 = conj_guard g g_t  in
                                   (uu____28703,
                                     (FStar_List.append uvars [t]),
                                     uu____28728)))))
                   (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____28510
              (fun uu____28757  ->
                 match uu____28757 with | (uu____28774,uvars,g) -> (uvars, g))
  
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun env1  ->
    fun u  ->
      fun t  ->
        fun wp  ->
          fun r  ->
            let trivial_post =
              let post_ts =
                let uu____28815 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28815 FStar_Util.must  in
              let uu____28832 = inst_tscheme_with post_ts [u]  in
              match uu____28832 with
              | (uu____28837,post) ->
                  let uu____28839 =
                    let uu____28840 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                    [uu____28840]  in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____28839 r
               in
            let uu____28873 =
              let uu____28874 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg
                 in
              [uu____28874]  in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____28873 r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28910  -> ());
    push = (fun uu____28912  -> ());
    pop = (fun uu____28915  -> ());
    snapshot =
      (fun uu____28918  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28937  -> fun uu____28938  -> ());
    encode_sig = (fun uu____28953  -> fun uu____28954  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28960 =
             let uu____28967 = FStar_Options.peek ()  in (e, g, uu____28967)
              in
           [uu____28960]);
    solve = (fun uu____28983  -> fun uu____28984  -> fun uu____28985  -> ());
    finish = (fun uu____28992  -> ());
    refresh = (fun uu____28994  -> ())
  } 
let (get_letrec_arity :
  env ->
    FStar_Syntax_Syntax.lbname -> Prims.int FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lbname  ->
      let compare_either f1 f2 e1 e2 =
        match (e1, e2) with
        | (FStar_Util.Inl v1,FStar_Util.Inl v2) -> f1 v1 v2
        | (FStar_Util.Inr v1,FStar_Util.Inr v2) -> f2 v1 v2
        | uu____29103 -> false  in
      let uu____29117 =
        FStar_Util.find_opt
          (fun uu____29151  ->
             match uu____29151 with
             | (lbname',uu____29167,uu____29168,uu____29169) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs
         in
      match uu____29117 with
      | FStar_Pervasives_Native.Some
          (uu____29183,arity,uu____29185,uu____29186) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  