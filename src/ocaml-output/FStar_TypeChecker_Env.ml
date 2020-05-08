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
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
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
           (fun uu___0_14374  ->
              match uu___0_14374 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14377 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____14377  in
                  let uu____14378 =
                    let uu____14379 = FStar_Syntax_Subst.compress y  in
                    uu____14379.FStar_Syntax_Syntax.n  in
                  (match uu____14378 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14383 =
                         let uu___327_14384 = y1  in
                         let uu____14385 =
                           FStar_Syntax_Subst.subst subst
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
  fun subst  ->
    fun env1  ->
      let uu___333_14402 = env1  in
      let uu____14403 = rename_gamma subst env1.gamma  in
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
        identifier_info = (uu___333_14402.identifier_info);
        tc_hooks = (uu___333_14402.tc_hooks);
        dsenv = (uu___333_14402.dsenv);
        nbe = (uu___333_14402.nbe);
        strict_args_tab = (uu___333_14402.strict_args_tab);
        erasable_types_tab = (uu___333_14402.erasable_types_tab);
        enable_defer_to_tac = (uu___333_14402.enable_defer_to_tac)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14411  -> fun uu____14412  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___340_14434 = env1  in
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
        identifier_info = (uu___340_14434.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14434.dsenv);
        nbe = (uu___340_14434.nbe);
        strict_args_tab = (uu___340_14434.strict_args_tab);
        erasable_types_tab = (uu___340_14434.erasable_types_tab);
        enable_defer_to_tac = (uu___340_14434.enable_defer_to_tac)
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
        identifier_info = (uu___344_14446.identifier_info);
        tc_hooks = (uu___344_14446.tc_hooks);
        dsenv = uu____14447;
        nbe = (uu___344_14446.nbe);
        strict_args_tab = (uu___344_14446.strict_args_tab);
        erasable_types_tab = (uu___344_14446.erasable_types_tab);
        enable_defer_to_tac = (uu___344_14446.enable_defer_to_tac)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14464 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____14464)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14479) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14482,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14484,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14487 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14501 . unit -> 'uuuuuu14501 FStar_Util.smap =
  fun uu____14508  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14514 . unit -> 'uuuuuu14514 FStar_Util.smap =
  fun uu____14521  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14659 = new_gamma_cache ()  in
                  let uu____14662 = new_sigtab ()  in
                  let uu____14665 = new_sigtab ()  in
                  let uu____14672 =
                    let uu____14687 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14687, FStar_Pervasives_Native.None)  in
                  let uu____14708 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14712 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14716 = FStar_Options.using_facts_from ()  in
                  let uu____14717 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14720 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14721 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14735 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14659;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14662;
                    attrtab = uu____14665;
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
                    qtbl_name_and_index = uu____14672;
                    normalized_eff_names = uu____14708;
                    fv_delta_depths = uu____14712;
                    proof_ns = uu____14716;
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
                    identifier_info = uu____14717;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14720;
                    nbe;
                    strict_args_tab = uu____14721;
                    erasable_types_tab = uu____14735;
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
  fun uu____14929  ->
    let uu____14930 = FStar_ST.op_Bang query_indices  in
    match uu____14930 with
    | [] -> failwith "Empty query indices!"
    | uu____14985 ->
        let uu____14995 =
          let uu____15005 =
            let uu____15013 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____15013  in
          let uu____15067 = FStar_ST.op_Bang query_indices  in uu____15005 ::
            uu____15067
           in
        FStar_ST.op_Colon_Equals query_indices uu____14995
  
let (pop_query_indices : unit -> unit) =
  fun uu____15163  ->
    let uu____15164 = FStar_ST.op_Bang query_indices  in
    match uu____15164 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15291  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15328  ->
    match uu____15328 with
    | (l,n) ->
        let uu____15338 = FStar_ST.op_Bang query_indices  in
        (match uu____15338 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15460 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15483  ->
    let uu____15484 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15484
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15552 =
       let uu____15555 = FStar_ST.op_Bang stack  in env1 :: uu____15555  in
     FStar_ST.op_Colon_Equals stack uu____15552);
    (let uu___418_15604 = env1  in
     let uu____15605 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15608 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15611 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15618 =
       let uu____15633 =
         let uu____15637 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15637  in
       let uu____15669 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15633, uu____15669)  in
     let uu____15718 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15721 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15724 =
       let uu____15727 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15727  in
     let uu____15747 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15760 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___418_15604.solver);
       range = (uu___418_15604.range);
       curmodule = (uu___418_15604.curmodule);
       gamma = (uu___418_15604.gamma);
       gamma_sig = (uu___418_15604.gamma_sig);
       gamma_cache = uu____15605;
       modules = (uu___418_15604.modules);
       expected_typ = (uu___418_15604.expected_typ);
       sigtab = uu____15608;
       attrtab = uu____15611;
       instantiate_imp = (uu___418_15604.instantiate_imp);
       effects = (uu___418_15604.effects);
       generalize = (uu___418_15604.generalize);
       letrecs = (uu___418_15604.letrecs);
       top_level = (uu___418_15604.top_level);
       check_uvars = (uu___418_15604.check_uvars);
       use_eq = (uu___418_15604.use_eq);
       use_eq_strict = (uu___418_15604.use_eq_strict);
       is_iface = (uu___418_15604.is_iface);
       admit = (uu___418_15604.admit);
       lax = (uu___418_15604.lax);
       lax_universes = (uu___418_15604.lax_universes);
       phase1 = (uu___418_15604.phase1);
       failhard = (uu___418_15604.failhard);
       nosynth = (uu___418_15604.nosynth);
       uvar_subtyping = (uu___418_15604.uvar_subtyping);
       tc_term = (uu___418_15604.tc_term);
       type_of = (uu___418_15604.type_of);
       universe_of = (uu___418_15604.universe_of);
       check_type_of = (uu___418_15604.check_type_of);
       use_bv_sorts = (uu___418_15604.use_bv_sorts);
       qtbl_name_and_index = uu____15618;
       normalized_eff_names = uu____15718;
       fv_delta_depths = uu____15721;
       proof_ns = (uu___418_15604.proof_ns);
       synth_hook = (uu___418_15604.synth_hook);
       try_solve_implicits_hook = (uu___418_15604.try_solve_implicits_hook);
       splice = (uu___418_15604.splice);
       mpreprocess = (uu___418_15604.mpreprocess);
       postprocess = (uu___418_15604.postprocess);
       identifier_info = uu____15724;
       tc_hooks = (uu___418_15604.tc_hooks);
       dsenv = (uu___418_15604.dsenv);
       nbe = (uu___418_15604.nbe);
       strict_args_tab = uu____15747;
       erasable_types_tab = uu____15760;
       enable_defer_to_tac = (uu___418_15604.enable_defer_to_tac)
     })
  
let (pop_stack : unit -> env) =
  fun uu____15770  ->
    let uu____15771 = FStar_ST.op_Bang stack  in
    match uu____15771 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15825 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15915  ->
           let uu____15916 = snapshot_stack env1  in
           match uu____15916 with
           | (stack_depth,env2) ->
               let uu____15950 = snapshot_query_indices ()  in
               (match uu____15950 with
                | (query_indices_depth,()) ->
                    let uu____15983 = (env2.solver).snapshot msg  in
                    (match uu____15983 with
                     | (solver_depth,()) ->
                         let uu____16040 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____16040 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_16107 = env2  in
                                 {
                                   solver = (uu___443_16107.solver);
                                   range = (uu___443_16107.range);
                                   curmodule = (uu___443_16107.curmodule);
                                   gamma = (uu___443_16107.gamma);
                                   gamma_sig = (uu___443_16107.gamma_sig);
                                   gamma_cache = (uu___443_16107.gamma_cache);
                                   modules = (uu___443_16107.modules);
                                   expected_typ =
                                     (uu___443_16107.expected_typ);
                                   sigtab = (uu___443_16107.sigtab);
                                   attrtab = (uu___443_16107.attrtab);
                                   instantiate_imp =
                                     (uu___443_16107.instantiate_imp);
                                   effects = (uu___443_16107.effects);
                                   generalize = (uu___443_16107.generalize);
                                   letrecs = (uu___443_16107.letrecs);
                                   top_level = (uu___443_16107.top_level);
                                   check_uvars = (uu___443_16107.check_uvars);
                                   use_eq = (uu___443_16107.use_eq);
                                   use_eq_strict =
                                     (uu___443_16107.use_eq_strict);
                                   is_iface = (uu___443_16107.is_iface);
                                   admit = (uu___443_16107.admit);
                                   lax = (uu___443_16107.lax);
                                   lax_universes =
                                     (uu___443_16107.lax_universes);
                                   phase1 = (uu___443_16107.phase1);
                                   failhard = (uu___443_16107.failhard);
                                   nosynth = (uu___443_16107.nosynth);
                                   uvar_subtyping =
                                     (uu___443_16107.uvar_subtyping);
                                   tc_term = (uu___443_16107.tc_term);
                                   type_of = (uu___443_16107.type_of);
                                   universe_of = (uu___443_16107.universe_of);
                                   check_type_of =
                                     (uu___443_16107.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_16107.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_16107.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_16107.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_16107.fv_delta_depths);
                                   proof_ns = (uu___443_16107.proof_ns);
                                   synth_hook = (uu___443_16107.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_16107.try_solve_implicits_hook);
                                   splice = (uu___443_16107.splice);
                                   mpreprocess = (uu___443_16107.mpreprocess);
                                   postprocess = (uu___443_16107.postprocess);
                                   identifier_info =
                                     (uu___443_16107.identifier_info);
                                   tc_hooks = (uu___443_16107.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_16107.nbe);
                                   strict_args_tab =
                                     (uu___443_16107.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_16107.erasable_types_tab);
                                   enable_defer_to_tac =
                                     (uu___443_16107.enable_defer_to_tac)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16141  ->
             let uu____16142 =
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
             match uu____16142 with
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
                             ((let uu____16322 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16322
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____16338 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____16338
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____16370,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____16412 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16442  ->
                  match uu____16442 with
                  | (m,uu____16450) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16412 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16464 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16464 next);
              (let uu___488_16467 = env1  in
               {
                 solver = (uu___488_16467.solver);
                 range = (uu___488_16467.range);
                 curmodule = (uu___488_16467.curmodule);
                 gamma = (uu___488_16467.gamma);
                 gamma_sig = (uu___488_16467.gamma_sig);
                 gamma_cache = (uu___488_16467.gamma_cache);
                 modules = (uu___488_16467.modules);
                 expected_typ = (uu___488_16467.expected_typ);
                 sigtab = (uu___488_16467.sigtab);
                 attrtab = (uu___488_16467.attrtab);
                 instantiate_imp = (uu___488_16467.instantiate_imp);
                 effects = (uu___488_16467.effects);
                 generalize = (uu___488_16467.generalize);
                 letrecs = (uu___488_16467.letrecs);
                 top_level = (uu___488_16467.top_level);
                 check_uvars = (uu___488_16467.check_uvars);
                 use_eq = (uu___488_16467.use_eq);
                 use_eq_strict = (uu___488_16467.use_eq_strict);
                 is_iface = (uu___488_16467.is_iface);
                 admit = (uu___488_16467.admit);
                 lax = (uu___488_16467.lax);
                 lax_universes = (uu___488_16467.lax_universes);
                 phase1 = (uu___488_16467.phase1);
                 failhard = (uu___488_16467.failhard);
                 nosynth = (uu___488_16467.nosynth);
                 uvar_subtyping = (uu___488_16467.uvar_subtyping);
                 tc_term = (uu___488_16467.tc_term);
                 type_of = (uu___488_16467.type_of);
                 universe_of = (uu___488_16467.universe_of);
                 check_type_of = (uu___488_16467.check_type_of);
                 use_bv_sorts = (uu___488_16467.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16467.normalized_eff_names);
                 fv_delta_depths = (uu___488_16467.fv_delta_depths);
                 proof_ns = (uu___488_16467.proof_ns);
                 synth_hook = (uu___488_16467.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16467.try_solve_implicits_hook);
                 splice = (uu___488_16467.splice);
                 mpreprocess = (uu___488_16467.mpreprocess);
                 postprocess = (uu___488_16467.postprocess);
                 identifier_info = (uu___488_16467.identifier_info);
                 tc_hooks = (uu___488_16467.tc_hooks);
                 dsenv = (uu___488_16467.dsenv);
                 nbe = (uu___488_16467.nbe);
                 strict_args_tab = (uu___488_16467.strict_args_tab);
                 erasable_types_tab = (uu___488_16467.erasable_types_tab);
                 enable_defer_to_tac = (uu___488_16467.enable_defer_to_tac)
               }))
         | FStar_Pervasives_Native.Some (uu____16484,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16499 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16499 next);
              (let uu___497_16502 = env1  in
               {
                 solver = (uu___497_16502.solver);
                 range = (uu___497_16502.range);
                 curmodule = (uu___497_16502.curmodule);
                 gamma = (uu___497_16502.gamma);
                 gamma_sig = (uu___497_16502.gamma_sig);
                 gamma_cache = (uu___497_16502.gamma_cache);
                 modules = (uu___497_16502.modules);
                 expected_typ = (uu___497_16502.expected_typ);
                 sigtab = (uu___497_16502.sigtab);
                 attrtab = (uu___497_16502.attrtab);
                 instantiate_imp = (uu___497_16502.instantiate_imp);
                 effects = (uu___497_16502.effects);
                 generalize = (uu___497_16502.generalize);
                 letrecs = (uu___497_16502.letrecs);
                 top_level = (uu___497_16502.top_level);
                 check_uvars = (uu___497_16502.check_uvars);
                 use_eq = (uu___497_16502.use_eq);
                 use_eq_strict = (uu___497_16502.use_eq_strict);
                 is_iface = (uu___497_16502.is_iface);
                 admit = (uu___497_16502.admit);
                 lax = (uu___497_16502.lax);
                 lax_universes = (uu___497_16502.lax_universes);
                 phase1 = (uu___497_16502.phase1);
                 failhard = (uu___497_16502.failhard);
                 nosynth = (uu___497_16502.nosynth);
                 uvar_subtyping = (uu___497_16502.uvar_subtyping);
                 tc_term = (uu___497_16502.tc_term);
                 type_of = (uu___497_16502.type_of);
                 universe_of = (uu___497_16502.universe_of);
                 check_type_of = (uu___497_16502.check_type_of);
                 use_bv_sorts = (uu___497_16502.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16502.normalized_eff_names);
                 fv_delta_depths = (uu___497_16502.fv_delta_depths);
                 proof_ns = (uu___497_16502.proof_ns);
                 synth_hook = (uu___497_16502.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16502.try_solve_implicits_hook);
                 splice = (uu___497_16502.splice);
                 mpreprocess = (uu___497_16502.mpreprocess);
                 postprocess = (uu___497_16502.postprocess);
                 identifier_info = (uu___497_16502.identifier_info);
                 tc_hooks = (uu___497_16502.tc_hooks);
                 dsenv = (uu___497_16502.dsenv);
                 nbe = (uu___497_16502.nbe);
                 strict_args_tab = (uu___497_16502.strict_args_tab);
                 erasable_types_tab = (uu___497_16502.erasable_types_tab);
                 enable_defer_to_tac = (uu___497_16502.enable_defer_to_tac)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16531 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16531 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___504_16547 = e  in
         {
           solver = (uu___504_16547.solver);
           range = r;
           curmodule = (uu___504_16547.curmodule);
           gamma = (uu___504_16547.gamma);
           gamma_sig = (uu___504_16547.gamma_sig);
           gamma_cache = (uu___504_16547.gamma_cache);
           modules = (uu___504_16547.modules);
           expected_typ = (uu___504_16547.expected_typ);
           sigtab = (uu___504_16547.sigtab);
           attrtab = (uu___504_16547.attrtab);
           instantiate_imp = (uu___504_16547.instantiate_imp);
           effects = (uu___504_16547.effects);
           generalize = (uu___504_16547.generalize);
           letrecs = (uu___504_16547.letrecs);
           top_level = (uu___504_16547.top_level);
           check_uvars = (uu___504_16547.check_uvars);
           use_eq = (uu___504_16547.use_eq);
           use_eq_strict = (uu___504_16547.use_eq_strict);
           is_iface = (uu___504_16547.is_iface);
           admit = (uu___504_16547.admit);
           lax = (uu___504_16547.lax);
           lax_universes = (uu___504_16547.lax_universes);
           phase1 = (uu___504_16547.phase1);
           failhard = (uu___504_16547.failhard);
           nosynth = (uu___504_16547.nosynth);
           uvar_subtyping = (uu___504_16547.uvar_subtyping);
           tc_term = (uu___504_16547.tc_term);
           type_of = (uu___504_16547.type_of);
           universe_of = (uu___504_16547.universe_of);
           check_type_of = (uu___504_16547.check_type_of);
           use_bv_sorts = (uu___504_16547.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16547.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16547.normalized_eff_names);
           fv_delta_depths = (uu___504_16547.fv_delta_depths);
           proof_ns = (uu___504_16547.proof_ns);
           synth_hook = (uu___504_16547.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16547.try_solve_implicits_hook);
           splice = (uu___504_16547.splice);
           mpreprocess = (uu___504_16547.mpreprocess);
           postprocess = (uu___504_16547.postprocess);
           identifier_info = (uu___504_16547.identifier_info);
           tc_hooks = (uu___504_16547.tc_hooks);
           dsenv = (uu___504_16547.dsenv);
           nbe = (uu___504_16547.nbe);
           strict_args_tab = (uu___504_16547.strict_args_tab);
           erasable_types_tab = (uu___504_16547.erasable_types_tab);
           enable_defer_to_tac = (uu___504_16547.enable_defer_to_tac)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16567 =
        let uu____16568 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16568 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16567
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16623 =
          let uu____16624 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16624 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16623
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16679 =
          let uu____16680 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16680 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16679
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16735 =
        let uu____16736 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16736 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16735
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___521_16800 = env1  in
      {
        solver = (uu___521_16800.solver);
        range = (uu___521_16800.range);
        curmodule = lid;
        gamma = (uu___521_16800.gamma);
        gamma_sig = (uu___521_16800.gamma_sig);
        gamma_cache = (uu___521_16800.gamma_cache);
        modules = (uu___521_16800.modules);
        expected_typ = (uu___521_16800.expected_typ);
        sigtab = (uu___521_16800.sigtab);
        attrtab = (uu___521_16800.attrtab);
        instantiate_imp = (uu___521_16800.instantiate_imp);
        effects = (uu___521_16800.effects);
        generalize = (uu___521_16800.generalize);
        letrecs = (uu___521_16800.letrecs);
        top_level = (uu___521_16800.top_level);
        check_uvars = (uu___521_16800.check_uvars);
        use_eq = (uu___521_16800.use_eq);
        use_eq_strict = (uu___521_16800.use_eq_strict);
        is_iface = (uu___521_16800.is_iface);
        admit = (uu___521_16800.admit);
        lax = (uu___521_16800.lax);
        lax_universes = (uu___521_16800.lax_universes);
        phase1 = (uu___521_16800.phase1);
        failhard = (uu___521_16800.failhard);
        nosynth = (uu___521_16800.nosynth);
        uvar_subtyping = (uu___521_16800.uvar_subtyping);
        tc_term = (uu___521_16800.tc_term);
        type_of = (uu___521_16800.type_of);
        universe_of = (uu___521_16800.universe_of);
        check_type_of = (uu___521_16800.check_type_of);
        use_bv_sorts = (uu___521_16800.use_bv_sorts);
        qtbl_name_and_index = (uu___521_16800.qtbl_name_and_index);
        normalized_eff_names = (uu___521_16800.normalized_eff_names);
        fv_delta_depths = (uu___521_16800.fv_delta_depths);
        proof_ns = (uu___521_16800.proof_ns);
        synth_hook = (uu___521_16800.synth_hook);
        try_solve_implicits_hook = (uu___521_16800.try_solve_implicits_hook);
        splice = (uu___521_16800.splice);
        mpreprocess = (uu___521_16800.mpreprocess);
        postprocess = (uu___521_16800.postprocess);
        identifier_info = (uu___521_16800.identifier_info);
        tc_hooks = (uu___521_16800.tc_hooks);
        dsenv = (uu___521_16800.dsenv);
        nbe = (uu___521_16800.nbe);
        strict_args_tab = (uu___521_16800.strict_args_tab);
        erasable_types_tab = (uu___521_16800.erasable_types_tab);
        enable_defer_to_tac = (uu___521_16800.enable_defer_to_tac)
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
      let uu____16831 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16831
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16844 =
      let uu____16846 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____16846  in
    (FStar_Errors.Fatal_NameNotFound, uu____16844)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16861 =
      let uu____16863 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16863  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16861)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16872  ->
    let uu____16873 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
    FStar_Syntax_Syntax.U_unif uu____16873
  
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
      | ((formals,t),uu____16975) ->
          let vs = mk_univ_subst formals us  in
          let uu____16999 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16999)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_17016  ->
    match uu___1_17016 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17042  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17062 = inst_tscheme t  in
      match uu____17062 with
      | (us,t1) ->
          let uu____17073 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17073)
  
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
          let uu____17098 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17100 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17098 uu____17100
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
        fun uu____17127  ->
          match uu____17127 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17141 =
                    let uu____17143 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17147 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17151 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17153 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17143 uu____17147 uu____17151 uu____17153
                     in
                  failwith uu____17141)
               else ();
               (let uu____17158 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17158))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17176 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17187 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17198 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____17212 =
        let uu____17214 = FStar_Ident.nsstr l  in
        let uu____17216 = FStar_Ident.string_of_lid cur  in
        uu____17214 = uu____17216  in
      if uu____17212
      then Yes
      else
        (let uu____17222 =
           let uu____17224 = FStar_Ident.nsstr l  in
           let uu____17226 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____17224 uu____17226  in
         if uu____17222
         then
           let lns =
             let uu____17232 = FStar_Ident.ns_of_lid l  in
             let uu____17235 =
               let uu____17238 = FStar_Ident.ident_of_lid l  in [uu____17238]
                in
             FStar_List.append uu____17232 uu____17235  in
           let cur1 =
             let uu____17242 = FStar_Ident.ns_of_lid cur  in
             let uu____17245 =
               let uu____17248 = FStar_Ident.ident_of_lid cur  in
               [uu____17248]  in
             FStar_List.append uu____17242 uu____17245  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____17272) -> Maybe
             | (uu____17279,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____17298 = FStar_Ident.string_of_id hd  in
                 let uu____17300 = FStar_Ident.string_of_id hd'  in
                 uu____17298 = uu____17300 -> aux tl tl'
             | uu____17303 -> No  in
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
        (let uu____17355 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17355 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17399 =
            let uu____17402 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17402  in
          match uu____17399 with
          | FStar_Pervasives_Native.None  ->
              let uu____17424 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17468  ->
                     match uu___2_17468 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17507 = FStar_Ident.lid_equals lid l  in
                         if uu____17507
                         then
                           let uu____17530 =
                             let uu____17549 =
                               let uu____17564 = inst_tscheme t  in
                               FStar_Util.Inl uu____17564  in
                             let uu____17579 = FStar_Ident.range_of_lid l  in
                             (uu____17549, uu____17579)  in
                           FStar_Pervasives_Native.Some uu____17530
                         else FStar_Pervasives_Native.None
                     | uu____17632 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17424
                (fun uu____17670  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17680  ->
                        match uu___3_17680 with
                        | (uu____17683,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17685);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17686;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17687;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17688;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17689;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17690;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17712 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17712
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
                                  uu____17764 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17771 -> cache t  in
                            let uu____17772 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17772 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17778 =
                                   let uu____17779 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17779)
                                    in
                                 maybe_cache uu____17778)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17850 = find_in_sigtab env1 lid  in
         match uu____17850 with
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
      let uu____17931 = lookup_qname env1 lid  in
      match uu____17931 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17952,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____18066 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____18066 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____18111 =
          let uu____18114 = lookup_attr env2 attr  in se1 :: uu____18114  in
        FStar_Util.smap_add (attrtab env2) attr uu____18111  in
      FStar_List.iter
        (fun attr  ->
           let uu____18124 =
             let uu____18125 = FStar_Syntax_Subst.compress attr  in
             uu____18125.FStar_Syntax_Syntax.n  in
           match uu____18124 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18129 =
                 let uu____18131 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____18131  in
               add_one env1 se uu____18129
           | uu____18132 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18155) ->
          add_sigelts env1 ses
      | uu____18164 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____18172 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____18172 se) lids;
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
        (fun uu___4_18206  ->
           match uu___4_18206 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____18216 =
                 let uu____18223 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____18223)  in
               FStar_Pervasives_Native.Some uu____18216
           | uu____18232 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18294,lb::[]),uu____18296) ->
            let uu____18305 =
              let uu____18314 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18323 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18314, uu____18323)  in
            FStar_Pervasives_Native.Some uu____18305
        | FStar_Syntax_Syntax.Sig_let ((uu____18336,lbs),uu____18338) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18370 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18383 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18383
                     then
                       let uu____18396 =
                         let uu____18405 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18414 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18405, uu____18414)  in
                       FStar_Pervasives_Native.Some uu____18396
                     else FStar_Pervasives_Native.None)
        | uu____18437 -> FStar_Pervasives_Native.None
  
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
                    let uu____18529 =
                      let uu____18531 =
                        let uu____18533 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18535 =
                          let uu____18537 =
                            let uu____18539 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18545 =
                              let uu____18547 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18547  in
                            Prims.op_Hat uu____18539 uu____18545  in
                          Prims.op_Hat ", expected " uu____18537  in
                        Prims.op_Hat uu____18533 uu____18535  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18531
                       in
                    failwith uu____18529
                  else ());
             (let uu____18554 =
                let uu____18563 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18563, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18554))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18583,uu____18584) ->
            let uu____18589 =
              let uu____18598 =
                let uu____18603 =
                  let uu____18604 =
                    let uu____18607 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18607  in
                  (us, uu____18604)  in
                inst_ts us_opt uu____18603  in
              (uu____18598, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18589
        | uu____18626 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18715 =
          match uu____18715 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18811,uvs,t,uu____18814,uu____18815,uu____18816);
                      FStar_Syntax_Syntax.sigrng = uu____18817;
                      FStar_Syntax_Syntax.sigquals = uu____18818;
                      FStar_Syntax_Syntax.sigmeta = uu____18819;
                      FStar_Syntax_Syntax.sigattrs = uu____18820;
                      FStar_Syntax_Syntax.sigopts = uu____18821;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18846 =
                     let uu____18855 = inst_tscheme1 (uvs, t)  in
                     (uu____18855, rng)  in
                   FStar_Pervasives_Native.Some uu____18846
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18879;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18881;
                      FStar_Syntax_Syntax.sigattrs = uu____18882;
                      FStar_Syntax_Syntax.sigopts = uu____18883;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18902 =
                     let uu____18904 = in_cur_mod env1 l  in
                     uu____18904 = Yes  in
                   if uu____18902
                   then
                     let uu____18916 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18916
                      then
                        let uu____18932 =
                          let uu____18941 = inst_tscheme1 (uvs, t)  in
                          (uu____18941, rng)  in
                        FStar_Pervasives_Native.Some uu____18932
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18974 =
                        let uu____18983 = inst_tscheme1 (uvs, t)  in
                        (uu____18983, rng)  in
                      FStar_Pervasives_Native.Some uu____18974)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19008,uu____19009);
                      FStar_Syntax_Syntax.sigrng = uu____19010;
                      FStar_Syntax_Syntax.sigquals = uu____19011;
                      FStar_Syntax_Syntax.sigmeta = uu____19012;
                      FStar_Syntax_Syntax.sigattrs = uu____19013;
                      FStar_Syntax_Syntax.sigopts = uu____19014;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____19057 =
                          let uu____19066 = inst_tscheme1 (uvs, k)  in
                          (uu____19066, rng)  in
                        FStar_Pervasives_Native.Some uu____19057
                    | uu____19087 ->
                        let uu____19088 =
                          let uu____19097 =
                            let uu____19102 =
                              let uu____19103 =
                                let uu____19106 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19106
                                 in
                              (uvs, uu____19103)  in
                            inst_tscheme1 uu____19102  in
                          (uu____19097, rng)  in
                        FStar_Pervasives_Native.Some uu____19088)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19129,uu____19130);
                      FStar_Syntax_Syntax.sigrng = uu____19131;
                      FStar_Syntax_Syntax.sigquals = uu____19132;
                      FStar_Syntax_Syntax.sigmeta = uu____19133;
                      FStar_Syntax_Syntax.sigattrs = uu____19134;
                      FStar_Syntax_Syntax.sigopts = uu____19135;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19179 =
                          let uu____19188 = inst_tscheme_with (uvs, k) us  in
                          (uu____19188, rng)  in
                        FStar_Pervasives_Native.Some uu____19179
                    | uu____19209 ->
                        let uu____19210 =
                          let uu____19219 =
                            let uu____19224 =
                              let uu____19225 =
                                let uu____19228 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19228
                                 in
                              (uvs, uu____19225)  in
                            inst_tscheme_with uu____19224 us  in
                          (uu____19219, rng)  in
                        FStar_Pervasives_Native.Some uu____19210)
               | FStar_Util.Inr se ->
                   let uu____19264 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19285;
                          FStar_Syntax_Syntax.sigrng = uu____19286;
                          FStar_Syntax_Syntax.sigquals = uu____19287;
                          FStar_Syntax_Syntax.sigmeta = uu____19288;
                          FStar_Syntax_Syntax.sigattrs = uu____19289;
                          FStar_Syntax_Syntax.sigopts = uu____19290;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19307 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____19264
                     (FStar_Util.map_option
                        (fun uu____19355  ->
                           match uu____19355 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19386 =
          let uu____19397 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19397 mapper  in
        match uu____19386 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19471 =
              let uu____19482 =
                let uu____19489 =
                  let uu___858_19492 = t  in
                  let uu____19493 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19492.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19493;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19492.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19489)  in
              (uu____19482, r)  in
            FStar_Pervasives_Native.Some uu____19471
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19542 = lookup_qname env1 l  in
      match uu____19542 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19563 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19617 = try_lookup_bv env1 bv  in
      match uu____19617 with
      | FStar_Pervasives_Native.None  ->
          let uu____19632 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19632 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19648 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19649 =
            let uu____19650 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19650  in
          (uu____19648, uu____19649)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19672 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19672 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19738 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19738  in
          let uu____19739 =
            let uu____19748 =
              let uu____19753 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19753)  in
            (uu____19748, r1)  in
          FStar_Pervasives_Native.Some uu____19739
  
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
        let uu____19788 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19788 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19821,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19846 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19846  in
            let uu____19847 =
              let uu____19852 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19852, r1)  in
            FStar_Pervasives_Native.Some uu____19847
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19876 = try_lookup_lid env1 l  in
      match uu____19876 with
      | FStar_Pervasives_Native.None  ->
          let uu____19903 = name_not_found l  in
          let uu____19909 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19903 uu____19909
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19954  ->
              match uu___5_19954 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19957 = FStar_Ident.string_of_id x  in
                  let uu____19959 = FStar_Ident.string_of_id y  in
                  uu____19957 = uu____19959
              | uu____19962 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19983 = lookup_qname env1 lid  in
      match uu____19983 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19992,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19995;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19997;
              FStar_Syntax_Syntax.sigattrs = uu____19998;
              FStar_Syntax_Syntax.sigopts = uu____19999;_},FStar_Pervasives_Native.None
            ),uu____20000)
          ->
          let uu____20051 =
            let uu____20058 =
              let uu____20059 =
                let uu____20062 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____20062 t  in
              (uvs, uu____20059)  in
            (uu____20058, q)  in
          FStar_Pervasives_Native.Some uu____20051
      | uu____20075 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____20097 = lookup_qname env1 lid  in
      match uu____20097 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20102,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20105;
              FStar_Syntax_Syntax.sigquals = uu____20106;
              FStar_Syntax_Syntax.sigmeta = uu____20107;
              FStar_Syntax_Syntax.sigattrs = uu____20108;
              FStar_Syntax_Syntax.sigopts = uu____20109;_},FStar_Pervasives_Native.None
            ),uu____20110)
          ->
          let uu____20161 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20161 (uvs, t)
      | uu____20166 ->
          let uu____20167 = name_not_found lid  in
          let uu____20173 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20167 uu____20173
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____20193 = lookup_qname env1 lid  in
      match uu____20193 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20198,uvs,t,uu____20201,uu____20202,uu____20203);
              FStar_Syntax_Syntax.sigrng = uu____20204;
              FStar_Syntax_Syntax.sigquals = uu____20205;
              FStar_Syntax_Syntax.sigmeta = uu____20206;
              FStar_Syntax_Syntax.sigattrs = uu____20207;
              FStar_Syntax_Syntax.sigopts = uu____20208;_},FStar_Pervasives_Native.None
            ),uu____20209)
          ->
          let uu____20266 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20266 (uvs, t)
      | uu____20271 ->
          let uu____20272 = name_not_found lid  in
          let uu____20278 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20272 uu____20278
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____20301 = lookup_qname env1 lid  in
      match uu____20301 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20309,uu____20310,uu____20311,uu____20312,uu____20313,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20315;
              FStar_Syntax_Syntax.sigquals = uu____20316;
              FStar_Syntax_Syntax.sigmeta = uu____20317;
              FStar_Syntax_Syntax.sigattrs = uu____20318;
              FStar_Syntax_Syntax.sigopts = uu____20319;_},uu____20320),uu____20321)
          -> (true, dcs)
      | uu____20386 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20402 = lookup_qname env1 lid  in
      match uu____20402 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20403,uu____20404,uu____20405,l,uu____20407,uu____20408);
              FStar_Syntax_Syntax.sigrng = uu____20409;
              FStar_Syntax_Syntax.sigquals = uu____20410;
              FStar_Syntax_Syntax.sigmeta = uu____20411;
              FStar_Syntax_Syntax.sigattrs = uu____20412;
              FStar_Syntax_Syntax.sigopts = uu____20413;_},uu____20414),uu____20415)
          -> l
      | uu____20474 ->
          let uu____20475 =
            let uu____20477 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20477  in
          failwith uu____20475
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20547)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20604) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20628 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20628
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20663 -> FStar_Pervasives_Native.None)
          | uu____20672 -> FStar_Pervasives_Native.None
  
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
        let uu____20734 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20734
  
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
        let uu____20767 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20767
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20791 =
        let uu____20793 = FStar_Ident.nsstr lid  in uu____20793 = "Prims"  in
      if uu____20791
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20823,uu____20824) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20873),uu____20874) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20923 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20941 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20951 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20968 ->
                  let uu____20975 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20975
              | FStar_Syntax_Syntax.Sig_let ((uu____20976,lbs),uu____20978)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20994 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20994
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____21001 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____21017 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____21027 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____21034 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____21035 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21036 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____21049 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____21050 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____21073 =
        let uu____21075 = FStar_Ident.nsstr lid  in uu____21075 = "Prims"  in
      if uu____21073
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____21082 =
           let uu____21085 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____21085
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____21082
           (fun d_opt  ->
              let uu____21097 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____21097
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21107 =
                   let uu____21110 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21110  in
                 match uu____21107 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21111 =
                       let uu____21113 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21113
                        in
                     failwith uu____21111
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21118 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21118
                       then
                         let uu____21121 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21123 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21125 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21121 uu____21123 uu____21125
                       else ());
                      (let uu____21131 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____21131 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21152),uu____21153) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21202 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21224),uu____21225) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21274 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____21296 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21296
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21329 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____21329 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21351 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21360 =
                        let uu____21361 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21361.FStar_Syntax_Syntax.n  in
                      match uu____21360 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21366 -> false))
               in
            (true, uu____21351)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21389 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21389
  
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
          let uu____21461 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21461  in
        let uu____21462 = FStar_Util.smap_try_find tab s  in
        match uu____21462 with
        | FStar_Pervasives_Native.None  ->
            let uu____21465 = f ()  in
            (match uu____21465 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21503 =
        let uu____21504 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21504 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21538 =
        let uu____21539 = FStar_Syntax_Util.unrefine t  in
        uu____21539.FStar_Syntax_Syntax.n  in
      match uu____21538 with
      | FStar_Syntax_Syntax.Tm_type uu____21543 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21547) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21573) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21578,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21600 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21633 =
        let attrs =
          let uu____21639 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21639  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21679 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21679)
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
      let uu____21724 = lookup_qname env1 ftv  in
      match uu____21724 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21728) ->
          let uu____21773 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21773 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21794,t),r) ->
               let uu____21809 =
                 let uu____21810 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21810 t  in
               FStar_Pervasives_Native.Some uu____21809)
      | uu____21811 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21823 = try_lookup_effect_lid env1 ftv  in
      match uu____21823 with
      | FStar_Pervasives_Native.None  ->
          let uu____21826 = name_not_found ftv  in
          let uu____21832 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21826 uu____21832
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
        let uu____21856 = lookup_qname env1 lid0  in
        match uu____21856 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21867);
                FStar_Syntax_Syntax.sigrng = uu____21868;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21870;
                FStar_Syntax_Syntax.sigattrs = uu____21871;
                FStar_Syntax_Syntax.sigopts = uu____21872;_},FStar_Pervasives_Native.None
              ),uu____21873)
            ->
            let lid1 =
              let uu____21929 =
                let uu____21930 = FStar_Ident.range_of_lid lid  in
                let uu____21931 =
                  let uu____21932 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21932  in
                FStar_Range.set_use_range uu____21930 uu____21931  in
              FStar_Ident.set_lid_range lid uu____21929  in
            let uu____21933 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21939  ->
                      match uu___6_21939 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21942 -> false))
               in
            if uu____21933
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21961 =
                      let uu____21963 =
                        let uu____21965 = get_range env1  in
                        FStar_Range.string_of_range uu____21965  in
                      let uu____21966 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21968 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21963 uu____21966 uu____21968
                       in
                    failwith uu____21961)
                  in
               match (binders, univs) with
               | ([],uu____21989) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____22015,uu____22016::uu____22017::uu____22018) ->
                   let uu____22039 =
                     let uu____22041 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____22043 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____22041 uu____22043
                      in
                   failwith uu____22039
               | uu____22054 ->
                   let uu____22069 =
                     let uu____22074 =
                       let uu____22075 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____22075)  in
                     inst_tscheme_with uu____22074 insts  in
                   (match uu____22069 with
                    | (uu____22088,t) ->
                        let t1 =
                          let uu____22091 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____22091 t  in
                        let uu____22092 =
                          let uu____22093 = FStar_Syntax_Subst.compress t1
                             in
                          uu____22093.FStar_Syntax_Syntax.n  in
                        (match uu____22092 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22128 -> failwith "Impossible")))
        | uu____22136 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____22160 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22160 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22173,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22180 = find l2  in
            (match uu____22180 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22187 =
          let uu____22190 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____22190  in
        match uu____22187 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22193 = find l  in
            (match uu____22193 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____22198 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____22198
                     m);
                  m))
         in
      let uu____22200 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22200
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22221 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____22221 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22227) ->
            FStar_List.length bs
        | uu____22266 ->
            let uu____22267 =
              let uu____22273 =
                let uu____22275 = FStar_Ident.string_of_lid name  in
                let uu____22277 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22275 uu____22277
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22273)
               in
            FStar_Errors.raise_error uu____22267 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____22296 = lookup_qname env1 l1  in
      match uu____22296 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22299;
              FStar_Syntax_Syntax.sigrng = uu____22300;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22302;
              FStar_Syntax_Syntax.sigattrs = uu____22303;
              FStar_Syntax_Syntax.sigopts = uu____22304;_},uu____22305),uu____22306)
          -> q
      | uu____22359 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22383 =
          let uu____22384 =
            let uu____22386 = FStar_Util.string_of_int i  in
            let uu____22388 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22386 uu____22388
             in
          failwith uu____22384  in
        let uu____22391 = lookup_datacon env1 lid  in
        match uu____22391 with
        | (uu____22396,t) ->
            let uu____22398 =
              let uu____22399 = FStar_Syntax_Subst.compress t  in
              uu____22399.FStar_Syntax_Syntax.n  in
            (match uu____22398 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22403) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22449 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22463 = lookup_qname env1 l  in
      match uu____22463 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22465,uu____22466,uu____22467);
              FStar_Syntax_Syntax.sigrng = uu____22468;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22470;
              FStar_Syntax_Syntax.sigattrs = uu____22471;
              FStar_Syntax_Syntax.sigopts = uu____22472;_},uu____22473),uu____22474)
          ->
          FStar_Util.for_some
            (fun uu___7_22529  ->
               match uu___7_22529 with
               | FStar_Syntax_Syntax.Projector uu____22531 -> true
               | uu____22537 -> false) quals
      | uu____22539 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22553 = lookup_qname env1 lid  in
      match uu____22553 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22555,uu____22556,uu____22557,uu____22558,uu____22559,uu____22560);
              FStar_Syntax_Syntax.sigrng = uu____22561;
              FStar_Syntax_Syntax.sigquals = uu____22562;
              FStar_Syntax_Syntax.sigmeta = uu____22563;
              FStar_Syntax_Syntax.sigattrs = uu____22564;
              FStar_Syntax_Syntax.sigopts = uu____22565;_},uu____22566),uu____22567)
          -> true
      | uu____22627 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22641 = lookup_qname env1 lid  in
      match uu____22641 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22643,uu____22644,uu____22645,uu____22646,uu____22647,uu____22648);
              FStar_Syntax_Syntax.sigrng = uu____22649;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22651;
              FStar_Syntax_Syntax.sigattrs = uu____22652;
              FStar_Syntax_Syntax.sigopts = uu____22653;_},uu____22654),uu____22655)
          ->
          FStar_Util.for_some
            (fun uu___8_22718  ->
               match uu___8_22718 with
               | FStar_Syntax_Syntax.RecordType uu____22720 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22730 -> true
               | uu____22740 -> false) quals
      | uu____22742 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22752,uu____22753);
            FStar_Syntax_Syntax.sigrng = uu____22754;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22756;
            FStar_Syntax_Syntax.sigattrs = uu____22757;
            FStar_Syntax_Syntax.sigopts = uu____22758;_},uu____22759),uu____22760)
        ->
        FStar_Util.for_some
          (fun uu___9_22819  ->
             match uu___9_22819 with
             | FStar_Syntax_Syntax.Action uu____22821 -> true
             | uu____22823 -> false) quals
    | uu____22825 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22839 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22839
  
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
      let uu____22856 =
        let uu____22857 = FStar_Syntax_Util.un_uinst head  in
        uu____22857.FStar_Syntax_Syntax.n  in
      match uu____22856 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22863 ->
               true
           | uu____22866 -> false)
      | uu____22868 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22882 = lookup_qname env1 l  in
      match uu____22882 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22885),uu____22886) ->
          FStar_Util.for_some
            (fun uu___10_22934  ->
               match uu___10_22934 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22937 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22939 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____23015 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____23033) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____23051 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____23059 ->
                 FStar_Pervasives_Native.Some true
             | uu____23078 -> FStar_Pervasives_Native.Some false)
         in
      let uu____23081 =
        let uu____23085 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____23085 mapper  in
      match uu____23081 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____23145 = lookup_qname env1 lid  in
      match uu____23145 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23149,uu____23150,tps,uu____23152,uu____23153,uu____23154);
              FStar_Syntax_Syntax.sigrng = uu____23155;
              FStar_Syntax_Syntax.sigquals = uu____23156;
              FStar_Syntax_Syntax.sigmeta = uu____23157;
              FStar_Syntax_Syntax.sigattrs = uu____23158;
              FStar_Syntax_Syntax.sigopts = uu____23159;_},uu____23160),uu____23161)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23229 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23275  ->
              match uu____23275 with
              | (d,uu____23284) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____23300 = effect_decl_opt env1 l  in
      match uu____23300 with
      | FStar_Pervasives_Native.None  ->
          let uu____23315 = name_not_found l  in
          let uu____23321 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23315 uu____23321
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23349 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23349 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23356  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23370  ->
            fun uu____23371  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23405 = FStar_Ident.lid_equals l1 l2  in
        if uu____23405
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23424 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23424
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23443 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23496  ->
                        match uu____23496 with
                        | (m1,m2,uu____23510,uu____23511,uu____23512) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23443 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23537,uu____23538,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23586 = join_opt env1 l1 l2  in
        match uu____23586 with
        | FStar_Pervasives_Native.None  ->
            let uu____23607 =
              let uu____23613 =
                let uu____23615 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23617 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23615 uu____23617
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23613)  in
            FStar_Errors.raise_error uu____23607 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23660 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23660
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
  'uuuuuu23680 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23680) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23709 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23735  ->
                match uu____23735 with
                | (d,uu____23742) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23709 with
      | FStar_Pervasives_Native.None  ->
          let uu____23753 =
            let uu____23755 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23755
             in
          failwith uu____23753
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23770 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23770 with
           | (uu____23781,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23799)::(wp,uu____23801)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23857 -> failwith "Impossible"))
  
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
        | uu____23922 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23935 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23935 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23952 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23952 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23977 =
                     let uu____23983 =
                       let uu____23985 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23993 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____24004 =
                         let uu____24006 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____24006  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23985 uu____23993 uu____24004
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23983)
                      in
                   FStar_Errors.raise_error uu____23977
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____24014 =
                     let uu____24025 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____24025 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____24062  ->
                        fun uu____24063  ->
                          match (uu____24062, uu____24063) with
                          | ((x,uu____24093),(t,uu____24095)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____24014
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____24126 =
                     let uu___1612_24127 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1612_24127.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1612_24127.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1612_24127.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1612_24127.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24126
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu24139 .
    'uuuuuu24139 ->
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
            let uu____24180 =
              let uu____24187 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____24187)  in
            match uu____24180 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24211 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24213 = FStar_Util.string_of_int given  in
                     let uu____24215 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24211 uu____24213 uu____24215
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24220 = effect_decl_opt env1 effect_name  in
          match uu____24220 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24242) ->
              let uu____24253 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24253 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24271 =
                       let uu____24274 =
                         let uu____24275 =
                           let uu____24292 =
                             let uu____24303 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg
                                in
                             uu____24303 ::
                               (c1.FStar_Syntax_Syntax.effect_args)
                              in
                           (repr, uu____24292)  in
                         FStar_Syntax_Syntax.Tm_app uu____24275  in
                       let uu____24340 = get_range env1  in
                       FStar_Syntax_Syntax.mk uu____24274 uu____24340  in
                     FStar_Pervasives_Native.Some uu____24271)))
  
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
           (fun uu___11_24404  ->
              match uu___11_24404 with
              | FStar_Syntax_Syntax.Reflectable uu____24406 -> true
              | uu____24408 -> false))
  
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
      | uu____24468 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24483 =
        let uu____24484 = FStar_Syntax_Subst.compress t  in
        uu____24484.FStar_Syntax_Syntax.n  in
      match uu____24483 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24488,c) ->
          is_reifiable_comp env1 c
      | uu____24510 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24530 =
           let uu____24532 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24532  in
         if uu____24530
         then
           let uu____24535 =
             let uu____24541 =
               let uu____24543 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24543
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24541)  in
           let uu____24547 = get_range env1  in
           FStar_Errors.raise_error uu____24535 uu____24547
         else ());
        (let uu____24550 = effect_repr_aux true env1 c u_c  in
         match uu____24550 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1689_24586 = env1  in
        {
          solver = (uu___1689_24586.solver);
          range = (uu___1689_24586.range);
          curmodule = (uu___1689_24586.curmodule);
          gamma = (uu___1689_24586.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1689_24586.gamma_cache);
          modules = (uu___1689_24586.modules);
          expected_typ = (uu___1689_24586.expected_typ);
          sigtab = (uu___1689_24586.sigtab);
          attrtab = (uu___1689_24586.attrtab);
          instantiate_imp = (uu___1689_24586.instantiate_imp);
          effects = (uu___1689_24586.effects);
          generalize = (uu___1689_24586.generalize);
          letrecs = (uu___1689_24586.letrecs);
          top_level = (uu___1689_24586.top_level);
          check_uvars = (uu___1689_24586.check_uvars);
          use_eq = (uu___1689_24586.use_eq);
          use_eq_strict = (uu___1689_24586.use_eq_strict);
          is_iface = (uu___1689_24586.is_iface);
          admit = (uu___1689_24586.admit);
          lax = (uu___1689_24586.lax);
          lax_universes = (uu___1689_24586.lax_universes);
          phase1 = (uu___1689_24586.phase1);
          failhard = (uu___1689_24586.failhard);
          nosynth = (uu___1689_24586.nosynth);
          uvar_subtyping = (uu___1689_24586.uvar_subtyping);
          tc_term = (uu___1689_24586.tc_term);
          type_of = (uu___1689_24586.type_of);
          universe_of = (uu___1689_24586.universe_of);
          check_type_of = (uu___1689_24586.check_type_of);
          use_bv_sorts = (uu___1689_24586.use_bv_sorts);
          qtbl_name_and_index = (uu___1689_24586.qtbl_name_and_index);
          normalized_eff_names = (uu___1689_24586.normalized_eff_names);
          fv_delta_depths = (uu___1689_24586.fv_delta_depths);
          proof_ns = (uu___1689_24586.proof_ns);
          synth_hook = (uu___1689_24586.synth_hook);
          try_solve_implicits_hook =
            (uu___1689_24586.try_solve_implicits_hook);
          splice = (uu___1689_24586.splice);
          mpreprocess = (uu___1689_24586.mpreprocess);
          postprocess = (uu___1689_24586.postprocess);
          identifier_info = (uu___1689_24586.identifier_info);
          tc_hooks = (uu___1689_24586.tc_hooks);
          dsenv = (uu___1689_24586.dsenv);
          nbe = (uu___1689_24586.nbe);
          strict_args_tab = (uu___1689_24586.strict_args_tab);
          erasable_types_tab = (uu___1689_24586.erasable_types_tab);
          enable_defer_to_tac = (uu___1689_24586.enable_defer_to_tac)
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
    fun uu____24605  ->
      match uu____24605 with
      | (ed,quals) ->
          let effects1 =
            let uu___1698_24619 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1698_24619.order);
              joins = (uu___1698_24619.joins);
              polymonadic_binds = (uu___1698_24619.polymonadic_binds)
            }  in
          let uu___1701_24628 = env1  in
          {
            solver = (uu___1701_24628.solver);
            range = (uu___1701_24628.range);
            curmodule = (uu___1701_24628.curmodule);
            gamma = (uu___1701_24628.gamma);
            gamma_sig = (uu___1701_24628.gamma_sig);
            gamma_cache = (uu___1701_24628.gamma_cache);
            modules = (uu___1701_24628.modules);
            expected_typ = (uu___1701_24628.expected_typ);
            sigtab = (uu___1701_24628.sigtab);
            attrtab = (uu___1701_24628.attrtab);
            instantiate_imp = (uu___1701_24628.instantiate_imp);
            effects = effects1;
            generalize = (uu___1701_24628.generalize);
            letrecs = (uu___1701_24628.letrecs);
            top_level = (uu___1701_24628.top_level);
            check_uvars = (uu___1701_24628.check_uvars);
            use_eq = (uu___1701_24628.use_eq);
            use_eq_strict = (uu___1701_24628.use_eq_strict);
            is_iface = (uu___1701_24628.is_iface);
            admit = (uu___1701_24628.admit);
            lax = (uu___1701_24628.lax);
            lax_universes = (uu___1701_24628.lax_universes);
            phase1 = (uu___1701_24628.phase1);
            failhard = (uu___1701_24628.failhard);
            nosynth = (uu___1701_24628.nosynth);
            uvar_subtyping = (uu___1701_24628.uvar_subtyping);
            tc_term = (uu___1701_24628.tc_term);
            type_of = (uu___1701_24628.type_of);
            universe_of = (uu___1701_24628.universe_of);
            check_type_of = (uu___1701_24628.check_type_of);
            use_bv_sorts = (uu___1701_24628.use_bv_sorts);
            qtbl_name_and_index = (uu___1701_24628.qtbl_name_and_index);
            normalized_eff_names = (uu___1701_24628.normalized_eff_names);
            fv_delta_depths = (uu___1701_24628.fv_delta_depths);
            proof_ns = (uu___1701_24628.proof_ns);
            synth_hook = (uu___1701_24628.synth_hook);
            try_solve_implicits_hook =
              (uu___1701_24628.try_solve_implicits_hook);
            splice = (uu___1701_24628.splice);
            mpreprocess = (uu___1701_24628.mpreprocess);
            postprocess = (uu___1701_24628.postprocess);
            identifier_info = (uu___1701_24628.identifier_info);
            tc_hooks = (uu___1701_24628.tc_hooks);
            dsenv = (uu___1701_24628.dsenv);
            nbe = (uu___1701_24628.nbe);
            strict_args_tab = (uu___1701_24628.strict_args_tab);
            erasable_types_tab = (uu___1701_24628.erasable_types_tab);
            enable_defer_to_tac = (uu___1701_24628.enable_defer_to_tac)
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
        let uu____24657 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24725  ->
                  match uu____24725 with
                  | (m1,n1,uu____24743,uu____24744) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24657 with
        | FStar_Pervasives_Native.Some (uu____24769,uu____24770,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24815 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24890 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24890
                  (fun uu____24911  ->
                     match uu____24911 with
                     | (c1,g1) ->
                         let uu____24922 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24922
                           (fun uu____24943  ->
                              match uu____24943 with
                              | (c2,g2) ->
                                  let uu____24954 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24954)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____25076 = l1 u t e  in
                              l2 u t uu____25076))
                | uu____25077 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25145  ->
                    match uu____25145 with
                    | (e,uu____25153) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25176 =
            match uu____25176 with
            | (i,j) ->
                let uu____25187 = FStar_Ident.lid_equals i j  in
                if uu____25187
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____25194  ->
                       FStar_Pervasives_Native.Some uu____25194)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25223 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25233 = FStar_Ident.lid_equals i k  in
                        if uu____25233
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25247 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25247
                                  then []
                                  else
                                    (let uu____25254 =
                                       let uu____25263 =
                                         find_edge order1 (i, k)  in
                                       let uu____25266 =
                                         find_edge order1 (k, j)  in
                                       (uu____25263, uu____25266)  in
                                     match uu____25254 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25281 =
                                           compose_edges e1 e2  in
                                         [uu____25281]
                                     | uu____25282 -> [])))))
                 in
              FStar_List.append order1 uu____25223  in
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
                  let uu____25312 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25315 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____25315
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25312
                  then
                    let uu____25322 =
                      let uu____25328 =
                        let uu____25330 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25330
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25328)
                       in
                    let uu____25334 = get_range env1  in
                    FStar_Errors.raise_error uu____25322 uu____25334
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25412 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25412
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25464 =
                                             let uu____25473 =
                                               find_edge order2 (i, k)  in
                                             let uu____25476 =
                                               find_edge order2 (j, k)  in
                                             (uu____25473, uu____25476)  in
                                           match uu____25464 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25518,uu____25519)
                                                    ->
                                                    let uu____25526 =
                                                      let uu____25533 =
                                                        let uu____25535 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25535
                                                         in
                                                      let uu____25538 =
                                                        let uu____25540 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25540
                                                         in
                                                      (uu____25533,
                                                        uu____25538)
                                                       in
                                                    (match uu____25526 with
                                                     | (true ,true ) ->
                                                         let uu____25557 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25557
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
                                           | uu____25600 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25652 =
                                   let uu____25654 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25654
                                     FStar_Util.is_some
                                    in
                                 if uu____25652
                                 then
                                   let uu____25703 =
                                     let uu____25709 =
                                       let uu____25711 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25713 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25715 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25717 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25711 uu____25713 uu____25715
                                         uu____25717
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25709)
                                      in
                                   FStar_Errors.raise_error uu____25703
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1822_25756 = env1.effects  in
             {
               decls = (uu___1822_25756.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1822_25756.polymonadic_binds)
             }  in
           let uu___1825_25757 = env1  in
           {
             solver = (uu___1825_25757.solver);
             range = (uu___1825_25757.range);
             curmodule = (uu___1825_25757.curmodule);
             gamma = (uu___1825_25757.gamma);
             gamma_sig = (uu___1825_25757.gamma_sig);
             gamma_cache = (uu___1825_25757.gamma_cache);
             modules = (uu___1825_25757.modules);
             expected_typ = (uu___1825_25757.expected_typ);
             sigtab = (uu___1825_25757.sigtab);
             attrtab = (uu___1825_25757.attrtab);
             instantiate_imp = (uu___1825_25757.instantiate_imp);
             effects = effects1;
             generalize = (uu___1825_25757.generalize);
             letrecs = (uu___1825_25757.letrecs);
             top_level = (uu___1825_25757.top_level);
             check_uvars = (uu___1825_25757.check_uvars);
             use_eq = (uu___1825_25757.use_eq);
             use_eq_strict = (uu___1825_25757.use_eq_strict);
             is_iface = (uu___1825_25757.is_iface);
             admit = (uu___1825_25757.admit);
             lax = (uu___1825_25757.lax);
             lax_universes = (uu___1825_25757.lax_universes);
             phase1 = (uu___1825_25757.phase1);
             failhard = (uu___1825_25757.failhard);
             nosynth = (uu___1825_25757.nosynth);
             uvar_subtyping = (uu___1825_25757.uvar_subtyping);
             tc_term = (uu___1825_25757.tc_term);
             type_of = (uu___1825_25757.type_of);
             universe_of = (uu___1825_25757.universe_of);
             check_type_of = (uu___1825_25757.check_type_of);
             use_bv_sorts = (uu___1825_25757.use_bv_sorts);
             qtbl_name_and_index = (uu___1825_25757.qtbl_name_and_index);
             normalized_eff_names = (uu___1825_25757.normalized_eff_names);
             fv_delta_depths = (uu___1825_25757.fv_delta_depths);
             proof_ns = (uu___1825_25757.proof_ns);
             synth_hook = (uu___1825_25757.synth_hook);
             try_solve_implicits_hook =
               (uu___1825_25757.try_solve_implicits_hook);
             splice = (uu___1825_25757.splice);
             mpreprocess = (uu___1825_25757.mpreprocess);
             postprocess = (uu___1825_25757.postprocess);
             identifier_info = (uu___1825_25757.identifier_info);
             tc_hooks = (uu___1825_25757.tc_hooks);
             dsenv = (uu___1825_25757.dsenv);
             nbe = (uu___1825_25757.nbe);
             strict_args_tab = (uu___1825_25757.strict_args_tab);
             erasable_types_tab = (uu___1825_25757.erasable_types_tab);
             enable_defer_to_tac = (uu___1825_25757.enable_defer_to_tac)
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
              let uu____25805 = FStar_Ident.string_of_lid m  in
              let uu____25807 = FStar_Ident.string_of_lid n  in
              let uu____25809 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25805 uu____25807 uu____25809
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25818 =
              let uu____25820 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25820 FStar_Util.is_some  in
            if uu____25818
            then
              let uu____25857 =
                let uu____25863 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25863)
                 in
              FStar_Errors.raise_error uu____25857 env1.range
            else
              (let uu____25869 =
                 let uu____25871 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25871 FStar_Util.is_some  in
               if uu____25869
               then
                 let uu____25896 =
                   let uu____25902 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25902)
                    in
                 FStar_Errors.raise_error uu____25896 env1.range
               else
                 (let uu___1840_25908 = env1  in
                  {
                    solver = (uu___1840_25908.solver);
                    range = (uu___1840_25908.range);
                    curmodule = (uu___1840_25908.curmodule);
                    gamma = (uu___1840_25908.gamma);
                    gamma_sig = (uu___1840_25908.gamma_sig);
                    gamma_cache = (uu___1840_25908.gamma_cache);
                    modules = (uu___1840_25908.modules);
                    expected_typ = (uu___1840_25908.expected_typ);
                    sigtab = (uu___1840_25908.sigtab);
                    attrtab = (uu___1840_25908.attrtab);
                    instantiate_imp = (uu___1840_25908.instantiate_imp);
                    effects =
                      (let uu___1842_25910 = env1.effects  in
                       {
                         decls = (uu___1842_25910.decls);
                         order = (uu___1842_25910.order);
                         joins = (uu___1842_25910.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1840_25908.generalize);
                    letrecs = (uu___1840_25908.letrecs);
                    top_level = (uu___1840_25908.top_level);
                    check_uvars = (uu___1840_25908.check_uvars);
                    use_eq = (uu___1840_25908.use_eq);
                    use_eq_strict = (uu___1840_25908.use_eq_strict);
                    is_iface = (uu___1840_25908.is_iface);
                    admit = (uu___1840_25908.admit);
                    lax = (uu___1840_25908.lax);
                    lax_universes = (uu___1840_25908.lax_universes);
                    phase1 = (uu___1840_25908.phase1);
                    failhard = (uu___1840_25908.failhard);
                    nosynth = (uu___1840_25908.nosynth);
                    uvar_subtyping = (uu___1840_25908.uvar_subtyping);
                    tc_term = (uu___1840_25908.tc_term);
                    type_of = (uu___1840_25908.type_of);
                    universe_of = (uu___1840_25908.universe_of);
                    check_type_of = (uu___1840_25908.check_type_of);
                    use_bv_sorts = (uu___1840_25908.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1840_25908.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1840_25908.normalized_eff_names);
                    fv_delta_depths = (uu___1840_25908.fv_delta_depths);
                    proof_ns = (uu___1840_25908.proof_ns);
                    synth_hook = (uu___1840_25908.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1840_25908.try_solve_implicits_hook);
                    splice = (uu___1840_25908.splice);
                    mpreprocess = (uu___1840_25908.mpreprocess);
                    postprocess = (uu___1840_25908.postprocess);
                    identifier_info = (uu___1840_25908.identifier_info);
                    tc_hooks = (uu___1840_25908.tc_hooks);
                    dsenv = (uu___1840_25908.dsenv);
                    nbe = (uu___1840_25908.nbe);
                    strict_args_tab = (uu___1840_25908.strict_args_tab);
                    erasable_types_tab = (uu___1840_25908.erasable_types_tab);
                    enable_defer_to_tac =
                      (uu___1840_25908.enable_defer_to_tac)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1846_25982 = env1  in
      {
        solver = (uu___1846_25982.solver);
        range = (uu___1846_25982.range);
        curmodule = (uu___1846_25982.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1846_25982.gamma_sig);
        gamma_cache = (uu___1846_25982.gamma_cache);
        modules = (uu___1846_25982.modules);
        expected_typ = (uu___1846_25982.expected_typ);
        sigtab = (uu___1846_25982.sigtab);
        attrtab = (uu___1846_25982.attrtab);
        instantiate_imp = (uu___1846_25982.instantiate_imp);
        effects = (uu___1846_25982.effects);
        generalize = (uu___1846_25982.generalize);
        letrecs = (uu___1846_25982.letrecs);
        top_level = (uu___1846_25982.top_level);
        check_uvars = (uu___1846_25982.check_uvars);
        use_eq = (uu___1846_25982.use_eq);
        use_eq_strict = (uu___1846_25982.use_eq_strict);
        is_iface = (uu___1846_25982.is_iface);
        admit = (uu___1846_25982.admit);
        lax = (uu___1846_25982.lax);
        lax_universes = (uu___1846_25982.lax_universes);
        phase1 = (uu___1846_25982.phase1);
        failhard = (uu___1846_25982.failhard);
        nosynth = (uu___1846_25982.nosynth);
        uvar_subtyping = (uu___1846_25982.uvar_subtyping);
        tc_term = (uu___1846_25982.tc_term);
        type_of = (uu___1846_25982.type_of);
        universe_of = (uu___1846_25982.universe_of);
        check_type_of = (uu___1846_25982.check_type_of);
        use_bv_sorts = (uu___1846_25982.use_bv_sorts);
        qtbl_name_and_index = (uu___1846_25982.qtbl_name_and_index);
        normalized_eff_names = (uu___1846_25982.normalized_eff_names);
        fv_delta_depths = (uu___1846_25982.fv_delta_depths);
        proof_ns = (uu___1846_25982.proof_ns);
        synth_hook = (uu___1846_25982.synth_hook);
        try_solve_implicits_hook = (uu___1846_25982.try_solve_implicits_hook);
        splice = (uu___1846_25982.splice);
        mpreprocess = (uu___1846_25982.mpreprocess);
        postprocess = (uu___1846_25982.postprocess);
        identifier_info = (uu___1846_25982.identifier_info);
        tc_hooks = (uu___1846_25982.tc_hooks);
        dsenv = (uu___1846_25982.dsenv);
        nbe = (uu___1846_25982.nbe);
        strict_args_tab = (uu___1846_25982.strict_args_tab);
        erasable_types_tab = (uu___1846_25982.erasable_types_tab);
        enable_defer_to_tac = (uu___1846_25982.enable_defer_to_tac)
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
            (let uu___1859_26040 = env1  in
             {
               solver = (uu___1859_26040.solver);
               range = (uu___1859_26040.range);
               curmodule = (uu___1859_26040.curmodule);
               gamma = rest;
               gamma_sig = (uu___1859_26040.gamma_sig);
               gamma_cache = (uu___1859_26040.gamma_cache);
               modules = (uu___1859_26040.modules);
               expected_typ = (uu___1859_26040.expected_typ);
               sigtab = (uu___1859_26040.sigtab);
               attrtab = (uu___1859_26040.attrtab);
               instantiate_imp = (uu___1859_26040.instantiate_imp);
               effects = (uu___1859_26040.effects);
               generalize = (uu___1859_26040.generalize);
               letrecs = (uu___1859_26040.letrecs);
               top_level = (uu___1859_26040.top_level);
               check_uvars = (uu___1859_26040.check_uvars);
               use_eq = (uu___1859_26040.use_eq);
               use_eq_strict = (uu___1859_26040.use_eq_strict);
               is_iface = (uu___1859_26040.is_iface);
               admit = (uu___1859_26040.admit);
               lax = (uu___1859_26040.lax);
               lax_universes = (uu___1859_26040.lax_universes);
               phase1 = (uu___1859_26040.phase1);
               failhard = (uu___1859_26040.failhard);
               nosynth = (uu___1859_26040.nosynth);
               uvar_subtyping = (uu___1859_26040.uvar_subtyping);
               tc_term = (uu___1859_26040.tc_term);
               type_of = (uu___1859_26040.type_of);
               universe_of = (uu___1859_26040.universe_of);
               check_type_of = (uu___1859_26040.check_type_of);
               use_bv_sorts = (uu___1859_26040.use_bv_sorts);
               qtbl_name_and_index = (uu___1859_26040.qtbl_name_and_index);
               normalized_eff_names = (uu___1859_26040.normalized_eff_names);
               fv_delta_depths = (uu___1859_26040.fv_delta_depths);
               proof_ns = (uu___1859_26040.proof_ns);
               synth_hook = (uu___1859_26040.synth_hook);
               try_solve_implicits_hook =
                 (uu___1859_26040.try_solve_implicits_hook);
               splice = (uu___1859_26040.splice);
               mpreprocess = (uu___1859_26040.mpreprocess);
               postprocess = (uu___1859_26040.postprocess);
               identifier_info = (uu___1859_26040.identifier_info);
               tc_hooks = (uu___1859_26040.tc_hooks);
               dsenv = (uu___1859_26040.dsenv);
               nbe = (uu___1859_26040.nbe);
               strict_args_tab = (uu___1859_26040.strict_args_tab);
               erasable_types_tab = (uu___1859_26040.erasable_types_tab);
               enable_defer_to_tac = (uu___1859_26040.enable_defer_to_tac)
             }))
    | uu____26041 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____26070  ->
             match uu____26070 with | (x,uu____26078) -> push_bv env2 x) env1
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
            let uu___1873_26113 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1873_26113.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1873_26113.FStar_Syntax_Syntax.index);
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
        let uu____26186 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26186 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____26214 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26214)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1894_26230 = env1  in
      {
        solver = (uu___1894_26230.solver);
        range = (uu___1894_26230.range);
        curmodule = (uu___1894_26230.curmodule);
        gamma = (uu___1894_26230.gamma);
        gamma_sig = (uu___1894_26230.gamma_sig);
        gamma_cache = (uu___1894_26230.gamma_cache);
        modules = (uu___1894_26230.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1894_26230.sigtab);
        attrtab = (uu___1894_26230.attrtab);
        instantiate_imp = (uu___1894_26230.instantiate_imp);
        effects = (uu___1894_26230.effects);
        generalize = (uu___1894_26230.generalize);
        letrecs = (uu___1894_26230.letrecs);
        top_level = (uu___1894_26230.top_level);
        check_uvars = (uu___1894_26230.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1894_26230.use_eq_strict);
        is_iface = (uu___1894_26230.is_iface);
        admit = (uu___1894_26230.admit);
        lax = (uu___1894_26230.lax);
        lax_universes = (uu___1894_26230.lax_universes);
        phase1 = (uu___1894_26230.phase1);
        failhard = (uu___1894_26230.failhard);
        nosynth = (uu___1894_26230.nosynth);
        uvar_subtyping = (uu___1894_26230.uvar_subtyping);
        tc_term = (uu___1894_26230.tc_term);
        type_of = (uu___1894_26230.type_of);
        universe_of = (uu___1894_26230.universe_of);
        check_type_of = (uu___1894_26230.check_type_of);
        use_bv_sorts = (uu___1894_26230.use_bv_sorts);
        qtbl_name_and_index = (uu___1894_26230.qtbl_name_and_index);
        normalized_eff_names = (uu___1894_26230.normalized_eff_names);
        fv_delta_depths = (uu___1894_26230.fv_delta_depths);
        proof_ns = (uu___1894_26230.proof_ns);
        synth_hook = (uu___1894_26230.synth_hook);
        try_solve_implicits_hook = (uu___1894_26230.try_solve_implicits_hook);
        splice = (uu___1894_26230.splice);
        mpreprocess = (uu___1894_26230.mpreprocess);
        postprocess = (uu___1894_26230.postprocess);
        identifier_info = (uu___1894_26230.identifier_info);
        tc_hooks = (uu___1894_26230.tc_hooks);
        dsenv = (uu___1894_26230.dsenv);
        nbe = (uu___1894_26230.nbe);
        strict_args_tab = (uu___1894_26230.strict_args_tab);
        erasable_types_tab = (uu___1894_26230.erasable_types_tab);
        enable_defer_to_tac = (uu___1894_26230.enable_defer_to_tac)
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
    let uu____26261 = expected_typ env_  in
    ((let uu___1901_26267 = env_  in
      {
        solver = (uu___1901_26267.solver);
        range = (uu___1901_26267.range);
        curmodule = (uu___1901_26267.curmodule);
        gamma = (uu___1901_26267.gamma);
        gamma_sig = (uu___1901_26267.gamma_sig);
        gamma_cache = (uu___1901_26267.gamma_cache);
        modules = (uu___1901_26267.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1901_26267.sigtab);
        attrtab = (uu___1901_26267.attrtab);
        instantiate_imp = (uu___1901_26267.instantiate_imp);
        effects = (uu___1901_26267.effects);
        generalize = (uu___1901_26267.generalize);
        letrecs = (uu___1901_26267.letrecs);
        top_level = (uu___1901_26267.top_level);
        check_uvars = (uu___1901_26267.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1901_26267.use_eq_strict);
        is_iface = (uu___1901_26267.is_iface);
        admit = (uu___1901_26267.admit);
        lax = (uu___1901_26267.lax);
        lax_universes = (uu___1901_26267.lax_universes);
        phase1 = (uu___1901_26267.phase1);
        failhard = (uu___1901_26267.failhard);
        nosynth = (uu___1901_26267.nosynth);
        uvar_subtyping = (uu___1901_26267.uvar_subtyping);
        tc_term = (uu___1901_26267.tc_term);
        type_of = (uu___1901_26267.type_of);
        universe_of = (uu___1901_26267.universe_of);
        check_type_of = (uu___1901_26267.check_type_of);
        use_bv_sorts = (uu___1901_26267.use_bv_sorts);
        qtbl_name_and_index = (uu___1901_26267.qtbl_name_and_index);
        normalized_eff_names = (uu___1901_26267.normalized_eff_names);
        fv_delta_depths = (uu___1901_26267.fv_delta_depths);
        proof_ns = (uu___1901_26267.proof_ns);
        synth_hook = (uu___1901_26267.synth_hook);
        try_solve_implicits_hook = (uu___1901_26267.try_solve_implicits_hook);
        splice = (uu___1901_26267.splice);
        mpreprocess = (uu___1901_26267.mpreprocess);
        postprocess = (uu___1901_26267.postprocess);
        identifier_info = (uu___1901_26267.identifier_info);
        tc_hooks = (uu___1901_26267.tc_hooks);
        dsenv = (uu___1901_26267.dsenv);
        nbe = (uu___1901_26267.nbe);
        strict_args_tab = (uu___1901_26267.strict_args_tab);
        erasable_types_tab = (uu___1901_26267.erasable_types_tab);
        enable_defer_to_tac = (uu___1901_26267.enable_defer_to_tac)
      }), uu____26261)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26279 =
      let uu____26280 = FStar_Ident.id_of_text ""  in [uu____26280]  in
    FStar_Ident.lid_of_ids uu____26279  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____26287 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26287
        then
          let uu____26292 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26292 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1909_26320 = env1  in
       {
         solver = (uu___1909_26320.solver);
         range = (uu___1909_26320.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1909_26320.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1909_26320.expected_typ);
         sigtab = (uu___1909_26320.sigtab);
         attrtab = (uu___1909_26320.attrtab);
         instantiate_imp = (uu___1909_26320.instantiate_imp);
         effects = (uu___1909_26320.effects);
         generalize = (uu___1909_26320.generalize);
         letrecs = (uu___1909_26320.letrecs);
         top_level = (uu___1909_26320.top_level);
         check_uvars = (uu___1909_26320.check_uvars);
         use_eq = (uu___1909_26320.use_eq);
         use_eq_strict = (uu___1909_26320.use_eq_strict);
         is_iface = (uu___1909_26320.is_iface);
         admit = (uu___1909_26320.admit);
         lax = (uu___1909_26320.lax);
         lax_universes = (uu___1909_26320.lax_universes);
         phase1 = (uu___1909_26320.phase1);
         failhard = (uu___1909_26320.failhard);
         nosynth = (uu___1909_26320.nosynth);
         uvar_subtyping = (uu___1909_26320.uvar_subtyping);
         tc_term = (uu___1909_26320.tc_term);
         type_of = (uu___1909_26320.type_of);
         universe_of = (uu___1909_26320.universe_of);
         check_type_of = (uu___1909_26320.check_type_of);
         use_bv_sorts = (uu___1909_26320.use_bv_sorts);
         qtbl_name_and_index = (uu___1909_26320.qtbl_name_and_index);
         normalized_eff_names = (uu___1909_26320.normalized_eff_names);
         fv_delta_depths = (uu___1909_26320.fv_delta_depths);
         proof_ns = (uu___1909_26320.proof_ns);
         synth_hook = (uu___1909_26320.synth_hook);
         try_solve_implicits_hook =
           (uu___1909_26320.try_solve_implicits_hook);
         splice = (uu___1909_26320.splice);
         mpreprocess = (uu___1909_26320.mpreprocess);
         postprocess = (uu___1909_26320.postprocess);
         identifier_info = (uu___1909_26320.identifier_info);
         tc_hooks = (uu___1909_26320.tc_hooks);
         dsenv = (uu___1909_26320.dsenv);
         nbe = (uu___1909_26320.nbe);
         strict_args_tab = (uu___1909_26320.strict_args_tab);
         erasable_types_tab = (uu___1909_26320.erasable_types_tab);
         enable_defer_to_tac = (uu___1909_26320.enable_defer_to_tac)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26372)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26376,(uu____26377,t)))::tl
          ->
          let uu____26398 =
            let uu____26401 = FStar_Syntax_Free.uvars t  in
            ext out uu____26401  in
          aux uu____26398 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26404;
            FStar_Syntax_Syntax.index = uu____26405;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26413 =
            let uu____26416 = FStar_Syntax_Free.uvars t  in
            ext out uu____26416  in
          aux uu____26413 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26474)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26478,(uu____26479,t)))::tl
          ->
          let uu____26500 =
            let uu____26503 = FStar_Syntax_Free.univs t  in
            ext out uu____26503  in
          aux uu____26500 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26506;
            FStar_Syntax_Syntax.index = uu____26507;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26515 =
            let uu____26518 = FStar_Syntax_Free.univs t  in
            ext out uu____26518  in
          aux uu____26515 tl
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
          let uu____26580 = FStar_Util.set_add uname out  in
          aux uu____26580 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26583,(uu____26584,t)))::tl
          ->
          let uu____26605 =
            let uu____26608 = FStar_Syntax_Free.univnames t  in
            ext out uu____26608  in
          aux uu____26605 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26611;
            FStar_Syntax_Syntax.index = uu____26612;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26620 =
            let uu____26623 = FStar_Syntax_Free.univnames t  in
            ext out uu____26623  in
          aux uu____26620 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26644  ->
            match uu___12_26644 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26648 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26661 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26672 =
      let uu____26681 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26681
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26672 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26729 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26742  ->
              match uu___13_26742 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26745 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26745
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26749 = FStar_Ident.string_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26749
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26753) ->
                  let uu____26770 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26770))
       in
    FStar_All.pipe_right uu____26729 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26784  ->
    match uu___14_26784 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26790 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26790
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26813  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26868) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26901,uu____26902) -> false  in
      let uu____26916 =
        FStar_List.tryFind
          (fun uu____26938  ->
             match uu____26938 with | (p,uu____26949) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26916 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26968,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26998 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26998
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2052_27020 = e  in
        {
          solver = (uu___2052_27020.solver);
          range = (uu___2052_27020.range);
          curmodule = (uu___2052_27020.curmodule);
          gamma = (uu___2052_27020.gamma);
          gamma_sig = (uu___2052_27020.gamma_sig);
          gamma_cache = (uu___2052_27020.gamma_cache);
          modules = (uu___2052_27020.modules);
          expected_typ = (uu___2052_27020.expected_typ);
          sigtab = (uu___2052_27020.sigtab);
          attrtab = (uu___2052_27020.attrtab);
          instantiate_imp = (uu___2052_27020.instantiate_imp);
          effects = (uu___2052_27020.effects);
          generalize = (uu___2052_27020.generalize);
          letrecs = (uu___2052_27020.letrecs);
          top_level = (uu___2052_27020.top_level);
          check_uvars = (uu___2052_27020.check_uvars);
          use_eq = (uu___2052_27020.use_eq);
          use_eq_strict = (uu___2052_27020.use_eq_strict);
          is_iface = (uu___2052_27020.is_iface);
          admit = (uu___2052_27020.admit);
          lax = (uu___2052_27020.lax);
          lax_universes = (uu___2052_27020.lax_universes);
          phase1 = (uu___2052_27020.phase1);
          failhard = (uu___2052_27020.failhard);
          nosynth = (uu___2052_27020.nosynth);
          uvar_subtyping = (uu___2052_27020.uvar_subtyping);
          tc_term = (uu___2052_27020.tc_term);
          type_of = (uu___2052_27020.type_of);
          universe_of = (uu___2052_27020.universe_of);
          check_type_of = (uu___2052_27020.check_type_of);
          use_bv_sorts = (uu___2052_27020.use_bv_sorts);
          qtbl_name_and_index = (uu___2052_27020.qtbl_name_and_index);
          normalized_eff_names = (uu___2052_27020.normalized_eff_names);
          fv_delta_depths = (uu___2052_27020.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2052_27020.synth_hook);
          try_solve_implicits_hook =
            (uu___2052_27020.try_solve_implicits_hook);
          splice = (uu___2052_27020.splice);
          mpreprocess = (uu___2052_27020.mpreprocess);
          postprocess = (uu___2052_27020.postprocess);
          identifier_info = (uu___2052_27020.identifier_info);
          tc_hooks = (uu___2052_27020.tc_hooks);
          dsenv = (uu___2052_27020.dsenv);
          nbe = (uu___2052_27020.nbe);
          strict_args_tab = (uu___2052_27020.strict_args_tab);
          erasable_types_tab = (uu___2052_27020.erasable_types_tab);
          enable_defer_to_tac = (uu___2052_27020.enable_defer_to_tac)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2061_27068 = e  in
      {
        solver = (uu___2061_27068.solver);
        range = (uu___2061_27068.range);
        curmodule = (uu___2061_27068.curmodule);
        gamma = (uu___2061_27068.gamma);
        gamma_sig = (uu___2061_27068.gamma_sig);
        gamma_cache = (uu___2061_27068.gamma_cache);
        modules = (uu___2061_27068.modules);
        expected_typ = (uu___2061_27068.expected_typ);
        sigtab = (uu___2061_27068.sigtab);
        attrtab = (uu___2061_27068.attrtab);
        instantiate_imp = (uu___2061_27068.instantiate_imp);
        effects = (uu___2061_27068.effects);
        generalize = (uu___2061_27068.generalize);
        letrecs = (uu___2061_27068.letrecs);
        top_level = (uu___2061_27068.top_level);
        check_uvars = (uu___2061_27068.check_uvars);
        use_eq = (uu___2061_27068.use_eq);
        use_eq_strict = (uu___2061_27068.use_eq_strict);
        is_iface = (uu___2061_27068.is_iface);
        admit = (uu___2061_27068.admit);
        lax = (uu___2061_27068.lax);
        lax_universes = (uu___2061_27068.lax_universes);
        phase1 = (uu___2061_27068.phase1);
        failhard = (uu___2061_27068.failhard);
        nosynth = (uu___2061_27068.nosynth);
        uvar_subtyping = (uu___2061_27068.uvar_subtyping);
        tc_term = (uu___2061_27068.tc_term);
        type_of = (uu___2061_27068.type_of);
        universe_of = (uu___2061_27068.universe_of);
        check_type_of = (uu___2061_27068.check_type_of);
        use_bv_sorts = (uu___2061_27068.use_bv_sorts);
        qtbl_name_and_index = (uu___2061_27068.qtbl_name_and_index);
        normalized_eff_names = (uu___2061_27068.normalized_eff_names);
        fv_delta_depths = (uu___2061_27068.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2061_27068.synth_hook);
        try_solve_implicits_hook = (uu___2061_27068.try_solve_implicits_hook);
        splice = (uu___2061_27068.splice);
        mpreprocess = (uu___2061_27068.mpreprocess);
        postprocess = (uu___2061_27068.postprocess);
        identifier_info = (uu___2061_27068.identifier_info);
        tc_hooks = (uu___2061_27068.tc_hooks);
        dsenv = (uu___2061_27068.dsenv);
        nbe = (uu___2061_27068.nbe);
        strict_args_tab = (uu___2061_27068.strict_args_tab);
        erasable_types_tab = (uu___2061_27068.erasable_types_tab);
        enable_defer_to_tac = (uu___2061_27068.enable_defer_to_tac)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____27084 = FStar_Syntax_Free.names t  in
      let uu____27087 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____27084 uu____27087
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27110 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27110
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27120 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27120
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____27141 =
      match uu____27141 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27161 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27161)
       in
    let uu____27169 =
      let uu____27173 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____27173 FStar_List.rev  in
    FStar_All.pipe_right uu____27169 (FStar_String.concat " ")
  
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
        FStar_TypeChecker_Common.deferred_to_tac = uu____27229;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([],[]);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27247 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27247 with
                   | FStar_Pervasives_Native.Some uu____27251 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27254 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred_to_tac = uu____27264;
        FStar_TypeChecker_Common.deferred = uu____27265;
        FStar_TypeChecker_Common.univ_ineqs = uu____27266;
        FStar_TypeChecker_Common.implicits = uu____27267;_} -> true
    | uu____27277 -> false
  
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
          let uu___2107_27299 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2107_27299.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2107_27299.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2107_27299.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2107_27299.FStar_TypeChecker_Common.implicits)
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
          let uu____27338 = FStar_Options.defensive ()  in
          if uu____27338
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27344 =
              let uu____27346 =
                let uu____27348 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27348  in
              Prims.op_Negation uu____27346  in
            (if uu____27344
             then
               let uu____27355 =
                 let uu____27361 =
                   let uu____27363 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27365 =
                     let uu____27367 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27367
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27363 uu____27365
                    in
                 (FStar_Errors.Warning_Defensive, uu____27361)  in
               FStar_Errors.log_issue rng uu____27355
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
          let uu____27407 =
            let uu____27409 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27409  in
          if uu____27407
          then ()
          else
            (let uu____27414 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27414 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27440 =
            let uu____27442 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27442  in
          if uu____27440
          then ()
          else
            (let uu____27447 = bound_vars e  in
             def_check_closed_in rng msg uu____27447 t)
  
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
          let uu___2144_27486 = g  in
          let uu____27487 =
            let uu____27488 =
              let uu____27489 =
                let uu____27490 =
                  let uu____27507 =
                    let uu____27518 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____27518]  in
                  (f, uu____27507)  in
                FStar_Syntax_Syntax.Tm_app uu____27490  in
              FStar_Syntax_Syntax.mk uu____27489 f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27555  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27555) uu____27488
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27487;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2144_27486.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2144_27486.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2144_27486.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2144_27486.FStar_TypeChecker_Common.implicits)
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
          let uu___2151_27573 = g  in
          let uu____27574 =
            let uu____27575 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27575  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27574;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2151_27573.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27573.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27573.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27573.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2156_27592 = g  in
          let uu____27593 =
            let uu____27594 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27594  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27593;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2156_27592.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27592.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27592.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27592.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2160_27596 = g  in
          let uu____27597 =
            let uu____27598 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27598  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27597;
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___2160_27596.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___2160_27596.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2160_27596.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2160_27596.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27605 ->
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
                       let uu____27682 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27682
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2183_27689 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2183_27689.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2183_27689.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2183_27689.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2183_27689.FStar_TypeChecker_Common.implicits)
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
               let uu____27723 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27723
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
            let uu___2198_27750 = g  in
            let uu____27751 =
              let uu____27752 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27752  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27751;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___2198_27750.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___2198_27750.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2198_27750.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2198_27750.FStar_TypeChecker_Common.implicits)
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
              let uu____27802 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27802 with
              | FStar_Pervasives_Native.Some
                  (uu____27827::(tm,uu____27829)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27893 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27911 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27911;
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
                    (let uu____27945 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27945
                     then
                       let uu____27949 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27949
                     else ());
                    (let g =
                       let uu___2222_27955 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2222_27955.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___2222_27955.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2222_27955.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2222_27955.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____28009 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28067  ->
                      fun b  ->
                        match uu____28067 with
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
                                  let uu____28119 =
                                    let uu____28120 =
                                      let uu____28127 = FStar_Dyn.mkdyn env1
                                         in
                                      (uu____28127, t)  in
                                    FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                      uu____28120
                                     in
                                  FStar_Pervasives_Native.Some uu____28119
                              | FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Meta
                                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                  t)) ->
                                  FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr t)
                              | uu____28133 -> FStar_Pervasives_Native.None
                               in
                            let uu____28136 =
                              let uu____28149 = reason b  in
                              new_implicit_var_aux uu____28149 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                ctx_uvar_meta_t
                               in
                            (match uu____28136 with
                             | (t,uu____28162,g_t) ->
                                 let uu____28176 =
                                   let uu____28179 =
                                     let uu____28182 =
                                       let uu____28183 =
                                         let uu____28190 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28190, t)  in
                                       FStar_Syntax_Syntax.NT uu____28183  in
                                     [uu____28182]  in
                                   FStar_List.append substs1 uu____28179  in
                                 let uu____28201 = conj_guard g g_t  in
                                 (uu____28176, (FStar_List.append uvars [t]),
                                   uu____28201))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____28009
              (fun uu____28230  ->
                 match uu____28230 with | (uu____28247,uvars,g) -> (uvars, g))
  
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
                let uu____28288 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28288 FStar_Util.must  in
              let uu____28305 = inst_tscheme_with post_ts [u]  in
              match uu____28305 with
              | (uu____28310,post) ->
                  let uu____28312 =
                    let uu____28313 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                    [uu____28313]  in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____28312 r
               in
            let uu____28346 =
              let uu____28347 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg
                 in
              [uu____28347]  in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____28346 r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28383  -> ());
    push = (fun uu____28385  -> ());
    pop = (fun uu____28388  -> ());
    snapshot =
      (fun uu____28391  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28410  -> fun uu____28411  -> ());
    encode_sig = (fun uu____28426  -> fun uu____28427  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28433 =
             let uu____28440 = FStar_Options.peek ()  in (e, g, uu____28440)
              in
           [uu____28433]);
    solve = (fun uu____28456  -> fun uu____28457  -> fun uu____28458  -> ());
    finish = (fun uu____28465  -> ());
    refresh = (fun uu____28467  -> ())
  } 