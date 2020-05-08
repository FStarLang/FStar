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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> solver
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> range
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> curmodule
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> gamma
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> modules
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> expected_typ
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> sigtab
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> attrtab
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> effects1
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> generalize
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> letrecs
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> top_level
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> check_uvars
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> use_eq
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> use_eq_strict
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> is_iface
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> admit
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> lax
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> lax_universes
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> phase1
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> failhard
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> nosynth
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> tc_term
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> type_of
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> universe_of
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> check_type_of
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> use_bv_sorts
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} ->
        qtbl_name_and_index
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} ->
        normalized_eff_names
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> proof_ns
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> synth_hook
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} ->
        try_solve_implicits_hook
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> splice
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> mpreprocess
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> postprocess
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> identifier_info
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> dsenv
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> nbe
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
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
        dsenv; nbe; strict_args_tab; erasable_types_tab;_} ->
        erasable_types_tab
  
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
           (fun uu___0_14189  ->
              match uu___0_14189 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14192 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____14192  in
                  let uu____14193 =
                    let uu____14194 = FStar_Syntax_Subst.compress y  in
                    uu____14194.FStar_Syntax_Syntax.n  in
                  (match uu____14193 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14198 =
                         let uu___327_14199 = y1  in
                         let uu____14200 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14199.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14199.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14200
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14198
                   | uu____14203 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst  ->
    fun env1  ->
      let uu___333_14217 = env1  in
      let uu____14218 = rename_gamma subst env1.gamma  in
      {
        solver = (uu___333_14217.solver);
        range = (uu___333_14217.range);
        curmodule = (uu___333_14217.curmodule);
        gamma = uu____14218;
        gamma_sig = (uu___333_14217.gamma_sig);
        gamma_cache = (uu___333_14217.gamma_cache);
        modules = (uu___333_14217.modules);
        expected_typ = (uu___333_14217.expected_typ);
        sigtab = (uu___333_14217.sigtab);
        attrtab = (uu___333_14217.attrtab);
        instantiate_imp = (uu___333_14217.instantiate_imp);
        effects = (uu___333_14217.effects);
        generalize = (uu___333_14217.generalize);
        letrecs = (uu___333_14217.letrecs);
        top_level = (uu___333_14217.top_level);
        check_uvars = (uu___333_14217.check_uvars);
        use_eq = (uu___333_14217.use_eq);
        use_eq_strict = (uu___333_14217.use_eq_strict);
        is_iface = (uu___333_14217.is_iface);
        admit = (uu___333_14217.admit);
        lax = (uu___333_14217.lax);
        lax_universes = (uu___333_14217.lax_universes);
        phase1 = (uu___333_14217.phase1);
        failhard = (uu___333_14217.failhard);
        nosynth = (uu___333_14217.nosynth);
        uvar_subtyping = (uu___333_14217.uvar_subtyping);
        tc_term = (uu___333_14217.tc_term);
        type_of = (uu___333_14217.type_of);
        universe_of = (uu___333_14217.universe_of);
        check_type_of = (uu___333_14217.check_type_of);
        use_bv_sorts = (uu___333_14217.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14217.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14217.normalized_eff_names);
        fv_delta_depths = (uu___333_14217.fv_delta_depths);
        proof_ns = (uu___333_14217.proof_ns);
        synth_hook = (uu___333_14217.synth_hook);
        try_solve_implicits_hook = (uu___333_14217.try_solve_implicits_hook);
        splice = (uu___333_14217.splice);
        mpreprocess = (uu___333_14217.mpreprocess);
        postprocess = (uu___333_14217.postprocess);
        identifier_info = (uu___333_14217.identifier_info);
        tc_hooks = (uu___333_14217.tc_hooks);
        dsenv = (uu___333_14217.dsenv);
        nbe = (uu___333_14217.nbe);
        strict_args_tab = (uu___333_14217.strict_args_tab);
        erasable_types_tab = (uu___333_14217.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14226  -> fun uu____14227  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___340_14249 = env1  in
      {
        solver = (uu___340_14249.solver);
        range = (uu___340_14249.range);
        curmodule = (uu___340_14249.curmodule);
        gamma = (uu___340_14249.gamma);
        gamma_sig = (uu___340_14249.gamma_sig);
        gamma_cache = (uu___340_14249.gamma_cache);
        modules = (uu___340_14249.modules);
        expected_typ = (uu___340_14249.expected_typ);
        sigtab = (uu___340_14249.sigtab);
        attrtab = (uu___340_14249.attrtab);
        instantiate_imp = (uu___340_14249.instantiate_imp);
        effects = (uu___340_14249.effects);
        generalize = (uu___340_14249.generalize);
        letrecs = (uu___340_14249.letrecs);
        top_level = (uu___340_14249.top_level);
        check_uvars = (uu___340_14249.check_uvars);
        use_eq = (uu___340_14249.use_eq);
        use_eq_strict = (uu___340_14249.use_eq_strict);
        is_iface = (uu___340_14249.is_iface);
        admit = (uu___340_14249.admit);
        lax = (uu___340_14249.lax);
        lax_universes = (uu___340_14249.lax_universes);
        phase1 = (uu___340_14249.phase1);
        failhard = (uu___340_14249.failhard);
        nosynth = (uu___340_14249.nosynth);
        uvar_subtyping = (uu___340_14249.uvar_subtyping);
        tc_term = (uu___340_14249.tc_term);
        type_of = (uu___340_14249.type_of);
        universe_of = (uu___340_14249.universe_of);
        check_type_of = (uu___340_14249.check_type_of);
        use_bv_sorts = (uu___340_14249.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14249.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14249.normalized_eff_names);
        fv_delta_depths = (uu___340_14249.fv_delta_depths);
        proof_ns = (uu___340_14249.proof_ns);
        synth_hook = (uu___340_14249.synth_hook);
        try_solve_implicits_hook = (uu___340_14249.try_solve_implicits_hook);
        splice = (uu___340_14249.splice);
        mpreprocess = (uu___340_14249.mpreprocess);
        postprocess = (uu___340_14249.postprocess);
        identifier_info = (uu___340_14249.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14249.dsenv);
        nbe = (uu___340_14249.nbe);
        strict_args_tab = (uu___340_14249.strict_args_tab);
        erasable_types_tab = (uu___340_14249.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___344_14261 = e  in
      let uu____14262 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___344_14261.solver);
        range = (uu___344_14261.range);
        curmodule = (uu___344_14261.curmodule);
        gamma = (uu___344_14261.gamma);
        gamma_sig = (uu___344_14261.gamma_sig);
        gamma_cache = (uu___344_14261.gamma_cache);
        modules = (uu___344_14261.modules);
        expected_typ = (uu___344_14261.expected_typ);
        sigtab = (uu___344_14261.sigtab);
        attrtab = (uu___344_14261.attrtab);
        instantiate_imp = (uu___344_14261.instantiate_imp);
        effects = (uu___344_14261.effects);
        generalize = (uu___344_14261.generalize);
        letrecs = (uu___344_14261.letrecs);
        top_level = (uu___344_14261.top_level);
        check_uvars = (uu___344_14261.check_uvars);
        use_eq = (uu___344_14261.use_eq);
        use_eq_strict = (uu___344_14261.use_eq_strict);
        is_iface = (uu___344_14261.is_iface);
        admit = (uu___344_14261.admit);
        lax = (uu___344_14261.lax);
        lax_universes = (uu___344_14261.lax_universes);
        phase1 = (uu___344_14261.phase1);
        failhard = (uu___344_14261.failhard);
        nosynth = (uu___344_14261.nosynth);
        uvar_subtyping = (uu___344_14261.uvar_subtyping);
        tc_term = (uu___344_14261.tc_term);
        type_of = (uu___344_14261.type_of);
        universe_of = (uu___344_14261.universe_of);
        check_type_of = (uu___344_14261.check_type_of);
        use_bv_sorts = (uu___344_14261.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14261.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14261.normalized_eff_names);
        fv_delta_depths = (uu___344_14261.fv_delta_depths);
        proof_ns = (uu___344_14261.proof_ns);
        synth_hook = (uu___344_14261.synth_hook);
        try_solve_implicits_hook = (uu___344_14261.try_solve_implicits_hook);
        splice = (uu___344_14261.splice);
        mpreprocess = (uu___344_14261.mpreprocess);
        postprocess = (uu___344_14261.postprocess);
        identifier_info = (uu___344_14261.identifier_info);
        tc_hooks = (uu___344_14261.tc_hooks);
        dsenv = uu____14262;
        nbe = (uu___344_14261.nbe);
        strict_args_tab = (uu___344_14261.strict_args_tab);
        erasable_types_tab = (uu___344_14261.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14279 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____14279)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14294) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14297,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14299,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14302 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14316 . unit -> 'uuuuuu14316 FStar_Util.smap =
  fun uu____14323  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14329 . unit -> 'uuuuuu14329 FStar_Util.smap =
  fun uu____14336  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14474 = new_gamma_cache ()  in
                  let uu____14477 = new_sigtab ()  in
                  let uu____14480 = new_sigtab ()  in
                  let uu____14487 =
                    let uu____14502 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14502, FStar_Pervasives_Native.None)  in
                  let uu____14523 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14527 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14531 = FStar_Options.using_facts_from ()  in
                  let uu____14532 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14535 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14536 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14550 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14474;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14477;
                    attrtab = uu____14480;
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
                    qtbl_name_and_index = uu____14487;
                    normalized_eff_names = uu____14523;
                    fv_delta_depths = uu____14527;
                    proof_ns = uu____14531;
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
                    identifier_info = uu____14532;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14535;
                    nbe;
                    strict_args_tab = uu____14536;
                    erasable_types_tab = uu____14550
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
  fun uu____14749  ->
    let uu____14750 = FStar_ST.op_Bang query_indices  in
    match uu____14750 with
    | [] -> failwith "Empty query indices!"
    | uu____14805 ->
        let uu____14815 =
          let uu____14825 =
            let uu____14833 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14833  in
          let uu____14887 = FStar_ST.op_Bang query_indices  in uu____14825 ::
            uu____14887
           in
        FStar_ST.op_Colon_Equals query_indices uu____14815
  
let (pop_query_indices : unit -> unit) =
  fun uu____14983  ->
    let uu____14984 = FStar_ST.op_Bang query_indices  in
    match uu____14984 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15111  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15148  ->
    match uu____15148 with
    | (l,n) ->
        let uu____15158 = FStar_ST.op_Bang query_indices  in
        (match uu____15158 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15280 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15303  ->
    let uu____15304 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15304
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15372 =
       let uu____15375 = FStar_ST.op_Bang stack  in env1 :: uu____15375  in
     FStar_ST.op_Colon_Equals stack uu____15372);
    (let uu___418_15424 = env1  in
     let uu____15425 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15428 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15431 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15438 =
       let uu____15453 =
         let uu____15457 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15457  in
       let uu____15489 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15453, uu____15489)  in
     let uu____15538 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15541 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15544 =
       let uu____15547 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15547  in
     let uu____15567 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15580 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___418_15424.solver);
       range = (uu___418_15424.range);
       curmodule = (uu___418_15424.curmodule);
       gamma = (uu___418_15424.gamma);
       gamma_sig = (uu___418_15424.gamma_sig);
       gamma_cache = uu____15425;
       modules = (uu___418_15424.modules);
       expected_typ = (uu___418_15424.expected_typ);
       sigtab = uu____15428;
       attrtab = uu____15431;
       instantiate_imp = (uu___418_15424.instantiate_imp);
       effects = (uu___418_15424.effects);
       generalize = (uu___418_15424.generalize);
       letrecs = (uu___418_15424.letrecs);
       top_level = (uu___418_15424.top_level);
       check_uvars = (uu___418_15424.check_uvars);
       use_eq = (uu___418_15424.use_eq);
       use_eq_strict = (uu___418_15424.use_eq_strict);
       is_iface = (uu___418_15424.is_iface);
       admit = (uu___418_15424.admit);
       lax = (uu___418_15424.lax);
       lax_universes = (uu___418_15424.lax_universes);
       phase1 = (uu___418_15424.phase1);
       failhard = (uu___418_15424.failhard);
       nosynth = (uu___418_15424.nosynth);
       uvar_subtyping = (uu___418_15424.uvar_subtyping);
       tc_term = (uu___418_15424.tc_term);
       type_of = (uu___418_15424.type_of);
       universe_of = (uu___418_15424.universe_of);
       check_type_of = (uu___418_15424.check_type_of);
       use_bv_sorts = (uu___418_15424.use_bv_sorts);
       qtbl_name_and_index = uu____15438;
       normalized_eff_names = uu____15538;
       fv_delta_depths = uu____15541;
       proof_ns = (uu___418_15424.proof_ns);
       synth_hook = (uu___418_15424.synth_hook);
       try_solve_implicits_hook = (uu___418_15424.try_solve_implicits_hook);
       splice = (uu___418_15424.splice);
       mpreprocess = (uu___418_15424.mpreprocess);
       postprocess = (uu___418_15424.postprocess);
       identifier_info = uu____15544;
       tc_hooks = (uu___418_15424.tc_hooks);
       dsenv = (uu___418_15424.dsenv);
       nbe = (uu___418_15424.nbe);
       strict_args_tab = uu____15567;
       erasable_types_tab = uu____15580
     })
  
let (pop_stack : unit -> env) =
  fun uu____15590  ->
    let uu____15591 = FStar_ST.op_Bang stack  in
    match uu____15591 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15645 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15735  ->
           let uu____15736 = snapshot_stack env1  in
           match uu____15736 with
           | (stack_depth,env2) ->
               let uu____15770 = snapshot_query_indices ()  in
               (match uu____15770 with
                | (query_indices_depth,()) ->
                    let uu____15803 = (env2.solver).snapshot msg  in
                    (match uu____15803 with
                     | (solver_depth,()) ->
                         let uu____15860 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____15860 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_15927 = env2  in
                                 {
                                   solver = (uu___443_15927.solver);
                                   range = (uu___443_15927.range);
                                   curmodule = (uu___443_15927.curmodule);
                                   gamma = (uu___443_15927.gamma);
                                   gamma_sig = (uu___443_15927.gamma_sig);
                                   gamma_cache = (uu___443_15927.gamma_cache);
                                   modules = (uu___443_15927.modules);
                                   expected_typ =
                                     (uu___443_15927.expected_typ);
                                   sigtab = (uu___443_15927.sigtab);
                                   attrtab = (uu___443_15927.attrtab);
                                   instantiate_imp =
                                     (uu___443_15927.instantiate_imp);
                                   effects = (uu___443_15927.effects);
                                   generalize = (uu___443_15927.generalize);
                                   letrecs = (uu___443_15927.letrecs);
                                   top_level = (uu___443_15927.top_level);
                                   check_uvars = (uu___443_15927.check_uvars);
                                   use_eq = (uu___443_15927.use_eq);
                                   use_eq_strict =
                                     (uu___443_15927.use_eq_strict);
                                   is_iface = (uu___443_15927.is_iface);
                                   admit = (uu___443_15927.admit);
                                   lax = (uu___443_15927.lax);
                                   lax_universes =
                                     (uu___443_15927.lax_universes);
                                   phase1 = (uu___443_15927.phase1);
                                   failhard = (uu___443_15927.failhard);
                                   nosynth = (uu___443_15927.nosynth);
                                   uvar_subtyping =
                                     (uu___443_15927.uvar_subtyping);
                                   tc_term = (uu___443_15927.tc_term);
                                   type_of = (uu___443_15927.type_of);
                                   universe_of = (uu___443_15927.universe_of);
                                   check_type_of =
                                     (uu___443_15927.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_15927.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_15927.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_15927.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_15927.fv_delta_depths);
                                   proof_ns = (uu___443_15927.proof_ns);
                                   synth_hook = (uu___443_15927.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_15927.try_solve_implicits_hook);
                                   splice = (uu___443_15927.splice);
                                   mpreprocess = (uu___443_15927.mpreprocess);
                                   postprocess = (uu___443_15927.postprocess);
                                   identifier_info =
                                     (uu___443_15927.identifier_info);
                                   tc_hooks = (uu___443_15927.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_15927.nbe);
                                   strict_args_tab =
                                     (uu___443_15927.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_15927.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15961  ->
             let uu____15962 =
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
             match uu____15962 with
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
                             ((let uu____16142 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16142
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____16158 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____16158
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____16190,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____16232 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16262  ->
                  match uu____16262 with
                  | (m,uu____16270) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16232 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16284 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16284 next);
              (let uu___488_16287 = env1  in
               {
                 solver = (uu___488_16287.solver);
                 range = (uu___488_16287.range);
                 curmodule = (uu___488_16287.curmodule);
                 gamma = (uu___488_16287.gamma);
                 gamma_sig = (uu___488_16287.gamma_sig);
                 gamma_cache = (uu___488_16287.gamma_cache);
                 modules = (uu___488_16287.modules);
                 expected_typ = (uu___488_16287.expected_typ);
                 sigtab = (uu___488_16287.sigtab);
                 attrtab = (uu___488_16287.attrtab);
                 instantiate_imp = (uu___488_16287.instantiate_imp);
                 effects = (uu___488_16287.effects);
                 generalize = (uu___488_16287.generalize);
                 letrecs = (uu___488_16287.letrecs);
                 top_level = (uu___488_16287.top_level);
                 check_uvars = (uu___488_16287.check_uvars);
                 use_eq = (uu___488_16287.use_eq);
                 use_eq_strict = (uu___488_16287.use_eq_strict);
                 is_iface = (uu___488_16287.is_iface);
                 admit = (uu___488_16287.admit);
                 lax = (uu___488_16287.lax);
                 lax_universes = (uu___488_16287.lax_universes);
                 phase1 = (uu___488_16287.phase1);
                 failhard = (uu___488_16287.failhard);
                 nosynth = (uu___488_16287.nosynth);
                 uvar_subtyping = (uu___488_16287.uvar_subtyping);
                 tc_term = (uu___488_16287.tc_term);
                 type_of = (uu___488_16287.type_of);
                 universe_of = (uu___488_16287.universe_of);
                 check_type_of = (uu___488_16287.check_type_of);
                 use_bv_sorts = (uu___488_16287.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16287.normalized_eff_names);
                 fv_delta_depths = (uu___488_16287.fv_delta_depths);
                 proof_ns = (uu___488_16287.proof_ns);
                 synth_hook = (uu___488_16287.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16287.try_solve_implicits_hook);
                 splice = (uu___488_16287.splice);
                 mpreprocess = (uu___488_16287.mpreprocess);
                 postprocess = (uu___488_16287.postprocess);
                 identifier_info = (uu___488_16287.identifier_info);
                 tc_hooks = (uu___488_16287.tc_hooks);
                 dsenv = (uu___488_16287.dsenv);
                 nbe = (uu___488_16287.nbe);
                 strict_args_tab = (uu___488_16287.strict_args_tab);
                 erasable_types_tab = (uu___488_16287.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16304,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16319 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16319 next);
              (let uu___497_16322 = env1  in
               {
                 solver = (uu___497_16322.solver);
                 range = (uu___497_16322.range);
                 curmodule = (uu___497_16322.curmodule);
                 gamma = (uu___497_16322.gamma);
                 gamma_sig = (uu___497_16322.gamma_sig);
                 gamma_cache = (uu___497_16322.gamma_cache);
                 modules = (uu___497_16322.modules);
                 expected_typ = (uu___497_16322.expected_typ);
                 sigtab = (uu___497_16322.sigtab);
                 attrtab = (uu___497_16322.attrtab);
                 instantiate_imp = (uu___497_16322.instantiate_imp);
                 effects = (uu___497_16322.effects);
                 generalize = (uu___497_16322.generalize);
                 letrecs = (uu___497_16322.letrecs);
                 top_level = (uu___497_16322.top_level);
                 check_uvars = (uu___497_16322.check_uvars);
                 use_eq = (uu___497_16322.use_eq);
                 use_eq_strict = (uu___497_16322.use_eq_strict);
                 is_iface = (uu___497_16322.is_iface);
                 admit = (uu___497_16322.admit);
                 lax = (uu___497_16322.lax);
                 lax_universes = (uu___497_16322.lax_universes);
                 phase1 = (uu___497_16322.phase1);
                 failhard = (uu___497_16322.failhard);
                 nosynth = (uu___497_16322.nosynth);
                 uvar_subtyping = (uu___497_16322.uvar_subtyping);
                 tc_term = (uu___497_16322.tc_term);
                 type_of = (uu___497_16322.type_of);
                 universe_of = (uu___497_16322.universe_of);
                 check_type_of = (uu___497_16322.check_type_of);
                 use_bv_sorts = (uu___497_16322.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16322.normalized_eff_names);
                 fv_delta_depths = (uu___497_16322.fv_delta_depths);
                 proof_ns = (uu___497_16322.proof_ns);
                 synth_hook = (uu___497_16322.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16322.try_solve_implicits_hook);
                 splice = (uu___497_16322.splice);
                 mpreprocess = (uu___497_16322.mpreprocess);
                 postprocess = (uu___497_16322.postprocess);
                 identifier_info = (uu___497_16322.identifier_info);
                 tc_hooks = (uu___497_16322.tc_hooks);
                 dsenv = (uu___497_16322.dsenv);
                 nbe = (uu___497_16322.nbe);
                 strict_args_tab = (uu___497_16322.strict_args_tab);
                 erasable_types_tab = (uu___497_16322.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16351 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16351 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___504_16367 = e  in
         {
           solver = (uu___504_16367.solver);
           range = r;
           curmodule = (uu___504_16367.curmodule);
           gamma = (uu___504_16367.gamma);
           gamma_sig = (uu___504_16367.gamma_sig);
           gamma_cache = (uu___504_16367.gamma_cache);
           modules = (uu___504_16367.modules);
           expected_typ = (uu___504_16367.expected_typ);
           sigtab = (uu___504_16367.sigtab);
           attrtab = (uu___504_16367.attrtab);
           instantiate_imp = (uu___504_16367.instantiate_imp);
           effects = (uu___504_16367.effects);
           generalize = (uu___504_16367.generalize);
           letrecs = (uu___504_16367.letrecs);
           top_level = (uu___504_16367.top_level);
           check_uvars = (uu___504_16367.check_uvars);
           use_eq = (uu___504_16367.use_eq);
           use_eq_strict = (uu___504_16367.use_eq_strict);
           is_iface = (uu___504_16367.is_iface);
           admit = (uu___504_16367.admit);
           lax = (uu___504_16367.lax);
           lax_universes = (uu___504_16367.lax_universes);
           phase1 = (uu___504_16367.phase1);
           failhard = (uu___504_16367.failhard);
           nosynth = (uu___504_16367.nosynth);
           uvar_subtyping = (uu___504_16367.uvar_subtyping);
           tc_term = (uu___504_16367.tc_term);
           type_of = (uu___504_16367.type_of);
           universe_of = (uu___504_16367.universe_of);
           check_type_of = (uu___504_16367.check_type_of);
           use_bv_sorts = (uu___504_16367.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16367.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16367.normalized_eff_names);
           fv_delta_depths = (uu___504_16367.fv_delta_depths);
           proof_ns = (uu___504_16367.proof_ns);
           synth_hook = (uu___504_16367.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16367.try_solve_implicits_hook);
           splice = (uu___504_16367.splice);
           mpreprocess = (uu___504_16367.mpreprocess);
           postprocess = (uu___504_16367.postprocess);
           identifier_info = (uu___504_16367.identifier_info);
           tc_hooks = (uu___504_16367.tc_hooks);
           dsenv = (uu___504_16367.dsenv);
           nbe = (uu___504_16367.nbe);
           strict_args_tab = (uu___504_16367.strict_args_tab);
           erasable_types_tab = (uu___504_16367.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16387 =
        let uu____16388 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16388 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16387
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16443 =
          let uu____16444 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16444 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16443
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16499 =
          let uu____16500 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16500 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16499
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16555 =
        let uu____16556 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16556 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16555
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___521_16620 = env1  in
      {
        solver = (uu___521_16620.solver);
        range = (uu___521_16620.range);
        curmodule = lid;
        gamma = (uu___521_16620.gamma);
        gamma_sig = (uu___521_16620.gamma_sig);
        gamma_cache = (uu___521_16620.gamma_cache);
        modules = (uu___521_16620.modules);
        expected_typ = (uu___521_16620.expected_typ);
        sigtab = (uu___521_16620.sigtab);
        attrtab = (uu___521_16620.attrtab);
        instantiate_imp = (uu___521_16620.instantiate_imp);
        effects = (uu___521_16620.effects);
        generalize = (uu___521_16620.generalize);
        letrecs = (uu___521_16620.letrecs);
        top_level = (uu___521_16620.top_level);
        check_uvars = (uu___521_16620.check_uvars);
        use_eq = (uu___521_16620.use_eq);
        use_eq_strict = (uu___521_16620.use_eq_strict);
        is_iface = (uu___521_16620.is_iface);
        admit = (uu___521_16620.admit);
        lax = (uu___521_16620.lax);
        lax_universes = (uu___521_16620.lax_universes);
        phase1 = (uu___521_16620.phase1);
        failhard = (uu___521_16620.failhard);
        nosynth = (uu___521_16620.nosynth);
        uvar_subtyping = (uu___521_16620.uvar_subtyping);
        tc_term = (uu___521_16620.tc_term);
        type_of = (uu___521_16620.type_of);
        universe_of = (uu___521_16620.universe_of);
        check_type_of = (uu___521_16620.check_type_of);
        use_bv_sorts = (uu___521_16620.use_bv_sorts);
        qtbl_name_and_index = (uu___521_16620.qtbl_name_and_index);
        normalized_eff_names = (uu___521_16620.normalized_eff_names);
        fv_delta_depths = (uu___521_16620.fv_delta_depths);
        proof_ns = (uu___521_16620.proof_ns);
        synth_hook = (uu___521_16620.synth_hook);
        try_solve_implicits_hook = (uu___521_16620.try_solve_implicits_hook);
        splice = (uu___521_16620.splice);
        mpreprocess = (uu___521_16620.mpreprocess);
        postprocess = (uu___521_16620.postprocess);
        identifier_info = (uu___521_16620.identifier_info);
        tc_hooks = (uu___521_16620.tc_hooks);
        dsenv = (uu___521_16620.dsenv);
        nbe = (uu___521_16620.nbe);
        strict_args_tab = (uu___521_16620.strict_args_tab);
        erasable_types_tab = (uu___521_16620.erasable_types_tab)
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
      let uu____16651 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16651
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16664 =
      let uu____16666 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____16666  in
    (FStar_Errors.Fatal_NameNotFound, uu____16664)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16681 =
      let uu____16683 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16683  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16681)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16692  ->
    let uu____16693 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
    FStar_Syntax_Syntax.U_unif uu____16693
  
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
      | ((formals,t),uu____16795) ->
          let vs = mk_univ_subst formals us  in
          let uu____16819 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16819)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16836  ->
    match uu___1_16836 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16862  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16882 = inst_tscheme t  in
      match uu____16882 with
      | (us,t1) ->
          let uu____16893 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16893)
  
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
          let uu____16918 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16920 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16918 uu____16920
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
        fun uu____16947  ->
          match uu____16947 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16961 =
                    let uu____16963 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16967 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16971 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16973 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16963 uu____16967 uu____16971 uu____16973
                     in
                  failwith uu____16961)
               else ();
               (let uu____16978 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16978))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16996 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17007 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17018 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____17032 =
        let uu____17034 = FStar_Ident.nsstr l  in
        let uu____17036 = FStar_Ident.string_of_lid cur  in
        uu____17034 = uu____17036  in
      if uu____17032
      then Yes
      else
        (let uu____17042 =
           let uu____17044 = FStar_Ident.nsstr l  in
           let uu____17046 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____17044 uu____17046  in
         if uu____17042
         then
           let lns =
             let uu____17052 = FStar_Ident.ns_of_lid l  in
             let uu____17055 =
               let uu____17058 = FStar_Ident.ident_of_lid l  in [uu____17058]
                in
             FStar_List.append uu____17052 uu____17055  in
           let cur1 =
             let uu____17062 = FStar_Ident.ns_of_lid cur  in
             let uu____17065 =
               let uu____17068 = FStar_Ident.ident_of_lid cur  in
               [uu____17068]  in
             FStar_List.append uu____17062 uu____17065  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____17092) -> Maybe
             | (uu____17099,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____17118 = FStar_Ident.string_of_id hd  in
                 let uu____17120 = FStar_Ident.string_of_id hd'  in
                 uu____17118 = uu____17120 -> aux tl tl'
             | uu____17123 -> No  in
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
        (let uu____17175 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17175 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17219 =
            let uu____17222 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17222  in
          match uu____17219 with
          | FStar_Pervasives_Native.None  ->
              let uu____17244 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17288  ->
                     match uu___2_17288 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17327 = FStar_Ident.lid_equals lid l  in
                         if uu____17327
                         then
                           let uu____17350 =
                             let uu____17369 =
                               let uu____17384 = inst_tscheme t  in
                               FStar_Util.Inl uu____17384  in
                             let uu____17399 = FStar_Ident.range_of_lid l  in
                             (uu____17369, uu____17399)  in
                           FStar_Pervasives_Native.Some uu____17350
                         else FStar_Pervasives_Native.None
                     | uu____17452 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17244
                (fun uu____17490  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17500  ->
                        match uu___3_17500 with
                        | (uu____17503,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17505);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17506;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17507;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17508;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17509;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17510;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17532 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17532
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
                                  uu____17584 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17591 -> cache t  in
                            let uu____17592 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17592 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17598 =
                                   let uu____17599 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17599)
                                    in
                                 maybe_cache uu____17598)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17670 = find_in_sigtab env1 lid  in
         match uu____17670 with
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
      let uu____17751 = lookup_qname env1 lid  in
      match uu____17751 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17772,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17886 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17886 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17931 =
          let uu____17934 = lookup_attr env2 attr  in se1 :: uu____17934  in
        FStar_Util.smap_add (attrtab env2) attr uu____17931  in
      FStar_List.iter
        (fun attr  ->
           let uu____17944 =
             let uu____17945 = FStar_Syntax_Subst.compress attr  in
             uu____17945.FStar_Syntax_Syntax.n  in
           match uu____17944 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17949 =
                 let uu____17951 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17951  in
               add_one env1 se uu____17949
           | uu____17952 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17975) ->
          add_sigelts env1 ses
      | uu____17984 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17992 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17992 se) lids;
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
        (fun uu___4_18026  ->
           match uu___4_18026 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____18036 =
                 let uu____18043 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____18043)  in
               FStar_Pervasives_Native.Some uu____18036
           | uu____18052 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18114,lb::[]),uu____18116) ->
            let uu____18125 =
              let uu____18134 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18143 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18134, uu____18143)  in
            FStar_Pervasives_Native.Some uu____18125
        | FStar_Syntax_Syntax.Sig_let ((uu____18156,lbs),uu____18158) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18190 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18203 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18203
                     then
                       let uu____18216 =
                         let uu____18225 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18234 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18225, uu____18234)  in
                       FStar_Pervasives_Native.Some uu____18216
                     else FStar_Pervasives_Native.None)
        | uu____18257 -> FStar_Pervasives_Native.None
  
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
                    let uu____18349 =
                      let uu____18351 =
                        let uu____18353 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18355 =
                          let uu____18357 =
                            let uu____18359 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18365 =
                              let uu____18367 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18367  in
                            Prims.op_Hat uu____18359 uu____18365  in
                          Prims.op_Hat ", expected " uu____18357  in
                        Prims.op_Hat uu____18353 uu____18355  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18351
                       in
                    failwith uu____18349
                  else ());
             (let uu____18374 =
                let uu____18383 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18383, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18374))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18403,uu____18404) ->
            let uu____18409 =
              let uu____18418 =
                let uu____18423 =
                  let uu____18424 =
                    let uu____18427 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18427  in
                  (us, uu____18424)  in
                inst_ts us_opt uu____18423  in
              (uu____18418, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18409
        | uu____18446 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18535 =
          match uu____18535 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18631,uvs,t,uu____18634,uu____18635,uu____18636);
                      FStar_Syntax_Syntax.sigrng = uu____18637;
                      FStar_Syntax_Syntax.sigquals = uu____18638;
                      FStar_Syntax_Syntax.sigmeta = uu____18639;
                      FStar_Syntax_Syntax.sigattrs = uu____18640;
                      FStar_Syntax_Syntax.sigopts = uu____18641;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18666 =
                     let uu____18675 = inst_tscheme1 (uvs, t)  in
                     (uu____18675, rng)  in
                   FStar_Pervasives_Native.Some uu____18666
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18699;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18701;
                      FStar_Syntax_Syntax.sigattrs = uu____18702;
                      FStar_Syntax_Syntax.sigopts = uu____18703;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18722 =
                     let uu____18724 = in_cur_mod env1 l  in
                     uu____18724 = Yes  in
                   if uu____18722
                   then
                     let uu____18736 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18736
                      then
                        let uu____18752 =
                          let uu____18761 = inst_tscheme1 (uvs, t)  in
                          (uu____18761, rng)  in
                        FStar_Pervasives_Native.Some uu____18752
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18794 =
                        let uu____18803 = inst_tscheme1 (uvs, t)  in
                        (uu____18803, rng)  in
                      FStar_Pervasives_Native.Some uu____18794)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18828,uu____18829);
                      FStar_Syntax_Syntax.sigrng = uu____18830;
                      FStar_Syntax_Syntax.sigquals = uu____18831;
                      FStar_Syntax_Syntax.sigmeta = uu____18832;
                      FStar_Syntax_Syntax.sigattrs = uu____18833;
                      FStar_Syntax_Syntax.sigopts = uu____18834;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18877 =
                          let uu____18886 = inst_tscheme1 (uvs, k)  in
                          (uu____18886, rng)  in
                        FStar_Pervasives_Native.Some uu____18877
                    | uu____18907 ->
                        let uu____18908 =
                          let uu____18917 =
                            let uu____18922 =
                              let uu____18923 =
                                let uu____18926 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18926
                                 in
                              (uvs, uu____18923)  in
                            inst_tscheme1 uu____18922  in
                          (uu____18917, rng)  in
                        FStar_Pervasives_Native.Some uu____18908)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18949,uu____18950);
                      FStar_Syntax_Syntax.sigrng = uu____18951;
                      FStar_Syntax_Syntax.sigquals = uu____18952;
                      FStar_Syntax_Syntax.sigmeta = uu____18953;
                      FStar_Syntax_Syntax.sigattrs = uu____18954;
                      FStar_Syntax_Syntax.sigopts = uu____18955;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18999 =
                          let uu____19008 = inst_tscheme_with (uvs, k) us  in
                          (uu____19008, rng)  in
                        FStar_Pervasives_Native.Some uu____18999
                    | uu____19029 ->
                        let uu____19030 =
                          let uu____19039 =
                            let uu____19044 =
                              let uu____19045 =
                                let uu____19048 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19048
                                 in
                              (uvs, uu____19045)  in
                            inst_tscheme_with uu____19044 us  in
                          (uu____19039, rng)  in
                        FStar_Pervasives_Native.Some uu____19030)
               | FStar_Util.Inr se ->
                   let uu____19084 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19105;
                          FStar_Syntax_Syntax.sigrng = uu____19106;
                          FStar_Syntax_Syntax.sigquals = uu____19107;
                          FStar_Syntax_Syntax.sigmeta = uu____19108;
                          FStar_Syntax_Syntax.sigattrs = uu____19109;
                          FStar_Syntax_Syntax.sigopts = uu____19110;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19127 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____19084
                     (FStar_Util.map_option
                        (fun uu____19175  ->
                           match uu____19175 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19206 =
          let uu____19217 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19217 mapper  in
        match uu____19206 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19291 =
              let uu____19302 =
                let uu____19309 =
                  let uu___858_19312 = t  in
                  let uu____19313 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19312.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19313;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19312.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19309)  in
              (uu____19302, r)  in
            FStar_Pervasives_Native.Some uu____19291
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19362 = lookup_qname env1 l  in
      match uu____19362 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19383 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19437 = try_lookup_bv env1 bv  in
      match uu____19437 with
      | FStar_Pervasives_Native.None  ->
          let uu____19452 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19452 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19468 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19469 =
            let uu____19470 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19470  in
          (uu____19468, uu____19469)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19492 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19492 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19558 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19558  in
          let uu____19559 =
            let uu____19568 =
              let uu____19573 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19573)  in
            (uu____19568, r1)  in
          FStar_Pervasives_Native.Some uu____19559
  
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
        let uu____19608 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19608 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19641,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19666 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19666  in
            let uu____19667 =
              let uu____19672 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19672, r1)  in
            FStar_Pervasives_Native.Some uu____19667
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19696 = try_lookup_lid env1 l  in
      match uu____19696 with
      | FStar_Pervasives_Native.None  ->
          let uu____19723 = name_not_found l  in
          let uu____19729 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19723 uu____19729
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19774  ->
              match uu___5_19774 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19777 = FStar_Ident.string_of_id x  in
                  let uu____19779 = FStar_Ident.string_of_id y  in
                  uu____19777 = uu____19779
              | uu____19782 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19803 = lookup_qname env1 lid  in
      match uu____19803 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19812,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19815;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19817;
              FStar_Syntax_Syntax.sigattrs = uu____19818;
              FStar_Syntax_Syntax.sigopts = uu____19819;_},FStar_Pervasives_Native.None
            ),uu____19820)
          ->
          let uu____19871 =
            let uu____19878 =
              let uu____19879 =
                let uu____19882 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19882 t  in
              (uvs, uu____19879)  in
            (uu____19878, q)  in
          FStar_Pervasives_Native.Some uu____19871
      | uu____19895 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19917 = lookup_qname env1 lid  in
      match uu____19917 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19922,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19925;
              FStar_Syntax_Syntax.sigquals = uu____19926;
              FStar_Syntax_Syntax.sigmeta = uu____19927;
              FStar_Syntax_Syntax.sigattrs = uu____19928;
              FStar_Syntax_Syntax.sigopts = uu____19929;_},FStar_Pervasives_Native.None
            ),uu____19930)
          ->
          let uu____19981 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19981 (uvs, t)
      | uu____19986 ->
          let uu____19987 = name_not_found lid  in
          let uu____19993 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19987 uu____19993
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____20013 = lookup_qname env1 lid  in
      match uu____20013 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20018,uvs,t,uu____20021,uu____20022,uu____20023);
              FStar_Syntax_Syntax.sigrng = uu____20024;
              FStar_Syntax_Syntax.sigquals = uu____20025;
              FStar_Syntax_Syntax.sigmeta = uu____20026;
              FStar_Syntax_Syntax.sigattrs = uu____20027;
              FStar_Syntax_Syntax.sigopts = uu____20028;_},FStar_Pervasives_Native.None
            ),uu____20029)
          ->
          let uu____20086 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20086 (uvs, t)
      | uu____20091 ->
          let uu____20092 = name_not_found lid  in
          let uu____20098 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20092 uu____20098
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____20121 = lookup_qname env1 lid  in
      match uu____20121 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20129,uu____20130,uu____20131,uu____20132,uu____20133,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20135;
              FStar_Syntax_Syntax.sigquals = uu____20136;
              FStar_Syntax_Syntax.sigmeta = uu____20137;
              FStar_Syntax_Syntax.sigattrs = uu____20138;
              FStar_Syntax_Syntax.sigopts = uu____20139;_},uu____20140),uu____20141)
          -> (true, dcs)
      | uu____20206 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20222 = lookup_qname env1 lid  in
      match uu____20222 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20223,uu____20224,uu____20225,l,uu____20227,uu____20228);
              FStar_Syntax_Syntax.sigrng = uu____20229;
              FStar_Syntax_Syntax.sigquals = uu____20230;
              FStar_Syntax_Syntax.sigmeta = uu____20231;
              FStar_Syntax_Syntax.sigattrs = uu____20232;
              FStar_Syntax_Syntax.sigopts = uu____20233;_},uu____20234),uu____20235)
          -> l
      | uu____20294 ->
          let uu____20295 =
            let uu____20297 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20297  in
          failwith uu____20295
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20367)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20424) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20448 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20448
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20483 -> FStar_Pervasives_Native.None)
          | uu____20492 -> FStar_Pervasives_Native.None
  
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
        let uu____20554 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20554
  
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
        let uu____20587 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20587
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20611 =
        let uu____20613 = FStar_Ident.nsstr lid  in uu____20613 = "Prims"  in
      if uu____20611
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20643,uu____20644) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20693),uu____20694) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20743 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20761 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20771 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20788 ->
                  let uu____20795 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20795
              | FStar_Syntax_Syntax.Sig_let ((uu____20796,lbs),uu____20798)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20814 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20814
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20821 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20837 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____20847 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20854 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20855 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20856 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20869 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20870 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20893 =
        let uu____20895 = FStar_Ident.nsstr lid  in uu____20895 = "Prims"  in
      if uu____20893
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20902 =
           let uu____20905 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20905
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20902
           (fun d_opt  ->
              let uu____20917 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20917
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20927 =
                   let uu____20930 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20930  in
                 match uu____20927 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20931 =
                       let uu____20933 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20933
                        in
                     failwith uu____20931
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20938 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20938
                       then
                         let uu____20941 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20943 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20945 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20941 uu____20943 uu____20945
                       else ());
                      (let uu____20951 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20951 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20972),uu____20973) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21022 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21044),uu____21045) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21094 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____21116 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21116
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21149 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____21149 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21171 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21180 =
                        let uu____21181 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21181.FStar_Syntax_Syntax.n  in
                      match uu____21180 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21186 -> false))
               in
            (true, uu____21171)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21209 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21209
  
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
          let uu____21281 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21281  in
        let uu____21282 = FStar_Util.smap_try_find tab s  in
        match uu____21282 with
        | FStar_Pervasives_Native.None  ->
            let uu____21285 = f ()  in
            (match uu____21285 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21323 =
        let uu____21324 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21324 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21358 =
        let uu____21359 = FStar_Syntax_Util.unrefine t  in
        uu____21359.FStar_Syntax_Syntax.n  in
      match uu____21358 with
      | FStar_Syntax_Syntax.Tm_type uu____21363 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21367) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21393) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21398,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21420 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21453 =
        let attrs =
          let uu____21459 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21459  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21499 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21499)
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
      let uu____21544 = lookup_qname env1 ftv  in
      match uu____21544 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21548) ->
          let uu____21593 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21593 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21614,t),r) ->
               let uu____21629 =
                 let uu____21630 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21630 t  in
               FStar_Pervasives_Native.Some uu____21629)
      | uu____21631 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21643 = try_lookup_effect_lid env1 ftv  in
      match uu____21643 with
      | FStar_Pervasives_Native.None  ->
          let uu____21646 = name_not_found ftv  in
          let uu____21652 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21646 uu____21652
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
        let uu____21676 = lookup_qname env1 lid0  in
        match uu____21676 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21687);
                FStar_Syntax_Syntax.sigrng = uu____21688;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21690;
                FStar_Syntax_Syntax.sigattrs = uu____21691;
                FStar_Syntax_Syntax.sigopts = uu____21692;_},FStar_Pervasives_Native.None
              ),uu____21693)
            ->
            let lid1 =
              let uu____21749 =
                let uu____21750 = FStar_Ident.range_of_lid lid  in
                let uu____21751 =
                  let uu____21752 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21752  in
                FStar_Range.set_use_range uu____21750 uu____21751  in
              FStar_Ident.set_lid_range lid uu____21749  in
            let uu____21753 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21759  ->
                      match uu___6_21759 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21762 -> false))
               in
            if uu____21753
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21781 =
                      let uu____21783 =
                        let uu____21785 = get_range env1  in
                        FStar_Range.string_of_range uu____21785  in
                      let uu____21786 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21788 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21783 uu____21786 uu____21788
                       in
                    failwith uu____21781)
                  in
               match (binders, univs) with
               | ([],uu____21809) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21835,uu____21836::uu____21837::uu____21838) ->
                   let uu____21859 =
                     let uu____21861 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21863 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21861 uu____21863
                      in
                   failwith uu____21859
               | uu____21874 ->
                   let uu____21889 =
                     let uu____21894 =
                       let uu____21895 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21895)  in
                     inst_tscheme_with uu____21894 insts  in
                   (match uu____21889 with
                    | (uu____21908,t) ->
                        let t1 =
                          let uu____21911 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21911 t  in
                        let uu____21912 =
                          let uu____21913 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21913.FStar_Syntax_Syntax.n  in
                        (match uu____21912 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21948 -> failwith "Impossible")))
        | uu____21956 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21980 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21980 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21993,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22000 = find l2  in
            (match uu____22000 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22007 =
          let uu____22010 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____22010  in
        match uu____22007 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22013 = find l  in
            (match uu____22013 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____22018 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____22018
                     m);
                  m))
         in
      let uu____22020 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22020
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22041 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____22041 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22047) ->
            FStar_List.length bs
        | uu____22086 ->
            let uu____22087 =
              let uu____22093 =
                let uu____22095 = FStar_Ident.string_of_lid name  in
                let uu____22097 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22095 uu____22097
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22093)
               in
            FStar_Errors.raise_error uu____22087 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____22116 = lookup_qname env1 l1  in
      match uu____22116 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22119;
              FStar_Syntax_Syntax.sigrng = uu____22120;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22122;
              FStar_Syntax_Syntax.sigattrs = uu____22123;
              FStar_Syntax_Syntax.sigopts = uu____22124;_},uu____22125),uu____22126)
          -> q
      | uu____22179 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22203 =
          let uu____22204 =
            let uu____22206 = FStar_Util.string_of_int i  in
            let uu____22208 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22206 uu____22208
             in
          failwith uu____22204  in
        let uu____22211 = lookup_datacon env1 lid  in
        match uu____22211 with
        | (uu____22216,t) ->
            let uu____22218 =
              let uu____22219 = FStar_Syntax_Subst.compress t  in
              uu____22219.FStar_Syntax_Syntax.n  in
            (match uu____22218 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22223) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22269 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22283 = lookup_qname env1 l  in
      match uu____22283 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22285,uu____22286,uu____22287);
              FStar_Syntax_Syntax.sigrng = uu____22288;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22290;
              FStar_Syntax_Syntax.sigattrs = uu____22291;
              FStar_Syntax_Syntax.sigopts = uu____22292;_},uu____22293),uu____22294)
          ->
          FStar_Util.for_some
            (fun uu___7_22349  ->
               match uu___7_22349 with
               | FStar_Syntax_Syntax.Projector uu____22351 -> true
               | uu____22357 -> false) quals
      | uu____22359 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22373 = lookup_qname env1 lid  in
      match uu____22373 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22375,uu____22376,uu____22377,uu____22378,uu____22379,uu____22380);
              FStar_Syntax_Syntax.sigrng = uu____22381;
              FStar_Syntax_Syntax.sigquals = uu____22382;
              FStar_Syntax_Syntax.sigmeta = uu____22383;
              FStar_Syntax_Syntax.sigattrs = uu____22384;
              FStar_Syntax_Syntax.sigopts = uu____22385;_},uu____22386),uu____22387)
          -> true
      | uu____22447 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22461 = lookup_qname env1 lid  in
      match uu____22461 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22463,uu____22464,uu____22465,uu____22466,uu____22467,uu____22468);
              FStar_Syntax_Syntax.sigrng = uu____22469;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22471;
              FStar_Syntax_Syntax.sigattrs = uu____22472;
              FStar_Syntax_Syntax.sigopts = uu____22473;_},uu____22474),uu____22475)
          ->
          FStar_Util.for_some
            (fun uu___8_22538  ->
               match uu___8_22538 with
               | FStar_Syntax_Syntax.RecordType uu____22540 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22550 -> true
               | uu____22560 -> false) quals
      | uu____22562 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22572,uu____22573);
            FStar_Syntax_Syntax.sigrng = uu____22574;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22576;
            FStar_Syntax_Syntax.sigattrs = uu____22577;
            FStar_Syntax_Syntax.sigopts = uu____22578;_},uu____22579),uu____22580)
        ->
        FStar_Util.for_some
          (fun uu___9_22639  ->
             match uu___9_22639 with
             | FStar_Syntax_Syntax.Action uu____22641 -> true
             | uu____22643 -> false) quals
    | uu____22645 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22659 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22659
  
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
      let uu____22676 =
        let uu____22677 = FStar_Syntax_Util.un_uinst head  in
        uu____22677.FStar_Syntax_Syntax.n  in
      match uu____22676 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22683 ->
               true
           | uu____22686 -> false)
      | uu____22688 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22702 = lookup_qname env1 l  in
      match uu____22702 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22705),uu____22706) ->
          FStar_Util.for_some
            (fun uu___10_22754  ->
               match uu___10_22754 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22757 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22759 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22835 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22853) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22871 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22879 ->
                 FStar_Pervasives_Native.Some true
             | uu____22898 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22901 =
        let uu____22905 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22905 mapper  in
      match uu____22901 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22965 = lookup_qname env1 lid  in
      match uu____22965 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22969,uu____22970,tps,uu____22972,uu____22973,uu____22974);
              FStar_Syntax_Syntax.sigrng = uu____22975;
              FStar_Syntax_Syntax.sigquals = uu____22976;
              FStar_Syntax_Syntax.sigmeta = uu____22977;
              FStar_Syntax_Syntax.sigattrs = uu____22978;
              FStar_Syntax_Syntax.sigopts = uu____22979;_},uu____22980),uu____22981)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23049 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23095  ->
              match uu____23095 with
              | (d,uu____23104) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____23120 = effect_decl_opt env1 l  in
      match uu____23120 with
      | FStar_Pervasives_Native.None  ->
          let uu____23135 = name_not_found l  in
          let uu____23141 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23135 uu____23141
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23169 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23169 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23176  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23190  ->
            fun uu____23191  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23225 = FStar_Ident.lid_equals l1 l2  in
        if uu____23225
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23244 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23244
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23263 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23316  ->
                        match uu____23316 with
                        | (m1,m2,uu____23330,uu____23331,uu____23332) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23263 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23357,uu____23358,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23406 = join_opt env1 l1 l2  in
        match uu____23406 with
        | FStar_Pervasives_Native.None  ->
            let uu____23427 =
              let uu____23433 =
                let uu____23435 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23437 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23435 uu____23437
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23433)  in
            FStar_Errors.raise_error uu____23427 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23480 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23480
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
  'uuuuuu23500 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23500) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23529 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23555  ->
                match uu____23555 with
                | (d,uu____23562) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23529 with
      | FStar_Pervasives_Native.None  ->
          let uu____23573 =
            let uu____23575 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23575
             in
          failwith uu____23573
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23590 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23590 with
           | (uu____23601,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23619)::(wp,uu____23621)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23677 -> failwith "Impossible"))
  
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
        | uu____23742 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23755 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23755 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23772 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23772 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23797 =
                     let uu____23803 =
                       let uu____23805 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23813 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23824 =
                         let uu____23826 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23826  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23805 uu____23813 uu____23824
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23803)
                      in
                   FStar_Errors.raise_error uu____23797
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23834 =
                     let uu____23845 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23845 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23882  ->
                        fun uu____23883  ->
                          match (uu____23882, uu____23883) with
                          | ((x,uu____23913),(t,uu____23915)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23834
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23946 =
                     let uu___1612_23947 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1612_23947.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1612_23947.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1612_23947.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1612_23947.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23946
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23959 .
    'uuuuuu23959 ->
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
            let uu____24000 =
              let uu____24007 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____24007)  in
            match uu____24000 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24031 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24033 = FStar_Util.string_of_int given  in
                     let uu____24035 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24031 uu____24033 uu____24035
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24040 = effect_decl_opt env1 effect_name  in
          match uu____24040 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24062) ->
              let uu____24073 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24073 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24091 =
                       let uu____24094 =
                         let uu____24095 =
                           let uu____24112 =
                             let uu____24123 =
                               FStar_All.pipe_right res_typ
                                 FStar_Syntax_Syntax.as_arg
                                in
                             uu____24123 ::
                               (c1.FStar_Syntax_Syntax.effect_args)
                              in
                           (repr, uu____24112)  in
                         FStar_Syntax_Syntax.Tm_app uu____24095  in
                       let uu____24160 = get_range env1  in
                       FStar_Syntax_Syntax.mk uu____24094 uu____24160  in
                     FStar_Pervasives_Native.Some uu____24091)))
  
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
           (fun uu___11_24224  ->
              match uu___11_24224 with
              | FStar_Syntax_Syntax.Reflectable uu____24226 -> true
              | uu____24228 -> false))
  
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
      | uu____24288 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24303 =
        let uu____24304 = FStar_Syntax_Subst.compress t  in
        uu____24304.FStar_Syntax_Syntax.n  in
      match uu____24303 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24308,c) ->
          is_reifiable_comp env1 c
      | uu____24330 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24350 =
           let uu____24352 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24352  in
         if uu____24350
         then
           let uu____24355 =
             let uu____24361 =
               let uu____24363 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24363
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24361)  in
           let uu____24367 = get_range env1  in
           FStar_Errors.raise_error uu____24355 uu____24367
         else ());
        (let uu____24370 = effect_repr_aux true env1 c u_c  in
         match uu____24370 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1689_24406 = env1  in
        {
          solver = (uu___1689_24406.solver);
          range = (uu___1689_24406.range);
          curmodule = (uu___1689_24406.curmodule);
          gamma = (uu___1689_24406.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1689_24406.gamma_cache);
          modules = (uu___1689_24406.modules);
          expected_typ = (uu___1689_24406.expected_typ);
          sigtab = (uu___1689_24406.sigtab);
          attrtab = (uu___1689_24406.attrtab);
          instantiate_imp = (uu___1689_24406.instantiate_imp);
          effects = (uu___1689_24406.effects);
          generalize = (uu___1689_24406.generalize);
          letrecs = (uu___1689_24406.letrecs);
          top_level = (uu___1689_24406.top_level);
          check_uvars = (uu___1689_24406.check_uvars);
          use_eq = (uu___1689_24406.use_eq);
          use_eq_strict = (uu___1689_24406.use_eq_strict);
          is_iface = (uu___1689_24406.is_iface);
          admit = (uu___1689_24406.admit);
          lax = (uu___1689_24406.lax);
          lax_universes = (uu___1689_24406.lax_universes);
          phase1 = (uu___1689_24406.phase1);
          failhard = (uu___1689_24406.failhard);
          nosynth = (uu___1689_24406.nosynth);
          uvar_subtyping = (uu___1689_24406.uvar_subtyping);
          tc_term = (uu___1689_24406.tc_term);
          type_of = (uu___1689_24406.type_of);
          universe_of = (uu___1689_24406.universe_of);
          check_type_of = (uu___1689_24406.check_type_of);
          use_bv_sorts = (uu___1689_24406.use_bv_sorts);
          qtbl_name_and_index = (uu___1689_24406.qtbl_name_and_index);
          normalized_eff_names = (uu___1689_24406.normalized_eff_names);
          fv_delta_depths = (uu___1689_24406.fv_delta_depths);
          proof_ns = (uu___1689_24406.proof_ns);
          synth_hook = (uu___1689_24406.synth_hook);
          try_solve_implicits_hook =
            (uu___1689_24406.try_solve_implicits_hook);
          splice = (uu___1689_24406.splice);
          mpreprocess = (uu___1689_24406.mpreprocess);
          postprocess = (uu___1689_24406.postprocess);
          identifier_info = (uu___1689_24406.identifier_info);
          tc_hooks = (uu___1689_24406.tc_hooks);
          dsenv = (uu___1689_24406.dsenv);
          nbe = (uu___1689_24406.nbe);
          strict_args_tab = (uu___1689_24406.strict_args_tab);
          erasable_types_tab = (uu___1689_24406.erasable_types_tab)
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
    fun uu____24425  ->
      match uu____24425 with
      | (ed,quals) ->
          let effects1 =
            let uu___1698_24439 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1698_24439.order);
              joins = (uu___1698_24439.joins);
              polymonadic_binds = (uu___1698_24439.polymonadic_binds);
              polymonadic_subcomps = (uu___1698_24439.polymonadic_subcomps)
            }  in
          let uu___1701_24448 = env1  in
          {
            solver = (uu___1701_24448.solver);
            range = (uu___1701_24448.range);
            curmodule = (uu___1701_24448.curmodule);
            gamma = (uu___1701_24448.gamma);
            gamma_sig = (uu___1701_24448.gamma_sig);
            gamma_cache = (uu___1701_24448.gamma_cache);
            modules = (uu___1701_24448.modules);
            expected_typ = (uu___1701_24448.expected_typ);
            sigtab = (uu___1701_24448.sigtab);
            attrtab = (uu___1701_24448.attrtab);
            instantiate_imp = (uu___1701_24448.instantiate_imp);
            effects = effects1;
            generalize = (uu___1701_24448.generalize);
            letrecs = (uu___1701_24448.letrecs);
            top_level = (uu___1701_24448.top_level);
            check_uvars = (uu___1701_24448.check_uvars);
            use_eq = (uu___1701_24448.use_eq);
            use_eq_strict = (uu___1701_24448.use_eq_strict);
            is_iface = (uu___1701_24448.is_iface);
            admit = (uu___1701_24448.admit);
            lax = (uu___1701_24448.lax);
            lax_universes = (uu___1701_24448.lax_universes);
            phase1 = (uu___1701_24448.phase1);
            failhard = (uu___1701_24448.failhard);
            nosynth = (uu___1701_24448.nosynth);
            uvar_subtyping = (uu___1701_24448.uvar_subtyping);
            tc_term = (uu___1701_24448.tc_term);
            type_of = (uu___1701_24448.type_of);
            universe_of = (uu___1701_24448.universe_of);
            check_type_of = (uu___1701_24448.check_type_of);
            use_bv_sorts = (uu___1701_24448.use_bv_sorts);
            qtbl_name_and_index = (uu___1701_24448.qtbl_name_and_index);
            normalized_eff_names = (uu___1701_24448.normalized_eff_names);
            fv_delta_depths = (uu___1701_24448.fv_delta_depths);
            proof_ns = (uu___1701_24448.proof_ns);
            synth_hook = (uu___1701_24448.synth_hook);
            try_solve_implicits_hook =
              (uu___1701_24448.try_solve_implicits_hook);
            splice = (uu___1701_24448.splice);
            mpreprocess = (uu___1701_24448.mpreprocess);
            postprocess = (uu___1701_24448.postprocess);
            identifier_info = (uu___1701_24448.identifier_info);
            tc_hooks = (uu___1701_24448.tc_hooks);
            dsenv = (uu___1701_24448.dsenv);
            nbe = (uu___1701_24448.nbe);
            strict_args_tab = (uu___1701_24448.strict_args_tab);
            erasable_types_tab = (uu___1701_24448.erasable_types_tab)
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
        let uu____24477 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24545  ->
                  match uu____24545 with
                  | (m1,n1,uu____24563,uu____24564) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24477 with
        | FStar_Pervasives_Native.Some (uu____24589,uu____24590,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24635 -> FStar_Pervasives_Native.None
  
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        let uu____24680 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____24715  ->
                  match uu____24715 with
                  | (m1,n1,uu____24725) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24680 with
        | FStar_Pervasives_Native.Some (uu____24728,uu____24729,ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____24737 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24794 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24794
                  (fun uu____24815  ->
                     match uu____24815 with
                     | (c1,g1) ->
                         let uu____24826 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24826
                           (fun uu____24847  ->
                              match uu____24847 with
                              | (c2,g2) ->
                                  let uu____24858 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24858)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24980 = l1 u t e  in
                              l2 u t uu____24980))
                | uu____24981 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____25049  ->
                    match uu____25049 with
                    | (e,uu____25057) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25080 =
            match uu____25080 with
            | (i,j) ->
                let uu____25091 = FStar_Ident.lid_equals i j  in
                if uu____25091
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____25098  ->
                       FStar_Pervasives_Native.Some uu____25098)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25127 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25137 = FStar_Ident.lid_equals i k  in
                        if uu____25137
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25151 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25151
                                  then []
                                  else
                                    (let uu____25158 =
                                       let uu____25167 =
                                         find_edge order1 (i, k)  in
                                       let uu____25170 =
                                         find_edge order1 (k, j)  in
                                       (uu____25167, uu____25170)  in
                                     match uu____25158 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25185 =
                                           compose_edges e1 e2  in
                                         [uu____25185]
                                     | uu____25186 -> [])))))
                 in
              FStar_List.append order1 uu____25127  in
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
                  let uu____25216 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25219 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____25219
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25216
                  then
                    let uu____25226 =
                      let uu____25232 =
                        let uu____25234 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25234
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25232)
                       in
                    let uu____25238 = get_range env1  in
                    FStar_Errors.raise_error uu____25226 uu____25238
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25316 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25316
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25368 =
                                             let uu____25377 =
                                               find_edge order2 (i, k)  in
                                             let uu____25380 =
                                               find_edge order2 (j, k)  in
                                             (uu____25377, uu____25380)  in
                                           match uu____25368 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25422,uu____25423)
                                                    ->
                                                    let uu____25430 =
                                                      let uu____25437 =
                                                        let uu____25439 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25439
                                                         in
                                                      let uu____25442 =
                                                        let uu____25444 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25444
                                                         in
                                                      (uu____25437,
                                                        uu____25442)
                                                       in
                                                    (match uu____25430 with
                                                     | (true ,true ) ->
                                                         let uu____25461 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25461
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
                                           | uu____25504 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25556 =
                                   let uu____25558 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25558
                                     FStar_Util.is_some
                                    in
                                 if uu____25556
                                 then
                                   let uu____25607 =
                                     let uu____25613 =
                                       let uu____25615 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25617 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25619 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25621 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25615 uu____25617 uu____25619
                                         uu____25621
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25613)
                                      in
                                   FStar_Errors.raise_error uu____25607
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1835_25660 = env1.effects  in
             {
               decls = (uu___1835_25660.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1835_25660.polymonadic_binds);
               polymonadic_subcomps = (uu___1835_25660.polymonadic_subcomps)
             }  in
           let uu___1838_25661 = env1  in
           {
             solver = (uu___1838_25661.solver);
             range = (uu___1838_25661.range);
             curmodule = (uu___1838_25661.curmodule);
             gamma = (uu___1838_25661.gamma);
             gamma_sig = (uu___1838_25661.gamma_sig);
             gamma_cache = (uu___1838_25661.gamma_cache);
             modules = (uu___1838_25661.modules);
             expected_typ = (uu___1838_25661.expected_typ);
             sigtab = (uu___1838_25661.sigtab);
             attrtab = (uu___1838_25661.attrtab);
             instantiate_imp = (uu___1838_25661.instantiate_imp);
             effects = effects1;
             generalize = (uu___1838_25661.generalize);
             letrecs = (uu___1838_25661.letrecs);
             top_level = (uu___1838_25661.top_level);
             check_uvars = (uu___1838_25661.check_uvars);
             use_eq = (uu___1838_25661.use_eq);
             use_eq_strict = (uu___1838_25661.use_eq_strict);
             is_iface = (uu___1838_25661.is_iface);
             admit = (uu___1838_25661.admit);
             lax = (uu___1838_25661.lax);
             lax_universes = (uu___1838_25661.lax_universes);
             phase1 = (uu___1838_25661.phase1);
             failhard = (uu___1838_25661.failhard);
             nosynth = (uu___1838_25661.nosynth);
             uvar_subtyping = (uu___1838_25661.uvar_subtyping);
             tc_term = (uu___1838_25661.tc_term);
             type_of = (uu___1838_25661.type_of);
             universe_of = (uu___1838_25661.universe_of);
             check_type_of = (uu___1838_25661.check_type_of);
             use_bv_sorts = (uu___1838_25661.use_bv_sorts);
             qtbl_name_and_index = (uu___1838_25661.qtbl_name_and_index);
             normalized_eff_names = (uu___1838_25661.normalized_eff_names);
             fv_delta_depths = (uu___1838_25661.fv_delta_depths);
             proof_ns = (uu___1838_25661.proof_ns);
             synth_hook = (uu___1838_25661.synth_hook);
             try_solve_implicits_hook =
               (uu___1838_25661.try_solve_implicits_hook);
             splice = (uu___1838_25661.splice);
             mpreprocess = (uu___1838_25661.mpreprocess);
             postprocess = (uu___1838_25661.postprocess);
             identifier_info = (uu___1838_25661.identifier_info);
             tc_hooks = (uu___1838_25661.tc_hooks);
             dsenv = (uu___1838_25661.dsenv);
             nbe = (uu___1838_25661.nbe);
             strict_args_tab = (uu___1838_25661.strict_args_tab);
             erasable_types_tab = (uu___1838_25661.erasable_types_tab)
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
              let uu____25709 = FStar_Ident.string_of_lid m  in
              let uu____25711 = FStar_Ident.string_of_lid n  in
              let uu____25713 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25709 uu____25711 uu____25713
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25722 =
              let uu____25724 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25724 FStar_Util.is_some  in
            if uu____25722
            then
              let uu____25761 =
                let uu____25767 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25767)
                 in
              FStar_Errors.raise_error uu____25761 env1.range
            else
              (let uu____25773 =
                 (let uu____25777 = join_opt env1 m n  in
                  FStar_All.pipe_right uu____25777 FStar_Util.is_some) &&
                   (let uu____25802 = FStar_Ident.lid_equals m n  in
                    Prims.op_Negation uu____25802)
                  in
               if uu____25773
               then
                 let uu____25805 =
                   let uu____25811 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25811)
                    in
                 FStar_Errors.raise_error uu____25805 env1.range
               else
                 (let uu___1853_25817 = env1  in
                  {
                    solver = (uu___1853_25817.solver);
                    range = (uu___1853_25817.range);
                    curmodule = (uu___1853_25817.curmodule);
                    gamma = (uu___1853_25817.gamma);
                    gamma_sig = (uu___1853_25817.gamma_sig);
                    gamma_cache = (uu___1853_25817.gamma_cache);
                    modules = (uu___1853_25817.modules);
                    expected_typ = (uu___1853_25817.expected_typ);
                    sigtab = (uu___1853_25817.sigtab);
                    attrtab = (uu___1853_25817.attrtab);
                    instantiate_imp = (uu___1853_25817.instantiate_imp);
                    effects =
                      (let uu___1855_25819 = env1.effects  in
                       {
                         decls = (uu___1855_25819.decls);
                         order = (uu___1855_25819.order);
                         joins = (uu___1855_25819.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1855_25819.polymonadic_subcomps)
                       });
                    generalize = (uu___1853_25817.generalize);
                    letrecs = (uu___1853_25817.letrecs);
                    top_level = (uu___1853_25817.top_level);
                    check_uvars = (uu___1853_25817.check_uvars);
                    use_eq = (uu___1853_25817.use_eq);
                    use_eq_strict = (uu___1853_25817.use_eq_strict);
                    is_iface = (uu___1853_25817.is_iface);
                    admit = (uu___1853_25817.admit);
                    lax = (uu___1853_25817.lax);
                    lax_universes = (uu___1853_25817.lax_universes);
                    phase1 = (uu___1853_25817.phase1);
                    failhard = (uu___1853_25817.failhard);
                    nosynth = (uu___1853_25817.nosynth);
                    uvar_subtyping = (uu___1853_25817.uvar_subtyping);
                    tc_term = (uu___1853_25817.tc_term);
                    type_of = (uu___1853_25817.type_of);
                    universe_of = (uu___1853_25817.universe_of);
                    check_type_of = (uu___1853_25817.check_type_of);
                    use_bv_sorts = (uu___1853_25817.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1853_25817.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1853_25817.normalized_eff_names);
                    fv_delta_depths = (uu___1853_25817.fv_delta_depths);
                    proof_ns = (uu___1853_25817.proof_ns);
                    synth_hook = (uu___1853_25817.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1853_25817.try_solve_implicits_hook);
                    splice = (uu___1853_25817.splice);
                    mpreprocess = (uu___1853_25817.mpreprocess);
                    postprocess = (uu___1853_25817.postprocess);
                    identifier_info = (uu___1853_25817.identifier_info);
                    tc_hooks = (uu___1853_25817.tc_hooks);
                    dsenv = (uu___1853_25817.dsenv);
                    nbe = (uu___1853_25817.nbe);
                    strict_args_tab = (uu___1853_25817.strict_args_tab);
                    erasable_types_tab = (uu___1853_25817.erasable_types_tab)
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
            let uu____25910 = FStar_Ident.string_of_lid m  in
            let uu____25912 = FStar_Ident.string_of_lid n  in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu____25910 uu____25912
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice")
             in
          let uu____25921 =
            let uu____25923 = exists_polymonadic_subcomp env1 m n  in
            FStar_All.pipe_right uu____25923 FStar_Util.is_some  in
          if uu____25921
          then
            let uu____25930 =
              let uu____25936 = err_msg true  in
              (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25936)  in
            FStar_Errors.raise_error uu____25930 env1.range
          else
            (let uu____25942 =
               let uu____25944 = join_opt env1 m n  in
               FStar_All.pipe_right uu____25944 FStar_Util.is_some  in
             if uu____25942
             then
               let uu____25969 =
                 let uu____25975 = err_msg false  in
                 (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25975)
                  in
               FStar_Errors.raise_error uu____25969 env1.range
             else
               (let uu___1868_25981 = env1  in
                {
                  solver = (uu___1868_25981.solver);
                  range = (uu___1868_25981.range);
                  curmodule = (uu___1868_25981.curmodule);
                  gamma = (uu___1868_25981.gamma);
                  gamma_sig = (uu___1868_25981.gamma_sig);
                  gamma_cache = (uu___1868_25981.gamma_cache);
                  modules = (uu___1868_25981.modules);
                  expected_typ = (uu___1868_25981.expected_typ);
                  sigtab = (uu___1868_25981.sigtab);
                  attrtab = (uu___1868_25981.attrtab);
                  instantiate_imp = (uu___1868_25981.instantiate_imp);
                  effects =
                    (let uu___1870_25983 = env1.effects  in
                     {
                       decls = (uu___1870_25983.decls);
                       order = (uu___1870_25983.order);
                       joins = (uu___1870_25983.joins);
                       polymonadic_binds =
                         (uu___1870_25983.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___1868_25981.generalize);
                  letrecs = (uu___1868_25981.letrecs);
                  top_level = (uu___1868_25981.top_level);
                  check_uvars = (uu___1868_25981.check_uvars);
                  use_eq = (uu___1868_25981.use_eq);
                  use_eq_strict = (uu___1868_25981.use_eq_strict);
                  is_iface = (uu___1868_25981.is_iface);
                  admit = (uu___1868_25981.admit);
                  lax = (uu___1868_25981.lax);
                  lax_universes = (uu___1868_25981.lax_universes);
                  phase1 = (uu___1868_25981.phase1);
                  failhard = (uu___1868_25981.failhard);
                  nosynth = (uu___1868_25981.nosynth);
                  uvar_subtyping = (uu___1868_25981.uvar_subtyping);
                  tc_term = (uu___1868_25981.tc_term);
                  type_of = (uu___1868_25981.type_of);
                  universe_of = (uu___1868_25981.universe_of);
                  check_type_of = (uu___1868_25981.check_type_of);
                  use_bv_sorts = (uu___1868_25981.use_bv_sorts);
                  qtbl_name_and_index = (uu___1868_25981.qtbl_name_and_index);
                  normalized_eff_names =
                    (uu___1868_25981.normalized_eff_names);
                  fv_delta_depths = (uu___1868_25981.fv_delta_depths);
                  proof_ns = (uu___1868_25981.proof_ns);
                  synth_hook = (uu___1868_25981.synth_hook);
                  try_solve_implicits_hook =
                    (uu___1868_25981.try_solve_implicits_hook);
                  splice = (uu___1868_25981.splice);
                  mpreprocess = (uu___1868_25981.mpreprocess);
                  postprocess = (uu___1868_25981.postprocess);
                  identifier_info = (uu___1868_25981.identifier_info);
                  tc_hooks = (uu___1868_25981.tc_hooks);
                  dsenv = (uu___1868_25981.dsenv);
                  nbe = (uu___1868_25981.nbe);
                  strict_args_tab = (uu___1868_25981.strict_args_tab);
                  erasable_types_tab = (uu___1868_25981.erasable_types_tab)
                }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1874_26001 = env1  in
      {
        solver = (uu___1874_26001.solver);
        range = (uu___1874_26001.range);
        curmodule = (uu___1874_26001.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1874_26001.gamma_sig);
        gamma_cache = (uu___1874_26001.gamma_cache);
        modules = (uu___1874_26001.modules);
        expected_typ = (uu___1874_26001.expected_typ);
        sigtab = (uu___1874_26001.sigtab);
        attrtab = (uu___1874_26001.attrtab);
        instantiate_imp = (uu___1874_26001.instantiate_imp);
        effects = (uu___1874_26001.effects);
        generalize = (uu___1874_26001.generalize);
        letrecs = (uu___1874_26001.letrecs);
        top_level = (uu___1874_26001.top_level);
        check_uvars = (uu___1874_26001.check_uvars);
        use_eq = (uu___1874_26001.use_eq);
        use_eq_strict = (uu___1874_26001.use_eq_strict);
        is_iface = (uu___1874_26001.is_iface);
        admit = (uu___1874_26001.admit);
        lax = (uu___1874_26001.lax);
        lax_universes = (uu___1874_26001.lax_universes);
        phase1 = (uu___1874_26001.phase1);
        failhard = (uu___1874_26001.failhard);
        nosynth = (uu___1874_26001.nosynth);
        uvar_subtyping = (uu___1874_26001.uvar_subtyping);
        tc_term = (uu___1874_26001.tc_term);
        type_of = (uu___1874_26001.type_of);
        universe_of = (uu___1874_26001.universe_of);
        check_type_of = (uu___1874_26001.check_type_of);
        use_bv_sorts = (uu___1874_26001.use_bv_sorts);
        qtbl_name_and_index = (uu___1874_26001.qtbl_name_and_index);
        normalized_eff_names = (uu___1874_26001.normalized_eff_names);
        fv_delta_depths = (uu___1874_26001.fv_delta_depths);
        proof_ns = (uu___1874_26001.proof_ns);
        synth_hook = (uu___1874_26001.synth_hook);
        try_solve_implicits_hook = (uu___1874_26001.try_solve_implicits_hook);
        splice = (uu___1874_26001.splice);
        mpreprocess = (uu___1874_26001.mpreprocess);
        postprocess = (uu___1874_26001.postprocess);
        identifier_info = (uu___1874_26001.identifier_info);
        tc_hooks = (uu___1874_26001.tc_hooks);
        dsenv = (uu___1874_26001.dsenv);
        nbe = (uu___1874_26001.nbe);
        strict_args_tab = (uu___1874_26001.strict_args_tab);
        erasable_types_tab = (uu___1874_26001.erasable_types_tab)
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
            (let uu___1887_26059 = env1  in
             {
               solver = (uu___1887_26059.solver);
               range = (uu___1887_26059.range);
               curmodule = (uu___1887_26059.curmodule);
               gamma = rest;
               gamma_sig = (uu___1887_26059.gamma_sig);
               gamma_cache = (uu___1887_26059.gamma_cache);
               modules = (uu___1887_26059.modules);
               expected_typ = (uu___1887_26059.expected_typ);
               sigtab = (uu___1887_26059.sigtab);
               attrtab = (uu___1887_26059.attrtab);
               instantiate_imp = (uu___1887_26059.instantiate_imp);
               effects = (uu___1887_26059.effects);
               generalize = (uu___1887_26059.generalize);
               letrecs = (uu___1887_26059.letrecs);
               top_level = (uu___1887_26059.top_level);
               check_uvars = (uu___1887_26059.check_uvars);
               use_eq = (uu___1887_26059.use_eq);
               use_eq_strict = (uu___1887_26059.use_eq_strict);
               is_iface = (uu___1887_26059.is_iface);
               admit = (uu___1887_26059.admit);
               lax = (uu___1887_26059.lax);
               lax_universes = (uu___1887_26059.lax_universes);
               phase1 = (uu___1887_26059.phase1);
               failhard = (uu___1887_26059.failhard);
               nosynth = (uu___1887_26059.nosynth);
               uvar_subtyping = (uu___1887_26059.uvar_subtyping);
               tc_term = (uu___1887_26059.tc_term);
               type_of = (uu___1887_26059.type_of);
               universe_of = (uu___1887_26059.universe_of);
               check_type_of = (uu___1887_26059.check_type_of);
               use_bv_sorts = (uu___1887_26059.use_bv_sorts);
               qtbl_name_and_index = (uu___1887_26059.qtbl_name_and_index);
               normalized_eff_names = (uu___1887_26059.normalized_eff_names);
               fv_delta_depths = (uu___1887_26059.fv_delta_depths);
               proof_ns = (uu___1887_26059.proof_ns);
               synth_hook = (uu___1887_26059.synth_hook);
               try_solve_implicits_hook =
                 (uu___1887_26059.try_solve_implicits_hook);
               splice = (uu___1887_26059.splice);
               mpreprocess = (uu___1887_26059.mpreprocess);
               postprocess = (uu___1887_26059.postprocess);
               identifier_info = (uu___1887_26059.identifier_info);
               tc_hooks = (uu___1887_26059.tc_hooks);
               dsenv = (uu___1887_26059.dsenv);
               nbe = (uu___1887_26059.nbe);
               strict_args_tab = (uu___1887_26059.strict_args_tab);
               erasable_types_tab = (uu___1887_26059.erasable_types_tab)
             }))
    | uu____26060 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____26089  ->
             match uu____26089 with | (x,uu____26097) -> push_bv env2 x) env1
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
            let uu___1901_26132 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1901_26132.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1901_26132.FStar_Syntax_Syntax.index);
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
        let uu____26205 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26205 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____26233 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26233)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1922_26249 = env1  in
      {
        solver = (uu___1922_26249.solver);
        range = (uu___1922_26249.range);
        curmodule = (uu___1922_26249.curmodule);
        gamma = (uu___1922_26249.gamma);
        gamma_sig = (uu___1922_26249.gamma_sig);
        gamma_cache = (uu___1922_26249.gamma_cache);
        modules = (uu___1922_26249.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1922_26249.sigtab);
        attrtab = (uu___1922_26249.attrtab);
        instantiate_imp = (uu___1922_26249.instantiate_imp);
        effects = (uu___1922_26249.effects);
        generalize = (uu___1922_26249.generalize);
        letrecs = (uu___1922_26249.letrecs);
        top_level = (uu___1922_26249.top_level);
        check_uvars = (uu___1922_26249.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1922_26249.use_eq_strict);
        is_iface = (uu___1922_26249.is_iface);
        admit = (uu___1922_26249.admit);
        lax = (uu___1922_26249.lax);
        lax_universes = (uu___1922_26249.lax_universes);
        phase1 = (uu___1922_26249.phase1);
        failhard = (uu___1922_26249.failhard);
        nosynth = (uu___1922_26249.nosynth);
        uvar_subtyping = (uu___1922_26249.uvar_subtyping);
        tc_term = (uu___1922_26249.tc_term);
        type_of = (uu___1922_26249.type_of);
        universe_of = (uu___1922_26249.universe_of);
        check_type_of = (uu___1922_26249.check_type_of);
        use_bv_sorts = (uu___1922_26249.use_bv_sorts);
        qtbl_name_and_index = (uu___1922_26249.qtbl_name_and_index);
        normalized_eff_names = (uu___1922_26249.normalized_eff_names);
        fv_delta_depths = (uu___1922_26249.fv_delta_depths);
        proof_ns = (uu___1922_26249.proof_ns);
        synth_hook = (uu___1922_26249.synth_hook);
        try_solve_implicits_hook = (uu___1922_26249.try_solve_implicits_hook);
        splice = (uu___1922_26249.splice);
        mpreprocess = (uu___1922_26249.mpreprocess);
        postprocess = (uu___1922_26249.postprocess);
        identifier_info = (uu___1922_26249.identifier_info);
        tc_hooks = (uu___1922_26249.tc_hooks);
        dsenv = (uu___1922_26249.dsenv);
        nbe = (uu___1922_26249.nbe);
        strict_args_tab = (uu___1922_26249.strict_args_tab);
        erasable_types_tab = (uu___1922_26249.erasable_types_tab)
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
    let uu____26280 = expected_typ env_  in
    ((let uu___1929_26286 = env_  in
      {
        solver = (uu___1929_26286.solver);
        range = (uu___1929_26286.range);
        curmodule = (uu___1929_26286.curmodule);
        gamma = (uu___1929_26286.gamma);
        gamma_sig = (uu___1929_26286.gamma_sig);
        gamma_cache = (uu___1929_26286.gamma_cache);
        modules = (uu___1929_26286.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1929_26286.sigtab);
        attrtab = (uu___1929_26286.attrtab);
        instantiate_imp = (uu___1929_26286.instantiate_imp);
        effects = (uu___1929_26286.effects);
        generalize = (uu___1929_26286.generalize);
        letrecs = (uu___1929_26286.letrecs);
        top_level = (uu___1929_26286.top_level);
        check_uvars = (uu___1929_26286.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1929_26286.use_eq_strict);
        is_iface = (uu___1929_26286.is_iface);
        admit = (uu___1929_26286.admit);
        lax = (uu___1929_26286.lax);
        lax_universes = (uu___1929_26286.lax_universes);
        phase1 = (uu___1929_26286.phase1);
        failhard = (uu___1929_26286.failhard);
        nosynth = (uu___1929_26286.nosynth);
        uvar_subtyping = (uu___1929_26286.uvar_subtyping);
        tc_term = (uu___1929_26286.tc_term);
        type_of = (uu___1929_26286.type_of);
        universe_of = (uu___1929_26286.universe_of);
        check_type_of = (uu___1929_26286.check_type_of);
        use_bv_sorts = (uu___1929_26286.use_bv_sorts);
        qtbl_name_and_index = (uu___1929_26286.qtbl_name_and_index);
        normalized_eff_names = (uu___1929_26286.normalized_eff_names);
        fv_delta_depths = (uu___1929_26286.fv_delta_depths);
        proof_ns = (uu___1929_26286.proof_ns);
        synth_hook = (uu___1929_26286.synth_hook);
        try_solve_implicits_hook = (uu___1929_26286.try_solve_implicits_hook);
        splice = (uu___1929_26286.splice);
        mpreprocess = (uu___1929_26286.mpreprocess);
        postprocess = (uu___1929_26286.postprocess);
        identifier_info = (uu___1929_26286.identifier_info);
        tc_hooks = (uu___1929_26286.tc_hooks);
        dsenv = (uu___1929_26286.dsenv);
        nbe = (uu___1929_26286.nbe);
        strict_args_tab = (uu___1929_26286.strict_args_tab);
        erasable_types_tab = (uu___1929_26286.erasable_types_tab)
      }), uu____26280)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26298 =
      let uu____26299 = FStar_Ident.id_of_text ""  in [uu____26299]  in
    FStar_Ident.lid_of_ids uu____26298  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____26306 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26306
        then
          let uu____26311 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26311 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1937_26339 = env1  in
       {
         solver = (uu___1937_26339.solver);
         range = (uu___1937_26339.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1937_26339.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1937_26339.expected_typ);
         sigtab = (uu___1937_26339.sigtab);
         attrtab = (uu___1937_26339.attrtab);
         instantiate_imp = (uu___1937_26339.instantiate_imp);
         effects = (uu___1937_26339.effects);
         generalize = (uu___1937_26339.generalize);
         letrecs = (uu___1937_26339.letrecs);
         top_level = (uu___1937_26339.top_level);
         check_uvars = (uu___1937_26339.check_uvars);
         use_eq = (uu___1937_26339.use_eq);
         use_eq_strict = (uu___1937_26339.use_eq_strict);
         is_iface = (uu___1937_26339.is_iface);
         admit = (uu___1937_26339.admit);
         lax = (uu___1937_26339.lax);
         lax_universes = (uu___1937_26339.lax_universes);
         phase1 = (uu___1937_26339.phase1);
         failhard = (uu___1937_26339.failhard);
         nosynth = (uu___1937_26339.nosynth);
         uvar_subtyping = (uu___1937_26339.uvar_subtyping);
         tc_term = (uu___1937_26339.tc_term);
         type_of = (uu___1937_26339.type_of);
         universe_of = (uu___1937_26339.universe_of);
         check_type_of = (uu___1937_26339.check_type_of);
         use_bv_sorts = (uu___1937_26339.use_bv_sorts);
         qtbl_name_and_index = (uu___1937_26339.qtbl_name_and_index);
         normalized_eff_names = (uu___1937_26339.normalized_eff_names);
         fv_delta_depths = (uu___1937_26339.fv_delta_depths);
         proof_ns = (uu___1937_26339.proof_ns);
         synth_hook = (uu___1937_26339.synth_hook);
         try_solve_implicits_hook =
           (uu___1937_26339.try_solve_implicits_hook);
         splice = (uu___1937_26339.splice);
         mpreprocess = (uu___1937_26339.mpreprocess);
         postprocess = (uu___1937_26339.postprocess);
         identifier_info = (uu___1937_26339.identifier_info);
         tc_hooks = (uu___1937_26339.tc_hooks);
         dsenv = (uu___1937_26339.dsenv);
         nbe = (uu___1937_26339.nbe);
         strict_args_tab = (uu___1937_26339.strict_args_tab);
         erasable_types_tab = (uu___1937_26339.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26391)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26395,(uu____26396,t)))::tl
          ->
          let uu____26417 =
            let uu____26420 = FStar_Syntax_Free.uvars t  in
            ext out uu____26420  in
          aux uu____26417 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26423;
            FStar_Syntax_Syntax.index = uu____26424;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26432 =
            let uu____26435 = FStar_Syntax_Free.uvars t  in
            ext out uu____26435  in
          aux uu____26432 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26493)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26497,(uu____26498,t)))::tl
          ->
          let uu____26519 =
            let uu____26522 = FStar_Syntax_Free.univs t  in
            ext out uu____26522  in
          aux uu____26519 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26525;
            FStar_Syntax_Syntax.index = uu____26526;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26534 =
            let uu____26537 = FStar_Syntax_Free.univs t  in
            ext out uu____26537  in
          aux uu____26534 tl
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
          let uu____26599 = FStar_Util.set_add uname out  in
          aux uu____26599 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26602,(uu____26603,t)))::tl
          ->
          let uu____26624 =
            let uu____26627 = FStar_Syntax_Free.univnames t  in
            ext out uu____26627  in
          aux uu____26624 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26630;
            FStar_Syntax_Syntax.index = uu____26631;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26639 =
            let uu____26642 = FStar_Syntax_Free.univnames t  in
            ext out uu____26642  in
          aux uu____26639 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26663  ->
            match uu___12_26663 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26667 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26680 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26691 =
      let uu____26700 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26700
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26691 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26748 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26761  ->
              match uu___13_26761 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26764 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26764
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26768 = FStar_Ident.string_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26768
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26772) ->
                  let uu____26789 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26789))
       in
    FStar_All.pipe_right uu____26748 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26803  ->
    match uu___14_26803 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26809 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26809
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26832  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26887) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26920,uu____26921) -> false  in
      let uu____26935 =
        FStar_List.tryFind
          (fun uu____26957  ->
             match uu____26957 with | (p,uu____26968) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26935 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26987,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____27017 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____27017
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2080_27039 = e  in
        {
          solver = (uu___2080_27039.solver);
          range = (uu___2080_27039.range);
          curmodule = (uu___2080_27039.curmodule);
          gamma = (uu___2080_27039.gamma);
          gamma_sig = (uu___2080_27039.gamma_sig);
          gamma_cache = (uu___2080_27039.gamma_cache);
          modules = (uu___2080_27039.modules);
          expected_typ = (uu___2080_27039.expected_typ);
          sigtab = (uu___2080_27039.sigtab);
          attrtab = (uu___2080_27039.attrtab);
          instantiate_imp = (uu___2080_27039.instantiate_imp);
          effects = (uu___2080_27039.effects);
          generalize = (uu___2080_27039.generalize);
          letrecs = (uu___2080_27039.letrecs);
          top_level = (uu___2080_27039.top_level);
          check_uvars = (uu___2080_27039.check_uvars);
          use_eq = (uu___2080_27039.use_eq);
          use_eq_strict = (uu___2080_27039.use_eq_strict);
          is_iface = (uu___2080_27039.is_iface);
          admit = (uu___2080_27039.admit);
          lax = (uu___2080_27039.lax);
          lax_universes = (uu___2080_27039.lax_universes);
          phase1 = (uu___2080_27039.phase1);
          failhard = (uu___2080_27039.failhard);
          nosynth = (uu___2080_27039.nosynth);
          uvar_subtyping = (uu___2080_27039.uvar_subtyping);
          tc_term = (uu___2080_27039.tc_term);
          type_of = (uu___2080_27039.type_of);
          universe_of = (uu___2080_27039.universe_of);
          check_type_of = (uu___2080_27039.check_type_of);
          use_bv_sorts = (uu___2080_27039.use_bv_sorts);
          qtbl_name_and_index = (uu___2080_27039.qtbl_name_and_index);
          normalized_eff_names = (uu___2080_27039.normalized_eff_names);
          fv_delta_depths = (uu___2080_27039.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2080_27039.synth_hook);
          try_solve_implicits_hook =
            (uu___2080_27039.try_solve_implicits_hook);
          splice = (uu___2080_27039.splice);
          mpreprocess = (uu___2080_27039.mpreprocess);
          postprocess = (uu___2080_27039.postprocess);
          identifier_info = (uu___2080_27039.identifier_info);
          tc_hooks = (uu___2080_27039.tc_hooks);
          dsenv = (uu___2080_27039.dsenv);
          nbe = (uu___2080_27039.nbe);
          strict_args_tab = (uu___2080_27039.strict_args_tab);
          erasable_types_tab = (uu___2080_27039.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2089_27087 = e  in
      {
        solver = (uu___2089_27087.solver);
        range = (uu___2089_27087.range);
        curmodule = (uu___2089_27087.curmodule);
        gamma = (uu___2089_27087.gamma);
        gamma_sig = (uu___2089_27087.gamma_sig);
        gamma_cache = (uu___2089_27087.gamma_cache);
        modules = (uu___2089_27087.modules);
        expected_typ = (uu___2089_27087.expected_typ);
        sigtab = (uu___2089_27087.sigtab);
        attrtab = (uu___2089_27087.attrtab);
        instantiate_imp = (uu___2089_27087.instantiate_imp);
        effects = (uu___2089_27087.effects);
        generalize = (uu___2089_27087.generalize);
        letrecs = (uu___2089_27087.letrecs);
        top_level = (uu___2089_27087.top_level);
        check_uvars = (uu___2089_27087.check_uvars);
        use_eq = (uu___2089_27087.use_eq);
        use_eq_strict = (uu___2089_27087.use_eq_strict);
        is_iface = (uu___2089_27087.is_iface);
        admit = (uu___2089_27087.admit);
        lax = (uu___2089_27087.lax);
        lax_universes = (uu___2089_27087.lax_universes);
        phase1 = (uu___2089_27087.phase1);
        failhard = (uu___2089_27087.failhard);
        nosynth = (uu___2089_27087.nosynth);
        uvar_subtyping = (uu___2089_27087.uvar_subtyping);
        tc_term = (uu___2089_27087.tc_term);
        type_of = (uu___2089_27087.type_of);
        universe_of = (uu___2089_27087.universe_of);
        check_type_of = (uu___2089_27087.check_type_of);
        use_bv_sorts = (uu___2089_27087.use_bv_sorts);
        qtbl_name_and_index = (uu___2089_27087.qtbl_name_and_index);
        normalized_eff_names = (uu___2089_27087.normalized_eff_names);
        fv_delta_depths = (uu___2089_27087.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2089_27087.synth_hook);
        try_solve_implicits_hook = (uu___2089_27087.try_solve_implicits_hook);
        splice = (uu___2089_27087.splice);
        mpreprocess = (uu___2089_27087.mpreprocess);
        postprocess = (uu___2089_27087.postprocess);
        identifier_info = (uu___2089_27087.identifier_info);
        tc_hooks = (uu___2089_27087.tc_hooks);
        dsenv = (uu___2089_27087.dsenv);
        nbe = (uu___2089_27087.nbe);
        strict_args_tab = (uu___2089_27087.strict_args_tab);
        erasable_types_tab = (uu___2089_27087.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____27103 = FStar_Syntax_Free.names t  in
      let uu____27106 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____27103 uu____27106
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27129 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27129
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27139 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27139
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____27160 =
      match uu____27160 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27180 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27180)
       in
    let uu____27188 =
      let uu____27192 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____27192 FStar_List.rev  in
    FStar_All.pipe_right uu____27188 (FStar_String.concat " ")
  
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
                  (let uu____27260 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27260 with
                   | FStar_Pervasives_Native.Some uu____27264 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27267 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27277;
        FStar_TypeChecker_Common.univ_ineqs = uu____27278;
        FStar_TypeChecker_Common.implicits = uu____27279;_} -> true
    | uu____27289 -> false
  
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
          let uu___2133_27311 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2133_27311.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2133_27311.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2133_27311.FStar_TypeChecker_Common.implicits)
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
          let uu____27350 = FStar_Options.defensive ()  in
          if uu____27350
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27356 =
              let uu____27358 =
                let uu____27360 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27360  in
              Prims.op_Negation uu____27358  in
            (if uu____27356
             then
               let uu____27367 =
                 let uu____27373 =
                   let uu____27375 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27377 =
                     let uu____27379 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27379
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27375 uu____27377
                    in
                 (FStar_Errors.Warning_Defensive, uu____27373)  in
               FStar_Errors.log_issue rng uu____27367
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
          let uu____27419 =
            let uu____27421 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27421  in
          if uu____27419
          then ()
          else
            (let uu____27426 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27426 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27452 =
            let uu____27454 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27454  in
          if uu____27452
          then ()
          else
            (let uu____27459 = bound_vars e  in
             def_check_closed_in rng msg uu____27459 t)
  
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
          let uu___2170_27498 = g  in
          let uu____27499 =
            let uu____27500 =
              let uu____27501 =
                let uu____27502 =
                  let uu____27519 =
                    let uu____27530 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____27530]  in
                  (f, uu____27519)  in
                FStar_Syntax_Syntax.Tm_app uu____27502  in
              FStar_Syntax_Syntax.mk uu____27501 f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27567  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27567) uu____27500
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27499;
            FStar_TypeChecker_Common.deferred =
              (uu___2170_27498.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2170_27498.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2170_27498.FStar_TypeChecker_Common.implicits)
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
          let uu___2177_27585 = g  in
          let uu____27586 =
            let uu____27587 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27587  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27586;
            FStar_TypeChecker_Common.deferred =
              (uu___2177_27585.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2177_27585.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2177_27585.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2182_27604 = g  in
          let uu____27605 =
            let uu____27606 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27606  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27605;
            FStar_TypeChecker_Common.deferred =
              (uu___2182_27604.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2182_27604.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2182_27604.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2186_27608 = g  in
          let uu____27609 =
            let uu____27610 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27610  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27609;
            FStar_TypeChecker_Common.deferred =
              (uu___2186_27608.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2186_27608.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2186_27608.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27617 ->
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
                       let uu____27694 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27694
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2209_27701 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2209_27701.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2209_27701.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2209_27701.FStar_TypeChecker_Common.implicits)
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
               let uu____27735 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27735
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
            let uu___2224_27762 = g  in
            let uu____27763 =
              let uu____27764 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27764  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27763;
              FStar_TypeChecker_Common.deferred =
                (uu___2224_27762.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2224_27762.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2224_27762.FStar_TypeChecker_Common.implicits)
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
      fun env1  ->
        fun k  ->
          fun should_check  ->
            fun meta  ->
              let uu____27822 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27822 with
              | FStar_Pervasives_Native.Some
                  (uu____27847::(tm,uu____27849)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27913 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27931 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27931;
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
                    (let uu____27965 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27965
                     then
                       let uu____27969 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27969
                     else ());
                    (let g =
                       let uu___2248_27975 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2248_27975.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2248_27975.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2248_27975.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____28029 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____28087  ->
                      fun b  ->
                        match uu____28087 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____28129 =
                              new_implicit_var_aux "" r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____28129 with
                             | (t,l_ctx_uvars,g_t) ->
                                 ((let uu____28173 =
                                     FStar_All.pipe_left (debug env1)
                                       (FStar_Options.Other
                                          "LayeredEffectsEqns")
                                      in
                                   if uu____28173
                                   then
                                     FStar_List.iter
                                       (fun uu____28186  ->
                                          match uu____28186 with
                                          | (ctx_uvar,uu____28192) ->
                                              let uu____28193 =
                                                FStar_Syntax_Print.ctx_uvar_to_string_no_reason
                                                  ctx_uvar
                                                 in
                                              FStar_Util.print1
                                                "Layered Effect uvar : %s\n"
                                                uu____28193) l_ctx_uvars
                                   else ());
                                  (let uu____28198 =
                                     let uu____28201 =
                                       let uu____28204 =
                                         let uu____28205 =
                                           let uu____28212 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____28212, t)  in
                                         FStar_Syntax_Syntax.NT uu____28205
                                          in
                                       [uu____28204]  in
                                     FStar_List.append substs1 uu____28201
                                      in
                                   let uu____28223 = conj_guard g g_t  in
                                   (uu____28198,
                                     (FStar_List.append uvars [t]),
                                     uu____28223)))))
                   (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____28029
              (fun uu____28252  ->
                 match uu____28252 with | (uu____28269,uvars,g) -> (uvars, g))
  
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
                let uu____28310 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28310 FStar_Util.must  in
              let uu____28327 = inst_tscheme_with post_ts [u]  in
              match uu____28327 with
              | (uu____28332,post) ->
                  let uu____28334 =
                    let uu____28335 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                    [uu____28335]  in
                  FStar_Syntax_Syntax.mk_Tm_app post uu____28334 r
               in
            let uu____28368 =
              let uu____28369 =
                FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg
                 in
              [uu____28369]  in
            FStar_Syntax_Syntax.mk_Tm_app wp uu____28368 r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28405  -> ());
    push = (fun uu____28407  -> ());
    pop = (fun uu____28410  -> ());
    snapshot =
      (fun uu____28413  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28432  -> fun uu____28433  -> ());
    encode_sig = (fun uu____28448  -> fun uu____28449  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28455 =
             let uu____28462 = FStar_Options.peek ()  in (e, g, uu____28462)
              in
           [uu____28455]);
    solve = (fun uu____28478  -> fun uu____28479  -> fun uu____28480  -> ());
    finish = (fun uu____28487  -> ());
    refresh = (fun uu____28489  -> ())
  } 